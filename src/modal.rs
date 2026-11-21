// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

//! Sound formula-level modal truth proofs. Failure to prove an obligation is
//! inconclusive: execution.rs then runs exact symbolic reachability. Proof
//! contexts contain only established facts, never assumed action preconditions
//! or conditional-effect guards.
use crate::{
    boolean::{Formula, TRUE},
    encoding::Encoding,
    hierarchy::Certificate,
    model::{Atom, Condition},
    order::Order,
    report::Result,
    work::Work,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Point {
    Start,
    Before(usize),
    Finish,
}

pub(crate) struct Analyzer {
    encoding: Encoding,
    initial: Vec<bool>,
    transitions: Vec<BTreeMap<usize, Formula>>,
    required: Vec<(usize, Formula)>,
    auxiliary: Vec<(usize, Formula)>,
    guards: Vec<Formula>,
    regressions: BTreeMap<(Formula, usize), Formula>,
    supports: BTreeMap<Formula, BTreeSet<usize>>,
}

impl Analyzer {
    pub fn new(
        c: &Certificate,
        initial: &BTreeSet<Atom>,
        goal: &Condition,
        work: &mut Work,
    ) -> Result<Self> {
        let n = c.actions.len();
        let mut this = Self {
            encoding: Encoding::new(1),
            initial: vec![],
            transitions: vec![],
            required: vec![],
            auxiliary: vec![],
            guards: vec![],
            regressions: BTreeMap::new(),
            supports: BTreeMap::new(),
        };
        for (consumer, condition) in c
            .actions
            .iter()
            .map(|a| &a.condition)
            .chain(std::iter::once(goal))
            .enumerate()
        {
            // Conjunction distributes through necessary truth; disjunction
            // does not. Keep each disjunctive clause as one correlated formula.
            let mut pending = vec![condition];
            while let Some(condition) = pending.pop() {
                work.tick();
                if let Condition::And(parts) = condition {
                    work.charge(parts.len() as u64);
                    pending.extend(parts);
                } else {
                    let formula = this.encoding.compile(condition, work)?;
                    work.charge(2);
                    this.required.push((consumer, formula));
                }
            }
        }
        for action in &c.actions {
            let index = this.transitions.len();
            for effect in &action.conditional {
                let guard = this.encoding.compile(&effect.condition, work)?;
                let negative = this.encoding.booleans.not(guard, work)?;
                work.charge(4);
                this.auxiliary.extend([(index, guard), (index, negative)]);
            }
            let transition = this.encoding.effects(action, work)?;
            this.transitions.push(transition);
        }
        for event in &c.events[n..] {
            let formula = this.encoding.compile(&event.condition, work)?;
            work.tick();
            this.guards.push(formula);
        }
        work.charge(this.encoding.atoms.len() as u64);
        this.initial = vec![false; this.encoding.atoms.len()];
        for (atom, &variable) in &this.encoding.atoms {
            work.tick();
            this.initial[variable] = initial.contains(atom);
        }
        Ok(this)
    }

    fn support(&mut self, formula: Formula, work: &mut Work) -> Result<&BTreeSet<usize>> {
        if !self.supports.contains_key(&formula) {
            let support = self.encoding.booleans.support(formula, work)?;
            work.tick();
            self.supports.insert(formula, support);
        }
        Ok(&self.supports[&formula])
    }

    fn regress(&mut self, formula: Formula, action: usize, work: &mut Work) -> Result<Formula> {
        work.tick();
        if let Some(&result) = self.regressions.get(&(formula, action)) {
            return Ok(result);
        }
        self.support(formula, work)?;
        let mut changed = false;
        for variable in &self.supports[&formula] {
            work.tick();
            changed |= self.transitions[action].contains_key(variable);
        }
        let result = if changed {
            self.encoding
                .booleans
                .substitute(formula, &self.transitions[action], work)?
        } else {
            formula
        };
        work.charge(3);
        self.regressions.insert((formula, action), result);
        Ok(result)
    }

    /// A sufficient proof only: false delegates to the exact symbolic backend.
    pub fn prove(&mut self, c: &Certificate, order: &Order, work: &mut Work) -> Result<bool> {
        let n = c.actions.len();
        let mut queries: BTreeMap<Formula, BTreeSet<usize>> = BTreeMap::new();
        for &(consumer, formula) in self.required.iter().chain(&self.auxiliary) {
            work.charge(2);
            queries.entry(formula).or_default().insert(consumer);
        }
        let mut placements = vec![];
        for (guard, &formula) in self.guards.iter().enumerate() {
            let event = n + guard;
            let mut points = vec![];
            for point in std::iter::once(Point::Start)
                .chain(order.topological.iter().copied().map(Point::Before))
                .chain(std::iter::once(Point::Finish))
            {
                if eligible(c, order, event, point, work)? {
                    work.tick();
                    points.push(point);
                    let consumer = match point {
                        Point::Start => continue,
                        Point::Before(i) => i,
                        Point::Finish => n,
                    };
                    if formula != TRUE {
                        work.charge(2);
                        queries.entry(formula).or_default().insert(consumer);
                    }
                }
            }
            work.tick();
            placements.push(points);
        }
        work.charge((n + 1) as u64);
        let mut contexts = vec![TRUE; n + 1];
        let mut proved = BTreeSet::new();
        loop {
            let mut progress = false;
            for (&formula, consumers) in &queries {
                let initial = self.encoding.booleans.holds(formula, &self.initial, work)?;
                work.charge(2 * n as u64);
                let mut produces = vec![false; n];
                let mut preserves = vec![false; n];
                for a in 0..n {
                    let regression = self.regress(formula, a, work)?;
                    produces[a] = self
                        .encoding
                        .booleans
                        .entails(contexts[a], regression, work)?;
                    let assumption = self.encoding.booleans.and(contexts[a], formula, work)?;
                    preserves[a] = self
                        .encoding
                        .booleans
                        .entails(assumption, regression, work)?;
                }
                for &consumer in consumers {
                    work.tick();
                    if proved.contains(&(consumer, formula)) {
                        continue;
                    }
                    let before = |a, b| b == n || order.before(a, b);
                    let mut producers = vec![];
                    for (a, &produces) in produces.iter().enumerate() {
                        work.tick();
                        if produces && before(a, consumer) {
                            work.tick();
                            producers.push(a);
                        }
                    }
                    if !initial && producers.is_empty() {
                        continue;
                    }
                    let mut safe = true;
                    for (d, &preserves) in preserves.iter().enumerate() {
                        work.tick();
                        if preserves || d == consumer || (consumer < n && before(consumer, d)) {
                            continue;
                        }
                        let mut restored = false;
                        for &r in &producers {
                            work.tick();
                            if before(d, r) {
                                restored = true;
                                break;
                            }
                        }
                        if !restored {
                            safe = false;
                            break;
                        }
                    }
                    if safe {
                        work.charge(2);
                        proved.insert((consumer, formula));
                        contexts[consumer] =
                            self.encoding
                                .booleans
                                .and(contexts[consumer], formula, work)?;
                        progress = true;
                    }
                }
            }
            if !progress {
                break;
            }
        }
        for &(consumer, formula) in &self.required {
            work.tick();
            if !proved.contains(&(consumer, formula)) {
                return Ok(false);
            }
        }
        // Each chosen point is legal in every linearization. Events at the
        // same point are inserted in hierarchy order and have no effects.
        work.charge(self.guards.len() as u64);
        let mut chosen = vec![None; self.guards.len()];
        for &event in &c.hierarchy.topological {
            if event < n {
                continue;
            }
            let formula = self.guards[event - n];
            for &point in &placements[event - n] {
                work.tick();
                let true_here = match point {
                    Point::Start => self.encoding.booleans.holds(formula, &self.initial, work)?,
                    Point::Before(i) => formula == TRUE || proved.contains(&(i, formula)),
                    Point::Finish => formula == TRUE || proved.contains(&(n, formula)),
                };
                if !true_here {
                    continue;
                }
                let mut legal = true;
                for &parent in &c.hierarchy.predecessors[event] {
                    work.tick();
                    if parent >= n
                        && !chosen[parent - n].is_some_and(|p| point_before(order, p, point))
                    {
                        legal = false;
                        break;
                    }
                }
                if legal {
                    chosen[event - n] = Some(point);
                    break;
                }
            }
            if chosen[event - n].is_none() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn point_before(order: &Order, a: Point, b: Point) -> bool {
    match (a, b) {
        (Point::Start, _) | (_, Point::Finish) => true,
        (Point::Before(a), Point::Before(b)) => a == b || order.before(a, b),
        _ => false,
    }
}

fn eligible(
    c: &Certificate,
    order: &Order,
    event: usize,
    point: Point,
    work: &mut Work,
) -> Result<bool> {
    for action in 0..c.actions.len() {
        work.tick();
        if c.hierarchy.before(action, event)
            && !match point {
                Point::Start => false,
                Point::Before(next) => order.before(action, next),
                Point::Finish => true,
            }
        {
            return Ok(false);
        }
        if c.hierarchy.before(event, action)
            && !match point {
                Point::Start => true,
                Point::Before(next) => next == action || order.before(next, action),
                Point::Finish => false,
            }
        {
            return Ok(false);
        }
    }
    Ok(true)
}
