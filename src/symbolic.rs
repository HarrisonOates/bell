//! Exact universal partial-order validation by layered BDD reachability.
//!
//! A state contains dynamic facts, action completion bits, and method-check bits.
//! Unconditional hierarchy events are contracted away, preserving dependencies.
//! Method preconditions become internal, effect-free check actions, saturated
//! in topological order at each primitive boundary. Completing a check can only
//! enable other events, so this succeeds iff some legal placement succeeds.
//! Only the submitted primitive order controls the nondeterministic scheduler:
//! an order-enabled action with a false condition is a failure, never a pruned
//! scheduler choice. Each successful transition completes one new occurrence;
//! n layers therefore decide every linearization without an arbitrary bound.
use crate::{
    boolean::{Booleans, FALSE, Formula, TRUE},
    encoding::Encoding,
    execution::replay_sequence,
    hierarchy::Certificate,
    model::{Atom, Condition},
    report::{Diagnostic, Result, Status},
    work::Work,
};
use std::collections::{BTreeMap, BTreeSet};

struct Partition {
    relation: Formula,
    abstract_after: BTreeSet<usize>,
}

struct Transition {
    enabled: Formula,
    bad: Formula,
    updates: BTreeMap<usize, Formula>,
    partitions: Vec<Partition>,
    abstract_before: BTreeSet<usize>,
}

impl Transition {
    fn new(
        b: &mut Booleans,
        enabled: Formula,
        bad: Formula,
        updates: BTreeMap<usize, Formula>,
        work: &mut Work,
    ) -> Result<Self> {
        let changed: BTreeSet<_> = updates.keys().copied().collect();
        let mut last_use = BTreeMap::new();
        let mut partitions = vec![];
        for (i, (&variable, &value)) in updates.iter().enumerate() {
            for dependency in b.support(value, work)? {
                if changed.contains(&dependency) {
                    last_use.insert(dependency, i);
                }
            }
            let next = b.variable(variable + 1, work)?;
            partitions.push(Partition {
                relation: b.equivalent(next, value, work)?,
                abstract_after: BTreeSet::new(),
            });
        }
        let mut abstract_before = changed;
        for (variable, i) in last_use {
            abstract_before.remove(&variable);
            partitions[i].abstract_after.insert(variable);
        }
        Ok(Self {
            enabled,
            bad,
            updates,
            partitions,
            abstract_before,
        })
    }

    fn image(&self, b: &mut Booleans, states: Formula, work: &mut Work) -> Result<Formula> {
        let source = b.and(states, self.enabled, work)?;
        let mut result = b.exists(source, &self.abstract_before, work)?;
        if result == FALSE {
            return Ok(FALSE);
        }
        for partition in &self.partitions {
            result = b.and_exists(result, partition.relation, &partition.abstract_after, work)?;
        }
        // Unchanged variables retain their current name and need no explicit
        // frame equations. Only written variables use temporary odd IDs.
        let mut rename = BTreeMap::new();
        for &variable in self.updates.keys() {
            rename.insert(variable + 1, b.variable(variable, work)?);
        }
        b.substitute(result, &rename, work)
    }

    fn roots(&self, roots: &mut Vec<Formula>) {
        roots.extend([self.enabled, self.bad]);
        roots.extend(self.updates.values().copied());
        roots.extend(self.partitions.iter().map(|p| p.relation));
    }
}

struct System {
    booleans: Booleans,
    variables: usize,
    initial: Formula,
    final_failure: Formula,
    transitions: Vec<Transition>,
    checks: Vec<Transition>,
}

impl System {
    fn new(
        initial: &BTreeSet<Atom>,
        c: &Certificate,
        goal: &Condition,
        work: &mut Work,
    ) -> Result<Self> {
        let n = c.actions.len();
        let mut written = BTreeSet::new();
        for action in &c.actions {
            for atom in action.add.iter().chain(&action.delete).chain(
                action
                    .conditional
                    .iter()
                    .flat_map(|e| e.add.iter().chain(&e.delete)),
            ) {
                work.tick();
                written.insert(atom.clone());
            }
        }
        let mut encoding = Encoding::with_static_facts(2, initial.clone(), written);
        let mut conditions = vec![];
        for event in &c.events {
            conditions.push(encoding.compile(&event.condition, work)?);
        }
        let goal = encoding.compile(goal, work)?;
        let mut effects = vec![];
        for action in &c.actions {
            effects.push(encoding.effects(action, work)?);
        }
        // Only real actions and nontrivial method checks need completion bits.
        // Project paths through all other hierarchy events onto these retained
        // endpoints. In particular an empty method still connects its neighbors.
        let retained: Vec<_> = (0..n)
            .chain(
                c.hierarchy
                    .topological
                    .iter()
                    .copied()
                    .filter(|&e| e >= n && conditions[e] != TRUE),
            )
            .collect();
        let mut index = vec![None; c.events.len()];
        for (i, &event) in retained.iter().enumerate() {
            index[event] = Some(i);
        }
        let mut boundary = vec![BTreeSet::new(); c.events.len()];
        let mut predecessors = vec![BTreeSet::new(); retained.len()];
        for &event in &c.hierarchy.topological {
            let mut incoming = BTreeSet::new();
            for &parent in &c.hierarchy.predecessors[event] {
                work.charge(boundary[parent].len() as u64);
                incoming.extend(&boundary[parent]);
            }
            if let Some(i) = index[event] {
                predecessors[i] = incoming;
                boundary[event].insert(i);
            } else {
                boundary[event] = incoming;
            }
        }

        // No further atoms are introduced after assigning the completion bits.
        let facts = encoding.atoms.len();
        let event_variable = |event| 2 * (facts + event);
        let variables = 2 * (facts + retained.len());
        let b = &mut encoding.booleans;
        let mut done = vec![];
        for event in 0..retained.len() {
            done.push(b.variable(event_variable(event), work)?);
        }

        // Keep check actions separate: composing the entire hierarchy into each
        // primitive update expands formulas over unreachable histories. These
        // local updates are applied to REACHABLE sets, in topological order.
        let mut checks = vec![];
        for (i, &event) in retained.iter().enumerate().skip(n) {
            let mut enabled = conditions[event];
            for &parent in &predecessors[i] {
                enabled = b.and(enabled, done[parent], work)?;
            }
            let complete = b.or(done[i], enabled, work)?;
            checks.push(Transition::new(
                b,
                TRUE,
                FALSE,
                BTreeMap::from([(event_variable(i), complete)]),
                work,
            )?);
        }
        let mut state = vec![false; variables];
        for (atom, &variable) in &encoding.atoms {
            state[variable] = initial.contains(atom);
        }
        let mut initial = b.cube(&values(&state), work)?;
        for check in &checks {
            initial = check.image(b, initial, work)?;
        }

        let mut transitions = vec![];
        for (action, mut updates) in effects.into_iter().enumerate() {
            let mut permitted = b.not(done[action], work)?;
            for &parent in &c.order.predecessors[action] {
                permitted = b.and(permitted, done[parent], work)?;
            }
            let mut executable = conditions[action];
            for &parent in &predecessors[action] {
                executable = b.and(executable, done[parent], work)?;
            }
            let fails = b.not(executable, work)?;
            let failure = b.and(permitted, fails, work)?;
            let enabled = b.and(permitted, executable, work)?;
            updates.insert(event_variable(action), TRUE);
            transitions.push(Transition::new(b, enabled, failure, updates, work)?);
        }
        let mut success = goal;
        for &complete in &done[n..] {
            success = b.and(success, complete, work)?;
        }
        let final_failure = b.not(success, work)?;
        Ok(Self {
            booleans: encoding.booleans,
            variables,
            initial,
            final_failure,
            transitions,
            checks,
        })
    }

    fn saturate(&mut self, mut states: Formula, work: &mut Work) -> Result<Formula> {
        for check in &self.checks {
            states = check.image(&mut self.booleans, states, work)?;
        }
        Ok(states)
    }

    fn collect(&mut self, layers: &[Formula], work: &mut Work) {
        let mut roots = vec![self.initial, self.final_failure];
        roots.extend_from_slice(layers);
        for transition in self.transitions.iter().chain(&self.checks) {
            transition.roots(&mut roots);
        }
        self.booleans.collect(roots, work);
    }

    fn counterexample(
        &mut self,
        bad_states: Formula,
        layers: &[Formula],
        initial: &BTreeSet<Atom>,
        c: &Certificate,
        goal: &Condition,
        work: &mut Work,
    ) -> Diagnostic {
        match self.trace(bad_states, layers, c, work) {
            Err(error) => error,
            Ok(sequence) => match replay_sequence(initial, c, &sequence, goal, work) {
                Err(error) => error,
                Ok(()) => internal("symbolic counterexample passed concrete replay"),
            },
        }
    }

    fn trace(
        &mut self,
        bad_states: Formula,
        layers: &[Formula],
        c: &Certificate,
        work: &mut Work,
    ) -> Result<Vec<usize>> {
        let b = &mut self.booleans;
        let mut state = b
            .witness(bad_states, self.variables, work)
            .ok_or_else(|| internal("empty symbolic counterexample"))?;
        let mut failed_action = None;
        for (a, transition) in self.transitions.iter().enumerate() {
            if b.holds(transition.bad, &state, work)? {
                failed_action = Some(a);
                break;
            }
        }
        let mut sequence = vec![];
        for &previous in layers[..layers.len() - 1].iter().rev() {
            let mut target = b.cube(&values(&state), work)?;
            // Undo the deterministic check actions before undoing the primitive
            // action. Internal check IDs never appear in user counterexamples.
            for check in self.checks.iter().rev() {
                target = b.substitute(target, &check.updates, work)?;
            }
            let mut predecessor = None;
            for (a, transition) in self.transitions.iter().enumerate() {
                // Regression is exact for a concrete target, even when the
                // forward update is many-to-one (e.g. unconditional deletes).
                let preimage = b.substitute(target, &transition.updates, work)?;
                let preimage = b.and(preimage, transition.enabled, work)?;
                let candidates = b.and(previous, preimage, work)?;
                if let Some(values) = b.witness(candidates, self.variables, work) {
                    predecessor = Some((a, values));
                    break;
                }
            }
            let (a, values) =
                predecessor.ok_or_else(|| internal("symbolic witness has no predecessor"))?;
            sequence.push(a);
            state = values;
        }
        sequence.reverse();
        sequence.extend(failed_action);
        let prefix: BTreeSet<_> = sequence.iter().copied().collect();
        sequence.extend(
            c.order
                .topological
                .iter()
                .filter(|a| !prefix.contains(a))
                .copied(),
        );
        let mut done = vec![false; c.actions.len()];
        for &a in &sequence {
            if done[a] || c.order.predecessors[a].iter().any(|&p| !done[p]) {
                return Err(internal("symbolic witness violates the submitted order"));
            }
            done[a] = true;
        }
        Ok(sequence)
    }
}

fn values(state: &[bool]) -> BTreeMap<usize, bool> {
    state
        .iter()
        .enumerate()
        .step_by(2)
        .map(|(i, &value)| (i, value))
        .collect()
}

fn internal(message: &str) -> Diagnostic {
    Diagnostic::new(Status::InternalError, "symbolic_invariant", message)
}

pub(crate) fn validate(
    initial: &BTreeSet<Atom>,
    c: &Certificate,
    goal: &Condition,
    work: &mut Work,
) -> Result<()> {
    let mut system = System::new(initial, c, goal, work)?;
    let mut layers = vec![system.initial];
    let mut collect_at = 16_384;
    for depth in 0..=c.actions.len() {
        let current = layers[depth];
        if depth == c.actions.len() {
            let bad = system.booleans.and(current, system.final_failure, work)?;
            if bad != FALSE {
                return Err(system.counterexample(bad, &layers, initial, c, goal, work));
            }
            return Ok(());
        }
        let mut next = FALSE;
        for transition in &system.transitions {
            // Test each failure against the reachable frontier. A disjunction
            // of all failures over arbitrary states can be exponentially larger
            // even for a totally ordered plan with just one reachable prefix.
            let bad = system.booleans.and(current, transition.bad, work)?;
            if bad != FALSE {
                return Err(system.counterexample(bad, &layers, initial, c, goal, work));
            }
            let image = transition.image(&mut system.booleans, current, work)?;
            next = system.booleans.or(next, image, work)?;
        }
        // An unfinished ideal in an acyclic order has a permitted action. Bad
        // actions were checked above, so silently losing all paths is a bug.
        if next == FALSE {
            return Err(internal("nonterminal symbolic frontier has no successor"));
        }
        layers.push(system.saturate(next, work)?);
        if system.booleans.node_count() >= collect_at {
            system.collect(&layers, work);
            collect_at = 16_384.max(system.booleans.node_count().saturating_mul(2));
        }
    }
    unreachable!("the final frontier returns a verdict")
}
