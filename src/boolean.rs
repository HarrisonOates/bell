// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

//! Reduced ordered Boolean decision diagrams for regression and reachability.
//! Operations use explicit stacks; large grounded formulas cannot overflow the
//! call stack. Both retained nodes and operation-cache entries consume work.
use crate::{report::Result, work::Work};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) type Formula = usize;
pub(crate) const FALSE: Formula = 0;
pub(crate) const TRUE: Formula = 1;

#[derive(Clone, Copy)]
struct Node {
    variable: usize,
    low: Formula,
    high: Formula,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operations_and_parallel_substitution_match_all_two_variable_truth_tables() {
        let mut b = Booleans::new();
        let mut work = Work::default();
        let x = b.variable(0, &mut work).unwrap();
        let y = b.variable(1, &mut work).unwrap();
        let nx = b.not(x, &mut work).unwrap();
        let ny = b.not(y, &mut work).unwrap();
        let cubes =
            [(nx, ny), (x, ny), (nx, y), (x, y)].map(|(x, y)| b.and(x, y, &mut work).unwrap());
        let formulas: Vec<_> = (0..16)
            .map(|mask| {
                let mut f = FALSE;
                for (state, &cube) in cubes.iter().enumerate() {
                    if mask & (1 << state) != 0 {
                        f = b.or(f, cube, &mut work).unwrap();
                    }
                }
                f
            })
            .collect();
        assert_eq!(formulas.iter().copied().collect::<BTreeSet<_>>().len(), 16);
        for a in 0..16 {
            assert_eq!(b.not(formulas[a], &mut work).unwrap(), formulas[15 ^ a]);
            for c in 0..16 {
                assert_eq!(
                    b.and(formulas[a], formulas[c], &mut work).unwrap(),
                    formulas[a & c]
                );
                assert_eq!(
                    b.or(formulas[a], formulas[c], &mut work).unwrap(),
                    formulas[a | c]
                );
                assert_eq!(
                    b.entails(formulas[a], formulas[c], &mut work).unwrap(),
                    a & !c == 0
                );
                for quantified in 0..4 {
                    let variables = (0..2).filter(|i| quantified & (1 << i) != 0).collect();
                    let result = b
                        .and_exists(formulas[a], formulas[c], &variables, &mut work)
                        .unwrap();
                    let mut expected = 0;
                    for state in 0..4 {
                        if (0..4).any(|witness| {
                            (state ^ witness) & (3 ^ quantified) == 0
                                && (a & c) & (1 << witness) != 0
                        }) {
                            expected |= 1 << state;
                        }
                    }
                    assert_eq!(result, formulas[expected]);
                    assert_eq!(
                        b.exists(formulas[a & c], &variables, &mut work).unwrap(),
                        result
                    );
                    let witness = b.witness(result, 2, &mut work);
                    assert_eq!(witness.is_some(), expected != 0);
                    if let Some(witness) = witness {
                        assert!(b.holds(result, &witness, &mut work).unwrap());
                    }
                }
                for (mask, &formula) in formulas.iter().enumerate() {
                    let actual = b
                        .substitute(
                            formula,
                            &BTreeMap::from([(0, formulas[a]), (1, formulas[c])]),
                            &mut work,
                        )
                        .unwrap();
                    for state in 0..4 {
                        let new_state = ((a >> state) & 1) | (((c >> state) & 1) << 1);
                        assert_eq!(
                            b.holds(actual, &[state & 1 != 0, state & 2 != 0], &mut work)
                                .unwrap(),
                            mask & (1 << new_state) != 0
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn garbage_collection_preserves_roots_and_reuses_only_dead_nodes() {
        let mut b = Booleans::new();
        let mut work = Work::default();
        let x = b.variable(0, &mut work).unwrap();
        let y = b.variable(1, &mut work).unwrap();
        let keep = b.equivalent(x, y, &mut work).unwrap();
        let expected: Vec<_> = (0..4)
            .map(|s| b.holds(keep, &[s & 1 != 0, s & 2 != 0], &mut work).unwrap())
            .collect();
        for i in 2..100 {
            let unused = b.variable(i, &mut work).unwrap();
            b.and(keep, unused, &mut work).unwrap();
        }
        let before = b.node_count();
        b.collect([keep], &mut work);
        assert!(b.node_count() < before / 2);
        assert!(b.cache.is_empty());
        for round in 0..10 {
            let other = b.variable(2 + round, &mut work).unwrap();
            let value = b.and(keep, other, &mut work).unwrap();
            b.collect([keep, value], &mut work);
            let projected = b
                .exists(value, &BTreeSet::from([2 + round]), &mut work)
                .unwrap();
            assert_eq!(projected, keep);
            for (s, &expected) in expected.iter().enumerate() {
                assert_eq!(
                    b.holds(keep, &[s & 1 != 0, s & 2 != 0], &mut work).unwrap(),
                    expected
                );
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Operation {
    And,
    Or,
    Xor,
}

pub(crate) struct Booleans {
    nodes: Vec<Node>,
    free: Vec<Formula>,
    unique: BTreeMap<(usize, Formula, Formula), Formula>,
    cache: BTreeMap<(Operation, Formula, Formula), Formula>,
}

impl Booleans {
    pub fn new() -> Self {
        Self {
            nodes: vec![
                Node {
                    variable: usize::MAX,
                    low: FALSE,
                    high: FALSE
                };
                2
            ],
            free: vec![],
            unique: BTreeMap::new(),
            cache: BTreeMap::new(),
        }
    }

    fn node(
        &mut self,
        variable: usize,
        low: Formula,
        high: Formula,
        work: &mut Work,
    ) -> Result<Formula> {
        work.tick();
        if low == high {
            return Ok(low);
        }
        let key = (variable, low, high);
        if let Some(&id) = self.unique.get(&key) {
            return Ok(id);
        }
        work.charge(4);
        let node = Node {
            variable,
            low,
            high,
        };
        let id = if let Some(id) = self.free.pop() {
            self.nodes[id] = node;
            id
        } else {
            let id = self.nodes.len();
            self.nodes.push(node);
            id
        };
        self.unique.insert(key, id);
        Ok(id)
    }

    pub fn variable(&mut self, variable: usize, work: &mut Work) -> Result<Formula> {
        self.node(variable, FALSE, TRUE, work)
    }

    fn known(&self, op: Operation, a: Formula, b: Formula) -> Option<Formula> {
        // All calls use a <= b, and the two terminals have the lowest IDs.
        match op {
            Operation::And if a == FALSE => Some(FALSE),
            Operation::And if a == TRUE || a == b => Some(b),
            Operation::Or if a == FALSE || a == b => Some(b),
            Operation::Or if a == TRUE => Some(TRUE),
            Operation::Xor if a == FALSE => Some(b),
            Operation::Xor if a == b => Some(FALSE),
            _ => self.cache.get(&(op, a, b)).copied(),
        }
    }

    fn apply(&mut self, op: Operation, a: Formula, b: Formula, work: &mut Work) -> Result<Formula> {
        let pair = |a: Formula, b: Formula| (a.min(b), a.max(b));
        let root = pair(a, b);
        let mut stack = vec![root];
        while let Some((a, b)) = stack.pop() {
            work.tick();
            if self.known(op, a, b).is_some() {
                continue;
            }
            let left = self.nodes[a];
            let right = self.nodes[b];
            let variable = left.variable.min(right.variable);
            let (al, ah) = if left.variable == variable {
                (left.low, left.high)
            } else {
                (a, a)
            };
            let (bl, bh) = if right.variable == variable {
                (right.low, right.high)
            } else {
                (b, b)
            };
            let low = pair(al, bl);
            let high = pair(ah, bh);
            match (self.known(op, low.0, low.1), self.known(op, high.0, high.1)) {
                (Some(low), Some(high)) => {
                    let result = self.node(variable, low, high, work)?;
                    work.charge(4);
                    self.cache.insert((op, a, b), result);
                }
                (low_result, high_result) => {
                    work.charge(3);
                    stack.push((a, b));
                    if high_result.is_none() {
                        stack.push(high);
                    }
                    if low_result.is_none() {
                        stack.push(low);
                    }
                }
            }
        }
        Ok(self.known(op, root.0, root.1).unwrap())
    }

    pub fn and(&mut self, a: Formula, b: Formula, work: &mut Work) -> Result<Formula> {
        self.apply(Operation::And, a, b, work)
    }
    pub fn or(&mut self, a: Formula, b: Formula, work: &mut Work) -> Result<Formula> {
        self.apply(Operation::Or, a, b, work)
    }
    pub fn not(&mut self, a: Formula, work: &mut Work) -> Result<Formula> {
        self.apply(Operation::Xor, a, TRUE, work)
    }
    pub fn equivalent(&mut self, a: Formula, b: Formula, work: &mut Work) -> Result<Formula> {
        let different = self.apply(Operation::Xor, a, b, work)?;
        self.not(different, work)
    }

    /// Relational product: existential abstraction DURING conjunction, without
    /// first materializing the potentially much larger conjunction BDD.
    pub fn and_exists(
        &mut self,
        a: Formula,
        b: Formula,
        variables: &BTreeSet<usize>,
        work: &mut Work,
    ) -> Result<Formula> {
        if variables.is_empty() {
            return self.and(a, b, work);
        }
        let pair = |a: Formula, b: Formula| (a.min(b), a.max(b));
        let root = pair(a, b);
        let mut done = BTreeMap::new();
        let known = |a, b, done: &BTreeMap<(Formula, Formula), Formula>| {
            if a == FALSE {
                Some(FALSE)
            } else if a == TRUE && b == TRUE {
                Some(TRUE)
            } else {
                done.get(&(a, b)).copied()
            }
        };
        let mut stack = vec![root];
        while let Some((a, b)) = stack.pop() {
            work.tick();
            if known(a, b, &done).is_some() {
                continue;
            }
            let left = self.nodes[a];
            let right = self.nodes[b];
            let variable = left.variable.min(right.variable);
            let (al, ah) = if left.variable == variable {
                (left.low, left.high)
            } else {
                (a, a)
            };
            let (bl, bh) = if right.variable == variable {
                (right.low, right.high)
            } else {
                (b, b)
            };
            let low = pair(al, bl);
            let high = pair(ah, bh);
            match (known(low.0, low.1, &done), known(high.0, high.1, &done)) {
                (Some(low), Some(high)) => {
                    let value = if variables.contains(&variable) {
                        self.or(low, high, work)?
                    } else {
                        self.node(variable, low, high, work)?
                    };
                    work.charge(3);
                    done.insert((a, b), value);
                }
                (low_result, high_result) => {
                    stack.push((a, b));
                    if high_result.is_none() {
                        stack.push(high);
                    }
                    if low_result.is_none() {
                        stack.push(low);
                    }
                }
            }
        }
        Ok(known(root.0, root.1, &done).unwrap())
    }

    pub fn exists(
        &mut self,
        formula: Formula,
        variables: &BTreeSet<usize>,
        work: &mut Work,
    ) -> Result<Formula> {
        self.and_exists(formula, TRUE, variables, work)
    }

    pub fn cube(&mut self, values: &BTreeMap<usize, bool>, work: &mut Work) -> Result<Formula> {
        let mut result = TRUE;
        for (&variable, &value) in values.iter().rev() {
            result = if value {
                self.node(variable, FALSE, result, work)?
            } else {
                self.node(variable, result, FALSE, work)?
            };
        }
        Ok(result)
    }

    /// A full assignment, with don't-care variables set to false.
    pub fn witness(
        &self,
        mut formula: Formula,
        variables: usize,
        work: &mut Work,
    ) -> Option<Vec<bool>> {
        if formula == FALSE {
            return None;
        }
        work.charge(variables as u64);
        let mut values = vec![false; variables];
        while formula > TRUE {
            work.tick();
            let node = self.nodes[formula];
            let high = node.low == FALSE;
            values[node.variable] = high;
            formula = if high { node.high } else { node.low };
        }
        Some(values)
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len() - self.free.len()
    }

    /// Reclaim unreachable nodes while preserving IDs of all live roots. The
    /// caller supplies EVERY retained formula; operation caches are discarded.
    pub fn collect(&mut self, roots: impl IntoIterator<Item = Formula>, work: &mut Work) {
        self.cache.clear();
        let mut live = vec![false; self.nodes.len()];
        live[FALSE] = true;
        live[TRUE] = true;
        let mut pending: Vec<_> = roots.into_iter().collect();
        while let Some(id) = pending.pop() {
            work.tick();
            if live[id] {
                continue;
            }
            live[id] = true;
            let node = self.nodes[id];
            debug_assert_ne!(node.variable, usize::MAX);
            pending.extend([node.low, node.high]);
        }
        self.unique.retain(|_, id| live[*id]);
        for (id, node) in self.nodes.iter_mut().enumerate().skip(2) {
            work.tick();
            if !live[id] && node.variable != usize::MAX {
                *node = Node {
                    variable: usize::MAX,
                    low: FALSE,
                    high: FALSE,
                };
                self.free.push(id);
            }
        }
    }
    pub fn entails(&mut self, a: Formula, b: Formula, work: &mut Work) -> Result<bool> {
        let not_b = self.not(b, work)?;
        Ok(self.and(a, not_b, work)? == FALSE)
    }

    pub fn holds(&self, mut formula: Formula, state: &[bool], work: &mut Work) -> Result<bool> {
        while formula > TRUE {
            work.tick();
            let node = self.nodes[formula];
            formula = if state[node.variable] {
                node.high
            } else {
                node.low
            };
        }
        Ok(formula == TRUE)
    }

    pub fn support(&self, formula: Formula, work: &mut Work) -> Result<BTreeSet<usize>> {
        let mut result = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![formula];
        while let Some(id) = stack.pop() {
            work.tick();
            if id <= TRUE || !seen.insert(id) {
                continue;
            }
            work.charge(3);
            let node = self.nodes[id];
            result.insert(node.variable);
            stack.extend([node.low, node.high]);
        }
        Ok(result)
    }

    // Parallel substitution: replacements are formulas in the old state and
    // must not themselves be substituted. ITE restores variable ordering when
    // a replacement mentions variables earlier than the replaced one.
    pub fn substitute(
        &mut self,
        formula: Formula,
        replacements: &BTreeMap<usize, Formula>,
        work: &mut Work,
    ) -> Result<Formula> {
        let Some((&last_variable, _)) = replacements.last_key_value() else {
            return Ok(formula);
        };
        let mut done = BTreeMap::from([(FALSE, FALSE), (TRUE, TRUE)]);
        let mut stack = vec![formula];
        while let Some(id) = stack.pop() {
            work.tick();
            if done.contains_key(&id) {
                continue;
            }
            let node = self.nodes[id];
            // Variable ordering makes the whole suffix independent of every
            // replacement. Reuse it without traversing or rebuilding it.
            if node.variable > last_variable {
                done.insert(id, id);
                continue;
            }
            if let (Some(&low), Some(&high)) = (done.get(&node.low), done.get(&node.high)) {
                let test = match replacements.get(&node.variable) {
                    Some(&replacement) => replacement,
                    None => self.variable(node.variable, work)?,
                };
                let test_node = self.nodes[test];
                let result = if test == TRUE || low == high {
                    high
                } else if test == FALSE {
                    low
                } else if test_node.low == FALSE
                    && test_node.high == TRUE
                    && test_node.variable < self.nodes[low].variable
                    && test_node.variable < self.nodes[high].variable
                {
                    // Includes order-preserving next/current renames and
                    // unchanged nodes. General composition still uses ITE.
                    self.node(test_node.variable, low, high, work)?
                } else {
                    let negative = self.not(test, work)?;
                    let low = self.and(negative, low, work)?;
                    let high = self.and(test, high, work)?;
                    self.or(low, high, work)?
                };
                work.charge(2);
                done.insert(id, result);
            } else {
                work.charge(3);
                stack.extend([id, node.high, node.low]);
            }
        }
        Ok(done[&formula])
    }
}
