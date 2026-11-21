// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

use crate::{
    report::{Diagnostic, Result},
    work::Work,
};
use std::collections::{BTreeSet, VecDeque};

pub(crate) struct Order {
    pub successors: Vec<BTreeSet<usize>>,
    pub predecessors: Vec<BTreeSet<usize>>,
    pub topological: Vec<usize>,
    reach: Vec<Vec<u64>>,
}

impl Order {
    pub fn new(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
        work: &mut Work,
    ) -> Result<Self> {
        let words = n.div_ceil(64);
        let cells = n.checked_mul(words).ok_or_else(|| {
            Diagnostic::new(
                crate::Status::LimitExceeded,
                "order_size",
                "ordering graph is too large",
            )
        })?;
        work.charge(cells as u64 + n as u64);
        let mut successors = vec![BTreeSet::new(); n];
        let mut predecessors = vec![BTreeSet::new(); n];
        for (a, b) in edges {
            work.tick();
            if a >= n || b >= n {
                return Err(Diagnostic::input(
                    "ordering_reference",
                    "unknown ordering endpoint",
                ));
            }
            successors[a].insert(b);
            predecessors[b].insert(a);
        }
        let mut degree: Vec<_> = predecessors.iter().map(BTreeSet::len).collect();
        let mut ready: VecDeque<_> = (0..n).filter(|&i| degree[i] == 0).collect();
        let mut topological = Vec::with_capacity(n);
        while let Some(a) = ready.pop_front() {
            topological.push(a);
            for &b in &successors[a] {
                degree[b] -= 1;
                if degree[b] == 0 {
                    ready.push_back(b);
                }
            }
        }
        if topological.len() != n {
            return Err(Diagnostic::invalid(
                "ordering_cycle",
                "ordering constraints contain a cycle",
            ));
        }
        let mut reach = vec![vec![0; words]; n];
        for &a in topological.iter().rev() {
            for &b in &successors[a] {
                work.charge(words as u64);
                for w in 0..words {
                    reach[a][w] |= reach[b][w];
                }
                reach[a][b / 64] |= 1 << (b % 64);
            }
        }
        Ok(Self {
            successors,
            predecessors,
            topological,
            reach,
        })
    }
    pub fn before(&self, a: usize, b: usize) -> bool {
        self.reach[a][b / 64] & (1 << (b % 64)) != 0
    }
    pub fn total(&self) -> bool {
        self.topological.windows(2).all(|w| self.before(w[0], w[1]))
    }
    pub fn makespan(&self) -> usize {
        let mut length = vec![0; self.predecessors.len()];
        for &i in &self.topological {
            length[i] = 1 + self.predecessors[i]
                .iter()
                .map(|&p| length[p])
                .max()
                .unwrap_or(0);
        }
        length.into_iter().max().unwrap_or(0)
    }
}
