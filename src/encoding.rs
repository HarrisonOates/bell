//! Shared exact Boolean compilation of grounded conditions and action effects.
use crate::{
    boolean::{Booleans, FALSE, Formula, TRUE},
    model::{Atom, Condition, GroundAction},
    report::Result,
    work::Work,
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct Encoding {
    pub booleans: Booleans,
    pub atoms: BTreeMap<Atom, usize>,
    stride: usize,
    static_facts: Option<StaticFacts>,
}

struct StaticFacts {
    initial: BTreeSet<Atom>,
    written: BTreeSet<Atom>,
}

impl Encoding {
    /// Symbolic reachability reserves the odd variables for next-state values.
    pub fn new(stride: usize) -> Self {
        Self {
            booleans: Booleans::new(),
            atoms: BTreeMap::new(),
            stride,
            static_facts: None,
        }
    }

    /// Facts outside the conservative write set never change in execution.
    /// Fold them before constructing BDDs, including in conditional guards.
    pub fn with_static_facts(
        stride: usize,
        initial: BTreeSet<Atom>,
        written: BTreeSet<Atom>,
    ) -> Self {
        Self {
            static_facts: Some(StaticFacts { initial, written }),
            ..Self::new(stride)
        }
    }

    fn atom(&mut self, atom: &Atom, work: &mut Work) -> usize {
        if let Some(&variable) = self.atoms.get(atom) {
            return variable;
        }
        work.charge(2 + atom.arguments.len() as u64);
        let variable = self.stride * self.atoms.len();
        self.atoms.insert(atom.clone(), variable);
        variable
    }

    pub fn compile(&mut self, condition: &Condition, work: &mut Work) -> Result<Formula> {
        let mut stack = vec![(condition, false)];
        let mut values = vec![];
        while let Some((condition, combine)) = stack.pop() {
            work.tick();
            let value = match condition {
                Condition::True => TRUE,
                Condition::False => FALSE,
                Condition::Literal(literal) => {
                    if let Some(fixed) = &self.static_facts
                        && !fixed.written.contains(&literal.atom)
                    {
                        if fixed.initial.contains(&literal.atom) == literal.positive {
                            TRUE
                        } else {
                            FALSE
                        }
                    } else {
                        let variable = self.atom(&literal.atom, work);
                        let formula = self.booleans.variable(variable, work)?;
                        if literal.positive {
                            formula
                        } else {
                            self.booleans.not(formula, work)?
                        }
                    }
                }
                Condition::And(parts) | Condition::Or(parts) => {
                    if !combine {
                        work.charge(1 + parts.len() as u64);
                        stack.push((condition, true));
                        stack.extend(parts.iter().map(|p| (p, false)));
                        continue;
                    }
                    let conjunction = matches!(condition, Condition::And(_));
                    let mut value = if conjunction { TRUE } else { FALSE };
                    for _ in parts {
                        let part = values.pop().unwrap();
                        value = if conjunction {
                            self.booleans.and(value, part, work)?
                        } else {
                            self.booleans.or(value, part, work)?
                        };
                    }
                    value
                }
            };
            work.tick();
            values.push(value);
        }
        Ok(values[0])
    }

    /// Parallel updates in the OLD state. Absent entries are identity updates.
    pub fn effects(
        &mut self,
        action: &GroundAction,
        work: &mut Work,
    ) -> Result<BTreeMap<usize, Formula>> {
        let mut adds = BTreeMap::new();
        let mut deletes = BTreeMap::new();
        for atom in &action.add {
            adds.insert(self.atom(atom, work), TRUE);
        }
        for atom in &action.delete {
            deletes.insert(self.atom(atom, work), TRUE);
        }
        for effect in &action.conditional {
            let guard = self.compile(&effect.condition, work)?;
            if guard == FALSE {
                continue;
            }
            for (atoms, targets) in [(&effect.add, &mut adds), (&effect.delete, &mut deletes)] {
                for atom in atoms {
                    let variable = self.atom(atom, work);
                    let old = targets.get(&variable).copied().unwrap_or(FALSE);
                    let union = self.booleans.or(old, guard, work)?;
                    targets.insert(variable, union);
                }
            }
        }
        let changed: BTreeSet<_> = adds.keys().chain(deletes.keys()).copied().collect();
        let mut updates = BTreeMap::new();
        for variable in changed {
            let add = adds.get(&variable).copied().unwrap_or(FALSE);
            let delete = deletes.get(&variable).copied().unwrap_or(FALSE);
            let old = self.booleans.variable(variable, work)?;
            let keep = self.booleans.not(delete, work)?;
            let kept = self.booleans.and(old, keep, work)?;
            let next = self.booleans.or(add, kept, work)?;
            if old != next {
                updates.insert(variable, next);
            }
        }
        Ok(updates)
    }
}
