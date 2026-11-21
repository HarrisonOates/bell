use crate::{
    ExecutionBackend,
    hierarchy::Certificate,
    modal::Analyzer,
    model::{Atom, Condition, Model},
    order::Order,
    report::{Diagnostic, Result},
    symbolic,
    work::Work,
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn validate(
    model: &Model<'_>,
    certificate: &Certificate,
    goal: &Condition,
    backend: ExecutionBackend,
    work: &mut Work,
) -> Result<()> {
    if backend == ExecutionBackend::Symbolic {
        return symbolic::validate(&model.initial, certificate, goal, work);
    }
    let use_mtc = mtc_applicable(certificate, goal, work)?;
    let n = certificate.actions.len();
    let mut changed = BTreeSet::new();
    for action in &certificate.actions {
        for atom in action.add.iter().chain(&action.delete).chain(
            action
                .conditional
                .iter()
                .flat_map(|e| e.add.iter().chain(&e.delete)),
        ) {
            work.tick();
            changed.insert(atom.clone());
        }
    }
    let mut dynamic = false;
    let mut impossible = None;
    for event in &certificate.events[n..] {
        match event
            .condition
            .static_value(&model.initial, &changed, work)?
        {
            None => dynamic = true,
            Some(false) => impossible = Some(event),
            Some(true) => (),
        }
    }
    if backend == ExecutionBackend::Mtc && (!use_mtc || dynamic) {
        return Err(Diagnostic::unsupported(
            "the mtc backend requires conjunctive action conditions and goals, unconditional effects, and static method preconditions; use auto or symbolic",
        ));
    }
    if let Some(event) = impossible {
        return Err(Diagnostic::invalid(
            "method_precondition",
            "method precondition can never hold",
        )
        .task(&event.id));
    }
    if use_mtc {
        mtc(model, certificate, goal, work)?;
        if !dynamic {
            return Ok(());
        }
    }
    if certificate.order.total() {
        return replay(&model.initial, certificate, &certificate.order, goal, work);
    }
    // A sufficient modal proof can settle a plan without constructing reachable
    // sets. An unsuccessful proof delegates directly, without refining the order.
    if Analyzer::new(certificate, &model.initial, goal, work)?.prove(
        certificate,
        &certificate.order,
        work,
    )? {
        return Ok(());
    }
    // Cheap concrete counterexample, especially useful for large static goals.
    replay(&model.initial, certificate, &certificate.order, goal, work)?;
    symbolic::validate(&model.initial, certificate, goal, work)
}

fn replay(
    initial: &BTreeSet<Atom>,
    c: &Certificate,
    order: &Order,
    goal: &Condition,
    work: &mut Work,
) -> Result<()> {
    replay_sequence(initial, c, &order.topological, goal, work)
}

/// Concrete witness verification, also shared with symbolic counterexamples.
pub(crate) fn replay_sequence(
    initial: &BTreeSet<Atom>,
    c: &Certificate,
    sequence: &[usize],
    goal: &Condition,
    work: &mut Work,
) -> Result<()> {
    work.charge((c.events.len() + initial.len() + c.actions.len()) as u64);
    let mut prefix = Prefix {
        done: vec![false; c.events.len()],
        state: initial.clone(),
        trace: vec![],
    };
    for &i in sequence {
        saturate(c, &mut prefix, work)?;
        check_action(c, &prefix, i, work)?;
        c.actions[i].apply(&mut prefix.state, work)?;
        prefix.done[i] = true;
        prefix.trace.push(i);
    }
    saturate(c, &mut prefix, work)?;
    check_finish(c, &prefix, goal, work)
}

/// Explicit state/prefix explorer, an independent regression reference for
/// exact BDD reachability and the optional modal proof pass.
#[cfg(test)]
fn explore(
    initial: &BTreeSet<Atom>,
    certificate: &Certificate,
    goal: &Condition,
    work: &mut Work,
) -> Result<()> {
    let n = certificate.actions.len();
    work.charge((certificate.events.len() + initial.len() + n) as u64);
    let initial = Prefix {
        done: vec![false; certificate.events.len()],
        state: initial.clone(),
        trace: vec![],
    };
    let mut stack = vec![initial];
    let mut seen = BTreeSet::new();
    while let Some(mut prefix) = stack.pop() {
        work.tick();
        saturate(certificate, &mut prefix, work)?;
        work.charge((prefix.done.len() + prefix.state.len()) as u64);
        let key = (prefix.done.clone(), prefix.state.clone());
        if !seen.insert(key) {
            continue;
        }
        if prefix.trace.len() == n {
            check_finish(certificate, &prefix, goal, work)?;
            continue;
        }
        for &i in certificate.order.topological.iter().rev() {
            work.tick();
            if prefix.done[i]
                || certificate.order.predecessors[i]
                    .iter()
                    .any(|&p| !prefix.done[p])
            {
                continue;
            }
            // Every submitted-order choice must work. A false precondition or
            // unplaceable guard is a counterexample, never a pruned branch.
            check_action(certificate, &prefix, i, work)?;
            work.charge((prefix.done.len() + prefix.state.len() + prefix.trace.len()) as u64);
            let mut next = prefix.clone();
            certificate.actions[i].apply(&mut next.state, work)?;
            next.done[i] = true;
            next.trace.push(i);
            stack.push(next);
        }
    }
    Ok(())
}

fn mtc_applicable(c: &Certificate, goal: &Condition, work: &mut Work) -> Result<bool> {
    for action in &c.actions {
        if !action.conditional.is_empty() || action.condition.conjunction(work)?.is_none() {
            return Ok(false);
        }
    }
    Ok(goal.conjunction(work)?.is_some())
}

#[derive(Clone)]
struct Prefix {
    done: Vec<bool>,
    state: BTreeSet<Atom>,
    trace: Vec<usize>,
}

fn check_action(c: &Certificate, p: &Prefix, i: usize, work: &mut Work) -> Result<()> {
    work.tick();
    let problem = if c.hierarchy.predecessors[i].iter().any(|&j| !p.done[j]) {
        Some((
            "method_precondition",
            "required method precondition cannot hold before this action",
        ))
    } else if !c.actions[i].condition.holds(&p.state, work)? {
        Some(("action_precondition", "action precondition fails"))
    } else {
        None
    };
    if let Some((code, message)) = problem {
        let mut error = failure(c, p, code, message, i);
        error.counterexample.push(c.events[i].id.clone());
        return Err(error);
    }
    Ok(())
}

fn check_finish(c: &Certificate, p: &Prefix, goal: &Condition, work: &mut Work) -> Result<()> {
    if let Some(i) = (c.actions.len()..p.done.len()).find(|&i| !p.done[i]) {
        return Err(failure(
            c,
            p,
            "method_precondition",
            "method precondition has no legal placement",
            i,
        ));
    }
    if !goal.holds(&p.state, work)? {
        let mut error =
            Diagnostic::invalid("goal", "goal fails after a permitted linearization").task("goal");
        error.counterexample = p.trace.iter().map(|&i| c.events[i].id.clone()).collect();
        return Err(error);
    }
    Ok(())
}

fn failure(c: &Certificate, p: &Prefix, code: &str, message: &str, i: usize) -> Diagnostic {
    let mut error = Diagnostic::invalid(code, message).task(&c.events[i].id);
    error.counterexample = p.trace.iter().map(|&i| c.events[i].id.clone()).collect();
    error
}
fn saturate(c: &Certificate, p: &mut Prefix, work: &mut Work) -> Result<()> {
    if c.events.len() == c.actions.len() {
        return Ok(());
    }
    // A topological pass suffices: guards have no effects, and every guard
    // predecessor is visited before it. Check again after each real action.
    for &i in &c.hierarchy.topological {
        work.tick();
        if i >= c.actions.len()
            && !p.done[i]
            && c.hierarchy.predecessors[i].iter().all(|&j| p.done[j])
            && c.events[i].condition.holds(&p.state, work)?
        {
            p.done[i] = true;
        }
    }
    Ok(())
}

fn mtc(model: &Model<'_>, c: &Certificate, goal: &Condition, work: &mut Work) -> Result<()> {
    let n = c.actions.len();
    let mut adds: BTreeMap<&Atom, Vec<usize>> = BTreeMap::new();
    let mut deletes: BTreeMap<&Atom, Vec<usize>> = BTreeMap::new();
    for (i, a) in c.actions.iter().enumerate() {
        for atom in &a.add {
            adds.entry(atom).or_default().push(i);
        }
        for atom in &a.delete {
            deletes.entry(atom).or_default().push(i);
        }
    }
    for (consumer, condition) in c
        .actions
        .iter()
        .map(|a| &a.condition)
        .chain(std::iter::once(goal))
        .enumerate()
    {
        let id = if consumer == n {
            "goal"
        } else {
            &c.events[consumer].id
        };
        if matches!(condition, Condition::False) {
            return Err(
                Diagnostic::invalid("false_condition", "condition simplifies to false").task(id),
            );
        }
        let before = |a: usize, b: usize| b == n || (a < n && c.order.before(a, b));
        for literal in condition
            .conjunction(work)?
            .expect("MTC requires conjunctions")
        {
            work.tick();
            let (producers, destroyers) = if literal.positive {
                (&adds, &deletes)
            } else {
                (&deletes, &adds)
            };
            let mut support = vec![];
            if let Some(producers) = producers.get(&literal.atom) {
                for &a in producers {
                    work.tick();
                    if before(a, consumer) {
                        support.push(a);
                    }
                }
            }
            let label = format!(
                "{}{}",
                if literal.positive { "" } else { "not " },
                model.atom_label(&literal.atom)
            );
            if model.initial.contains(&literal.atom) != literal.positive && support.is_empty() {
                return Err(Diagnostic::invalid(
                    "missing_support",
                    format!("{label} is not guaranteed before {id}"),
                )
                .task(id));
            }
            for &d in destroyers.get(&literal.atom).into_iter().flatten() {
                work.tick();
                if d == consumer || (consumer < n && before(consumer, d)) {
                    continue;
                }
                let mut restored = false;
                for &r in &support {
                    work.tick();
                    if before(d, r) {
                        restored = true;
                        break;
                    }
                }
                if !restored {
                    return Err(Diagnostic::invalid(
                        "unresolved_threat",
                        format!(
                            "{} can destroy {label} before {id} without a guaranteed restoration",
                            c.events[d].id
                        ),
                    )
                    .task(id));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Status,
        hierarchy::Event,
        model::{ConditionalEffect, GroundAction, Literal},
    };

    fn atom(predicate: usize) -> Atom {
        Atom {
            predicate,
            arguments: vec![],
        }
    }
    fn state(mask: usize) -> BTreeSet<Atom> {
        (0..3)
            .filter(|bit| mask & (1 << bit) != 0)
            .map(atom)
            .collect()
    }
    fn condition(mask: usize) -> Condition {
        Condition::Or(
            (0..8)
                .filter(|row| mask & (1 << row) != 0)
                .map(|row| {
                    Condition::And(
                        (0..3)
                            .map(|bit| {
                                Condition::Literal(Literal {
                                    atom: atom(bit),
                                    positive: row & (1 << bit) != 0,
                                })
                            })
                            .collect(),
                    )
                })
                .collect(),
        )
    }

    #[test]
    fn symbolic_reachability_and_modal_proofs_match_prefix_reference_with_nested_guards() {
        let mut seed = 71u64;
        let mut random = |bound: usize| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 32) as usize % bound
        };
        let mut valid = 0;
        let mut invalid = 0;
        for case in 0..1500 {
            let mut work = Work::default();
            let actions: Vec<_> = (0..4)
                .map(|_| GroundAction {
                    condition: if random(4) == 0 {
                        condition(random(256))
                    } else {
                        Condition::True
                    },
                    add: state(random(8)),
                    delete: state(random(8)),
                    cost: 0,
                    conditional: (0..2)
                        .map(|_| ConditionalEffect {
                            condition: condition(random(256)),
                            add: state(random(8)),
                            delete: state(random(8)),
                        })
                        .collect(),
                })
                .collect();
            let mut events: Vec<_> = actions
                .iter()
                .enumerate()
                .map(|(i, a)| Event {
                    id: i.to_string(),
                    condition: a.condition.clone(),
                })
                .collect();
            for i in 4..8 {
                events.push(Event {
                    id: i.to_string(),
                    condition: if i % 2 == 0 && random(2) == 0 {
                        condition(random(256))
                    } else {
                        Condition::True
                    },
                });
            }
            let mut hierarchy_edges = vec![(4, 0), (0, 5), (6, 1), (1, 7)];
            match case % 4 {
                1 => hierarchy_edges.push((5, 6)),
                2 => hierarchy_edges.extend([(4, 6), (7, 5)]),
                3 => hierarchy_edges.extend([(0, 6), (7, 5)]),
                _ => (),
            }
            let hierarchy = Order::new(8, hierarchy_edges, &mut work).unwrap();
            let mut edges = vec![];
            for a in 0..4 {
                for b in a + 1..4 {
                    if hierarchy.before(a, b) || random(3) == 0 {
                        edges.push((a, b));
                    }
                }
            }
            let order = Order::new(4, edges, &mut work).unwrap();
            let c = Certificate {
                actions,
                events,
                hierarchy,
                order,
            };
            let initial = state(random(8));
            let goal = if random(2) == 0 {
                Condition::True
            } else {
                condition(random(256))
            };
            let actual = symbolic::validate(&initial, &c, &goal, &mut work).map_err(|e| e.status);
            if Analyzer::new(&c, &initial, &goal, &mut work)
                .unwrap()
                .prove(&c, &c.order, &mut work)
                .unwrap()
            {
                assert_eq!(actual, Ok(()), "unsound modal proof in case {case}");
            }
            let expected = explore(&initial, &c, &goal, &mut Work::default()).map_err(|e| e.status);
            assert_eq!(
                actual, expected,
                "case {case}, initial={initial:?}, goal={goal:?}"
            );
            match actual {
                Ok(()) => valid += 1,
                Err(Status::InvalidPlan) => invalid += 1,
                other => panic!("{other:?}"),
            }
        }
        assert!(valid > 100, "only {valid} valid cases");
        assert!(invalid > 100, "only {invalid} invalid cases");
    }
}
