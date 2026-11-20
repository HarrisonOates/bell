use crate::{
    budget::Budget,
    hierarchy::Certificate,
    model::{Atom, Condition, Model},
    report::{Diagnostic, Result},
};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn validate(
    model: &Model<'_>,
    certificate: &Certificate,
    goal: &Condition,
    budget: &mut Budget,
) -> Result<()> {
    mtc(model, certificate, goal, budget)?;
    let n = certificate.actions.len();
    let changed: BTreeSet<_> = certificate
        .actions
        .iter()
        .flat_map(|a| a.add.iter().chain(&a.delete))
        .cloned()
        .collect();
    let mut dynamic = false;
    for event in &certificate.events[n..] {
        budget.tick()?;
        if event.condition.impossible {
            return Err(Diagnostic::invalid(
                "method_precondition",
                "method binding makes its precondition false",
            )
            .task(&event.id));
        }
        for literal in &event.condition.literals {
            if changed.contains(&literal.atom) {
                dynamic = true;
            } else if model.initial.contains(&literal.atom) != literal.positive {
                return Err(Diagnostic::invalid(
                    "method_precondition",
                    format!(
                        "method requires {}{}, which never holds",
                        if literal.positive { "" } else { "not " },
                        model.atom_label(&literal.atom)
                    ),
                )
                .task(&event.id));
            }
        }
    }
    if !dynamic {
        return Ok(());
    }
    let initial = Prefix {
        done: vec![false; certificate.events.len()],
        state: model.initial.clone(),
        trace: vec![],
    };
    let mut stack = vec![initial];
    let mut seen = BTreeSet::new();
    while let Some(mut prefix) = stack.pop() {
        budget.tick()?;
        saturate(certificate, &mut prefix, budget)?;
        let key = (prefix.done.clone(), prefix.state.clone());
        if !seen.insert(key) {
            continue;
        }
        budget.charge((prefix.done.len() + prefix.state.len()) as u64)?;
        if prefix.trace.len() == n {
            if let Some(i) = (n..prefix.done.len()).find(|&i| !prefix.done[i]) {
                return Err(failure(
                    certificate,
                    &prefix,
                    "method_precondition",
                    "method precondition has no legal placement",
                    i,
                ));
            }
            if !goal.holds(&prefix.state) {
                return Err(Diagnostic::invalid(
                    "goal",
                    "goal fails after a permitted linearization",
                ));
            }
            continue;
        }
        for &i in certificate.order.topological.iter().rev() {
            budget.tick()?;
            if prefix.done[i]
                || certificate.order.predecessors[i]
                    .iter()
                    .any(|&p| !prefix.done[p])
            {
                continue;
            }
            if certificate.hierarchy.predecessors[i]
                .iter()
                .any(|&p| !prefix.done[p])
            {
                let mut failed = prefix.clone();
                failed.trace.push(i);
                return Err(failure(
                    certificate,
                    &failed,
                    "method_precondition",
                    "required method precondition cannot hold before this action",
                    i,
                ));
            }
            if !certificate.actions[i].condition.holds(&prefix.state) {
                let mut failed = prefix.clone();
                failed.trace.push(i);
                return Err(failure(
                    certificate,
                    &failed,
                    "action_precondition",
                    "action precondition fails",
                    i,
                ));
            }
            budget.charge((prefix.done.len() + prefix.state.len() + prefix.trace.len()) as u64)?;
            let mut next = prefix.clone();
            certificate.actions[i].apply(&mut next.state);
            next.done[i] = true;
            next.trace.push(i);
            stack.push(next);
        }
    }
    Ok(())
}

#[derive(Clone)]
struct Prefix {
    done: Vec<bool>,
    state: BTreeSet<Atom>,
    trace: Vec<usize>,
}

fn failure(c: &Certificate, p: &Prefix, code: &str, message: &str, i: usize) -> Diagnostic {
    let mut error = Diagnostic::invalid(code, message).task(&c.events[i].id);
    error.counterexample = p.trace.iter().map(|&i| c.events[i].id.clone()).collect();
    error
}
fn saturate(c: &Certificate, p: &mut Prefix, budget: &mut Budget) -> Result<()> {
    // A topological pass suffices: guards have no effects, and every guard
    // predecessor is visited before it. Check again after each real action.
    for &i in &c.hierarchy.topological {
        budget.tick()?;
        if i >= c.actions.len()
            && !p.done[i]
            && c.hierarchy.predecessors[i].iter().all(|&j| p.done[j])
            && c.events[i].condition.holds(&p.state)
        {
            p.done[i] = true;
        }
    }
    Ok(())
}

fn mtc(model: &Model<'_>, c: &Certificate, goal: &Condition, budget: &mut Budget) -> Result<()> {
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
        if condition.impossible {
            return Err(Diagnostic::invalid(
                "false_condition",
                "condition contains a false ground equality",
            )
            .task(id));
        }
        let before = |a: usize, b: usize| b == n || (a < n && c.order.before(a, b));
        for literal in &condition.literals {
            budget.tick()?;
            let (producers, destroyers) = if literal.positive {
                (&adds, &deletes)
            } else {
                (&deletes, &adds)
            };
            let mut support = vec![];
            if let Some(producers) = producers.get(&literal.atom) {
                for &a in producers {
                    budget.tick()?;
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
                budget.tick()?;
                if d == consumer || (consumer < n && before(consumer, d)) {
                    continue;
                }
                let mut restored = false;
                for &r in &support {
                    budget.tick()?;
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
