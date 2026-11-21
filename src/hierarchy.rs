// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

use crate::{
    model::{Bindings, Condition, GroundAction, Model},
    order::Order,
    plan::{Occurrence, Plan},
    report::{Diagnostic, Result},
    work::Work,
};
use hddl_analyzer::HTN;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub(crate) struct Event {
    pub id: String,
    pub condition: Condition,
}
pub(crate) struct Certificate {
    pub actions: Vec<GroundAction>,
    pub order: Order,
    pub hierarchy: Order,
    pub events: Vec<Event>,
}

struct Builder<'a, 'm> {
    model: &'m Model<'a>,
    plan: &'m Plan,
    action_ids: BTreeMap<String, usize>,
    endpoints: BTreeMap<String, (usize, usize)>,
    events: Vec<Event>,
    edges: Vec<(usize, usize)>,
    queue: VecDeque<Occurrence>,
    expanded: BTreeSet<String>,
}

impl Builder<'_, '_> {
    fn introduce(&mut self, occurrence: &Occurrence) -> Result<(usize, usize)> {
        if self.endpoints.contains_key(&occurrence.id) {
            return Err(Diagnostic::invalid(
                "duplicate_introduction",
                "occurrence is introduced more than once (shared child or cycle)",
            )
            .task(&occurrence.id)
            .at(occurrence.location.clone()));
        }
        let pair = if let Some(&i) = self.action_ids.get(&occurrence.id) {
            if self.plan.actions[i].call != occurrence.call {
                return Err(Diagnostic::invalid(
                    "leaf_mismatch",
                    "action differs from the occurrence in the decomposition",
                )
                .task(&occurrence.id)
                .at(occurrence.location.clone()));
            }
            (i, i)
        } else {
            if self
                .model
                .actions
                .contains_key(occurrence.call.name.as_str())
            {
                return Err(Diagnostic::invalid(
                    "missing_action",
                    "primitive occurrence is missing from plan :htn",
                )
                .task(&occurrence.id)
                .at(occurrence.location.clone()));
            }
            let start = self.events.len();
            self.events.push(Event {
                id: occurrence.id.clone(),
                condition: Condition::default(),
            });
            self.events.push(Event {
                id: occurrence.id.clone(),
                condition: Condition::default(),
            });
            self.edges.push((start, start + 1));
            (start, start + 1)
        };
        self.endpoints.insert(occurrence.id.clone(), pair);
        self.queue.push_back(occurrence.clone());
        Ok(pair)
    }
    fn network(
        &mut self,
        tn: &HTN<'_>,
        children: &[Occurrence],
        env: &Bindings,
        parent: Option<(usize, usize)>,
        work: &mut Work,
    ) -> Result<()> {
        self.model.constraints(tn, env)?;
        if tn.subtasks.len() != children.len() {
            return Err(Diagnostic::invalid(
                "subtask_count",
                format!(
                    "expected {} subtasks, found {}",
                    tn.subtasks.len(),
                    children.len()
                ),
            ));
        }
        let mut endpoints = vec![];
        for (schema, occurrence) in tn.subtasks.iter().zip(children) {
            work.tick();
            if self.model.call(schema.task.name, &schema.terms, env)? != occurrence.call {
                return Err(Diagnostic::invalid(
                    "subtask_mismatch",
                    "subtasks must match the grounded source network in declaration order",
                )
                .task(&occurrence.id)
                .at(occurrence.location.clone()));
            }
            let pair = self.introduce(occurrence)?;
            if let Some((start, end)) = parent {
                self.edges.push((start, pair.0));
                self.edges.push((pair.1, end));
            }
            endpoints.push(pair);
        }
        let local = self.model.network_order(tn, work)?;
        for (a, successors) in local.successors.iter().enumerate() {
            for &b in successors {
                self.edges.push((endpoints[a].1, endpoints[b].0));
            }
        }
        Ok(())
    }
}

pub(crate) fn build(model: &Model<'_>, plan: &Plan, work: &mut Work) -> Result<Certificate> {
    let mut actions = vec![];
    let mut action_ids = BTreeMap::new();
    let mut events = vec![];
    for occurrence in &plan.actions {
        work.tick();
        let i = actions.len();
        if action_ids.insert(occurrence.id.clone(), i).is_some() {
            return Err(
                Diagnostic::invalid("duplicate_action_id", "duplicate action occurrence")
                    .task(&occurrence.id)
                    .at(occurrence.location.clone()),
            );
        }
        let action = model
            .ground_action(&occurrence.call, work)
            .map_err(|e| e.task(&occurrence.id).at(occurrence.location.clone()))?;
        events.push(Event {
            id: occurrence.id.clone(),
            condition: action.condition.clone(),
        });
        actions.push(action);
    }
    let plan_edges = plan
        .edges
        .iter()
        .map(|(a, b)| {
            let lookup = |id: &str| {
                action_ids.get(id).copied().ok_or_else(|| {
                    Diagnostic::invalid(
                        "ordering_reference",
                        format!("ordering refers to unknown action occurrence {id}"),
                    )
                })
            };
            Ok((lookup(a)?, lookup(b)?))
        })
        .collect::<Result<Vec<_>>>()?;
    let order = Order::new(actions.len(), plan_edges, work)?;
    let mut builder = Builder {
        model,
        plan,
        action_ids,
        endpoints: BTreeMap::new(),
        events,
        edges: vec![],
        queue: VecDeque::new(),
        expanded: BTreeSet::new(),
    };
    if let Some(root) = &model.problem.init_tn {
        let env = model.bind(
            root.parameters.as_deref().unwrap_or_default(),
            &plan.parameters,
        )?;
        builder.network(&root.tn, &plan.roots, &env, None, work)?;
    } else {
        if !plan.decompositions.is_empty() || !plan.parameters.is_empty() {
            return Err(Diagnostic::invalid(
                "unexpected_decomposition",
                "problem has no initial HTN; a decomposition or root binding is not applicable",
            ));
        }
        // Without hierarchy the certificate may have an empty root, or list its
        // primitive actions as roots. Execution and the goal still must hold.
        let roots = if plan.roots.is_empty() {
            &plan.actions
        } else {
            &plan.roots
        };
        for occurrence in roots {
            builder.introduce(occurrence)?;
        }
    }
    while let Some(occurrence) = builder.queue.pop_front() {
        work.tick();
        let check = (|| {
            let parameters = model
                .tasks
                .get(occurrence.call.name.as_str())
                .ok_or_else(|| {
                    Diagnostic::invalid(
                        "unknown_task",
                        format!("unknown task {}", occurrence.call.name),
                    )
                })?;
            model.bind(parameters, &occurrence.call.args)?;
            if model.actions.contains_key(occurrence.call.name.as_str()) {
                if plan.decompositions.contains_key(&occurrence.id) {
                    return Err(Diagnostic::invalid(
                        "primitive_decomposition",
                        "an action cannot have a decomposition",
                    ));
                }
                return Ok(());
            }
            let entry = plan.decompositions.get(&occurrence.id).ok_or_else(|| {
                Diagnostic::invalid(
                    "missing_decomposition",
                    "compound occurrence has no decomposition",
                )
            })?;
            if entry.task.call != occurrence.call {
                return Err(Diagnostic::invalid(
                    "decomposition_task",
                    "decomposition head differs from the introduced task",
                ));
            }
            let &i = model
                .methods
                .get(entry.method.name.as_str())
                .ok_or_else(|| {
                    Diagnostic::invalid(
                        "unknown_method",
                        format!("unknown method {}", entry.method.name),
                    )
                })?;
            let method = &model.domain.methods[i];
            let env = model.bind(&method.params, &entry.method.args)?;
            if model.call(method.task.name, &method.task_terms, &env)? != occurrence.call {
                return Err(Diagnostic::invalid(
                    "method_head",
                    "method does not decompose this task instance",
                ));
            }
            let pair = builder.endpoints[&occurrence.id];
            builder.events[pair.0].condition =
                model.condition(method.precondition.as_ref(), &env, work)?;
            builder.expanded.insert(occurrence.id.clone());
            builder.network(&method.tn, &entry.children, &env, Some(pair), work)
        })();
        check.map_err(|e| e.task(&occurrence.id).at(occurrence.location.clone()))?;
    }
    if builder.expanded.len() != plan.decompositions.len() {
        return Err(Diagnostic::invalid(
            "orphan_decomposition",
            "decomposition contains unreachable entries",
        ));
    }
    for occurrence in &plan.actions {
        if !builder.endpoints.contains_key(&occurrence.id) {
            return Err(Diagnostic::invalid(
                "orphan_action",
                "action is not produced by the hierarchy",
            )
            .task(&occurrence.id)
            .at(occurrence.location.clone()));
        }
    }
    let hierarchy = Order::new(builder.events.len(), builder.edges, work)?;
    for (a, first) in plan.actions.iter().enumerate() {
        for (b, second) in plan.actions.iter().enumerate() {
            work.tick();
            if hierarchy.before(a, b) && !order.before(a, b) {
                return Err(Diagnostic::invalid(
                    "missing_hierarchy_order",
                    format!(
                        "hierarchy requires {} < {}, but the submitted order does not imply it",
                        first.id, second.id
                    ),
                )
                .task(&second.id)
                .at(second.location.clone()));
            }
        }
    }
    Ok(Certificate {
        actions,
        order,
        hierarchy,
        events: builder.events,
    })
}
