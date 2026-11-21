// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

use crate::{
    input::Node,
    report::{Diagnostic, Location, Result},
};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Call {
    pub name: String,
    pub args: Vec<String>,
}
#[derive(Clone, Debug)]
pub(crate) struct Occurrence {
    pub id: String,
    pub call: Call,
    pub location: Location,
}
#[derive(Debug)]
pub(crate) struct Decomposition {
    pub task: Occurrence,
    pub method: Call,
    pub children: Vec<Occurrence>,
}
#[derive(Debug)]
pub(crate) struct Plan {
    pub domain: String,
    pub problem: String,
    pub unsolvable: bool,
    pub roots: Vec<Occurrence>,
    pub parameters: Vec<String>,
    pub decompositions: BTreeMap<String, Decomposition>,
    pub actions: Vec<Occurrence>,
    pub edges: Vec<(String, String)>,
}

fn call(node: &Node) -> Result<Call> {
    let items = node.list()?;
    let name = items
        .first()
        .ok_or_else(|| node.error("empty task or method call"))?
        .name()?;
    let args = items[1..].iter().map(Node::name).collect::<Result<_>>()?;
    Ok(Call { name, args })
}
fn occurrence(node: &Node) -> Result<Occurrence> {
    let items = node.list()?;
    if items.len() != 2 {
        return Err(node.error("expected (occurrence-id (task arguments...))"));
    }
    Ok(Occurrence {
        id: items[0].name()?,
        call: call(&items[1])?,
        location: node.location.clone(),
    })
}
fn conjunction(node: &Node) -> Result<Vec<&Node>> {
    let items = node.list()?;
    if items.is_empty() {
        Ok(vec![])
    } else if node.head() == "and" {
        if items.len() == 1 {
            return Err(node.error("use () for an empty task or ordering list"));
        }
        Ok(items[1..].iter().collect())
    } else {
        Ok(vec![node])
    }
}
fn occurrences(node: &Node) -> Result<Vec<Occurrence>> {
    conjunction(node)?.into_iter().map(occurrence).collect()
}
fn fields<'a>(nodes: &'a [Node], allowed: &[&str]) -> Result<BTreeMap<&'a str, &'a Node>> {
    let mut fields = BTreeMap::new();
    for pair in nodes.chunks(2) {
        let key = pair[0].atom()?;
        if pair.len() != 2 || !allowed.contains(&key) {
            return Err(pair[0].error(format!("unexpected or incomplete field {key}")));
        }
        if fields.insert(key, &pair[1]).is_some() {
            return Err(pair[0].error(format!("duplicate field {key}")));
        }
    }
    Ok(fields)
}
fn required<'a>(map: &BTreeMap<&str, &'a Node>, key: &str, node: &Node) -> Result<&'a Node> {
    map.get(key)
        .copied()
        .ok_or_else(|| node.error(format!("missing {key}")))
}

impl Plan {
    pub fn parse(node: &Node) -> Result<Self> {
        let items = node.list()?;
        if node.head() != "define" || items.len() < 5 {
            return Err(node.error("expected an IPC (define (plan name) ...) certificate"));
        }
        let header = items[1].list()?;
        if header.len() != 2 || items[1].head() != "plan" {
            return Err(items[1].error("expected (plan name)"));
        }
        header[1].name()?;
        let mut blocks = BTreeMap::new();
        for block in &items[2..] {
            if !matches!(
                block.head(),
                ":domain" | ":problem" | ":decomposition" | ":htn" | ":unsolvable"
            ) {
                return Err(block.error("unknown plan block"));
            }
            if blocks.insert(block.head(), block).is_some() {
                return Err(block.error(format!("duplicate {} block", block.head())));
            }
        }
        let named = |key: &str| -> Result<String> {
            let b = required(&blocks, key, node)?;
            if b.children.len() != 2 {
                return Err(b.error(format!("expected ({key} name)")));
            }
            b.children[1].name()
        };
        let mut plan = Self {
            domain: named(":domain")?,
            problem: named(":problem")?,
            unsolvable: false,
            roots: vec![],
            parameters: vec![],
            decompositions: BTreeMap::new(),
            actions: vec![],
            edges: vec![],
        };
        if let Some(unsolvable) = blocks.get(":unsolvable") {
            if unsolvable.children.len() != 1
                || blocks.contains_key(":decomposition")
                || blocks.contains_key(":htn")
            {
                return Err(unsolvable.error(":unsolvable must appear without solution blocks"));
            }
            plan.unsolvable = true;
            return Ok(plan);
        }
        let decomposition = required(&blocks, ":decomposition", node)?;
        let entries = &decomposition.children[1..];
        let root = entries
            .first()
            .ok_or_else(|| decomposition.error("missing :root"))?;
        if root.head() != ":root" {
            return Err(root.error("decomposition must begin with :root"));
        }
        let root_fields = fields(&root.children[1..], &[":parameters", ":subtasks"])?;
        if let Some(parameters) = root_fields.get(":parameters") {
            plan.parameters = parameters
                .list()?
                .iter()
                .map(Node::name)
                .collect::<Result<_>>()?;
        }
        plan.roots = occurrences(required(&root_fields, ":subtasks", root)?)?;
        for entry in &entries[1..] {
            let parts = entry.list()?;
            if parts.len() < 2 {
                return Err(entry.error("incomplete decomposition"));
            }
            let task = Occurrence {
                id: parts[0].name()?,
                call: call(&parts[1])?,
                location: entry.location.clone(),
            };
            let f = fields(&parts[2..], &[":method", ":subtasks"])?;
            let method = call(required(&f, ":method", entry)?)?;
            let children = occurrences(required(&f, ":subtasks", entry)?)?;
            let id = task.id.clone();
            if plan
                .decompositions
                .insert(
                    id.clone(),
                    Decomposition {
                        task,
                        method,
                        children,
                    },
                )
                .is_some()
            {
                return Err(Diagnostic::invalid(
                    "duplicate_decomposition",
                    "task has more than one decomposition",
                )
                .task(&id)
                .at(entry.location.clone()));
            }
        }
        let htn = required(&blocks, ":htn", node)?;
        let f = fields(
            &htn.children[1..],
            &[":ordered-tasks", ":tasks", ":ordering"],
        )?;
        match (f.get(":ordered-tasks"), f.get(":tasks")) {
            (Some(tasks), None) if !f.contains_key(":ordering") => {
                plan.actions = occurrences(tasks)?;
                plan.edges = plan
                    .actions
                    .windows(2)
                    .map(|w| (w[0].id.clone(), w[1].id.clone()))
                    .collect();
            }
            (None, Some(tasks)) => {
                plan.actions = occurrences(tasks)?;
                if let Some(ordering) = f.get(":ordering") {
                    for edge in conjunction(ordering)? {
                        let e = edge.list()?;
                        if edge.head() != "<" || e.len() < 3 {
                            return Err(edge.error("expected (< predecessor successor...)"));
                        }
                        let before = e[1].name()?;
                        for after in &e[2..] {
                            plan.edges.push((before.clone(), after.name()?));
                        }
                    }
                }
                if plan.actions.is_empty() {
                    return Err(tasks.error("write an empty plan as :ordered-tasks ()"));
                }
            }
            _ => return Err(htn.error("expected :ordered-tasks or :tasks with optional :ordering")),
        }
        Ok(plan)
    }
}
