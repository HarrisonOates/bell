// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

mod panda;
mod source;

use crate::{Diagnostic, Options, Status, work::Work};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
struct Call {
    name: String,
    args: Vec<String>,
}

impl Call {
    fn grounded(text: &str) -> Result<Self> {
        let text = text.to_ascii_lowercase();
        let (name, args) = match text.split_once('[') {
            Some((name, tail)) => {
                let args = tail
                    .strip_suffix(']')
                    .ok_or("unclosed grounded arguments")?;
                if args.contains(['[', ']']) {
                    return Err("malformed grounded arguments".into());
                }
                (
                    name,
                    if args.is_empty() {
                        vec![]
                    } else {
                        args.split(',').map(str::to_owned).collect()
                    },
                )
            }
            None => (text.as_str(), vec![]),
        };
        Ok(Self {
            name: name.into(),
            args,
        })
    }

    fn text(&self) -> String {
        format!(
            "({}{})",
            self.name,
            self.args
                .iter()
                .map(|a| format!(" {a}"))
                .collect::<String>()
        )
    }
}

#[derive(Clone)]
struct Node {
    call: Call,
    method: Option<String>,
    children: Vec<u64>,
    position: usize,
}

struct Tree {
    nodes: BTreeMap<u64, Node>,
    roots: Vec<u64>,
    actions: Vec<u64>,
    next_id: u64,
}

impl Tree {
    fn parse(text: &str, work: &mut Work) -> Result<Self> {
        fn id(word: &str) -> Result<u64> {
            word.parse::<u64>()
                .map_err(|_| "invalid PANDA occurrence ID".into())
        }
        fn call(words: &[&str]) -> Result<Call> {
            let first = words.first().ok_or("missing PANDA task")?;
            if first.starts_with('@') {
                return Err("scheduled PANDA output is unsupported".into());
            }
            if words.len() == 1 {
                Call::grounded(first)
            } else {
                if first.contains(['[', ']']) {
                    return Err("mixed grounded and source task arguments".into());
                }
                Ok(Call {
                    name: first.to_ascii_lowercase(),
                    args: words[1..].iter().map(|s| s.to_ascii_lowercase()).collect(),
                })
            }
        }
        let mut tree = Self {
            nodes: BTreeMap::new(),
            roots: vec![],
            actions: vec![],
            next_id: 0,
        };
        let mut started = false;
        let mut ended = false;
        let mut root_seen = false;
        for line in text.lines().map(str::trim) {
            work.tick();
            if line == "==>" {
                if started {
                    return Err("multiple PANDA plan blocks".into());
                }
                started = true;
                continue;
            }
            if line == "<==" {
                if !started || ended {
                    return Err("unexpected PANDA end marker".into());
                }
                ended = true;
                continue;
            }
            if !started || ended || line.is_empty() {
                continue;
            }
            let words: Vec<_> = line.split_whitespace().collect();
            if words[0] == "root" {
                if root_seen {
                    return Err("duplicate PANDA root line".into());
                }
                root_seen = true;
                tree.roots = words[1..].iter().map(|w| id(w)).collect::<Result<_>>()?;
                continue;
            }
            let occurrence = id(words[0])?;
            let (call, method, children) =
                if let Some(arrow) = words.iter().position(|w| *w == "->") {
                    if !root_seen {
                        return Err("PANDA decomposition precedes roots".into());
                    }
                    let method = words.get(arrow + 1).ok_or("missing PANDA method")?;
                    let method = method
                        .strip_suffix("[]")
                        .unwrap_or(method)
                        .to_ascii_lowercase();
                    let children = words[arrow + 2..]
                        .iter()
                        .map(|w| id(w))
                        .collect::<Result<_>>()?;
                    (call(&words[1..arrow])?, Some(method), children)
                } else {
                    if root_seen {
                        return Err("PANDA action follows roots".into());
                    }
                    tree.actions.push(occurrence);
                    (call(&words[1..])?, None, vec![])
                };
            if tree
                .nodes
                .insert(
                    occurrence,
                    Node {
                        call,
                        method,
                        children,
                        position: 0,
                    },
                )
                .is_some()
            {
                return Err("duplicate PANDA occurrence ID".into());
            }
            tree.next_id = tree
                .next_id
                .max(occurrence.checked_add(1).ok_or("PANDA ID overflow")?);
        }
        if !started || !ended || !root_seen {
            return Err("incomplete PANDA plan block (expected ==>, root, and <==)".into());
        }
        tree.traversal(work)?;
        Ok(tree)
    }

    fn allocate(&mut self) -> Result<u64> {
        let id = self.next_id;
        self.next_id = id.checked_add(1).ok_or("PANDA ID overflow")?;
        Ok(id)
    }

    fn traversal(&self, work: &mut Work) -> Result<Vec<u64>> {
        let mut pending = self.roots.clone();
        let mut seen = BTreeSet::new();
        let mut order = vec![];
        while let Some(id) = pending.pop() {
            work.tick();
            if !seen.insert(id) {
                return Err("shared or cyclic solution occurrence".into());
            }
            let node = self.nodes.get(&id).ok_or("missing solution occurrence")?;
            pending.extend(&node.children);
            order.push(id);
        }
        if seen.len() != self.nodes.len() {
            return Err("unreachable solution occurrence".into());
        }
        Ok(order)
    }

    fn positions(&mut self, work: &mut Work) -> Result<()> {
        let positions: BTreeMap<_, _> = self
            .actions
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, i))
            .collect();
        for id in self.traversal(work)?.into_iter().rev() {
            let node = &self.nodes[&id];
            let position = positions.get(&id).copied().unwrap_or_else(|| {
                node.children
                    .iter()
                    .map(|c| self.nodes[c].position)
                    .min()
                    .unwrap_or(usize::MAX)
            });
            self.nodes.get_mut(&id).unwrap().position = position;
        }
        Ok(())
    }

    fn splice(&mut self, id: u64, replacement: &[u64], work: &mut Work) -> Result<()> {
        fn replace(ids: &mut Vec<u64>, id: u64, replacement: &[u64]) {
            if let Some(index) = ids.iter().position(|&old| old == id) {
                ids.splice(index..=index, replacement.iter().copied());
            }
        }
        replace(&mut self.roots, id, replacement);
        replace(&mut self.actions, id, replacement);
        for node in self.nodes.values_mut() {
            work.tick();
            replace(&mut node.children, id, replacement);
        }
        self.nodes.remove(&id);
        Ok(())
    }

    fn tasks(&self, ids: &[u64]) -> String {
        if ids.is_empty() {
            return "()".into();
        }
        let entries: Vec<_> = ids
            .iter()
            .map(|id| format!("(n{id} {})", self.nodes[id].call.text()))
            .collect();
        format!("(and {})", entries.join(" "))
    }
}

#[derive(Deserialize)]
struct Reconstruction {
    version: u32,
    domain: String,
    problem: String,
    tasks: BTreeMap<String, TaskSource>,
    methods: BTreeMap<String, MethodSource>,
}

#[derive(Deserialize)]
struct TaskSource {
    name: Option<String>,
    arity: usize,
    primitive: bool,
}

#[derive(Deserialize)]
struct MethodSource {
    name: Option<String>,
    children: Vec<usize>,
    body_len: usize,
}

impl Reconstruction {
    fn parse(text: &str) -> Result<Self> {
        let map: Self = serde_json::from_str(text).map_err(|e| format!("source map: {e}"))?;
        if map.version != 1 {
            return Err("unsupported source map version".into());
        }
        Ok(map)
    }

    fn restore(&self, tree: &mut Tree, work: &mut Work) -> Result<()> {
        tree.positions(work)?;
        let mut replacements: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
        let mut retained = BTreeMap::new();
        for id in tree.traversal(work)?.into_iter().rev() {
            let node = &tree.nodes[&id];
            if node.call.name == "__noop" {
                if node.method.is_some() || !node.call.args.is_empty() {
                    return Err("malformed source-map noop".into());
                }
                replacements.insert(id, vec![]);
                continue;
            }
            let task = self
                .tasks
                .get(&node.call.name)
                .ok_or("task absent from source map")?;
            if task.arity != node.call.args.len() || task.primitive != node.method.is_none() {
                return Err("source-map task arity/kind mismatch".into());
            }
            let mut children = vec![];
            let method = if let Some(method) = &node.method {
                let source = self
                    .methods
                    .get(method)
                    .ok_or("method absent from source map")?;
                if node.children.len() != source.body_len.max(1) {
                    return Err("source-map method body length mismatch".into());
                }
                for &slot in &source.children {
                    let child = node
                        .children
                        .get(slot)
                        .ok_or("invalid source-map child slot")?;
                    children.extend_from_slice(&replacements[child]);
                }
                source.name.clone()
            } else {
                None
            };
            if let Some(name) = &task.name {
                if node.method.is_some() && method.is_none() {
                    return Err("source task uses artificial method".into());
                }
                retained.insert(
                    id,
                    Node {
                        call: Call {
                            name: name.clone(),
                            args: node.call.args.clone(),
                        },
                        method,
                        children,
                        position: node.position,
                    },
                );
                replacements.insert(id, vec![id]);
            } else {
                replacements.insert(id, children);
            }
        }
        tree.roots = tree
            .roots
            .iter()
            .flat_map(|id| replacements[id].iter().copied())
            .collect();
        tree.actions.retain(|id| retained.contains_key(id));
        tree.nodes = retained;
        Ok(())
    }
}

/// A reconstructed candidate; callers must validate it against the source inputs.
pub struct AdaptedPlan {
    pub text: String,
    pub work: u64,
}

/// Recover an HDDL 1.1 certificate from raw PANDA-format planner output.
/// This adapter constructs a witness; it does not replace independent validation.
pub fn from_panda(
    domain: &str,
    problem: &str,
    plan: &str,
    source_map: Option<&str>,
    options: &Options,
) -> std::result::Result<AdaptedPlan, Diagnostic> {
    for text in [Some(domain), Some(problem), Some(plan), source_map]
        .into_iter()
        .flatten()
    {
        if text.len() > options.max_input_bytes {
            return Err(Diagnostic::new(
                Status::LimitExceeded,
                "input_size",
                "adapter input exceeds the size limit",
            ));
        }
    }
    let mut work = Work::default();
    let result = (|| {
        let reconstruction = source_map.map(Reconstruction::parse).transpose()?;
        if let Some(map) = &reconstruction
            && (!map.domain.eq_ignore_ascii_case(domain)
                || !map.problem.eq_ignore_ascii_case(problem))
        {
            return Err("source map does not match the supplied domain/problem".into());
        }
        reconstruct(domain, problem, plan, reconstruction.as_ref(), &mut work)
    })();
    match result {
        Ok(text) => Ok(AdaptedPlan {
            text,
            work: work.used,
        }),
        Err(message) => Err(Diagnostic::input("panda_adapter", message)),
    }
}

fn reconstruct(
    domain: &str,
    problem: &str,
    plan: &str,
    reconstruction: Option<&Reconstruction>,
    work: &mut Work,
) -> Result<String> {
    let source = source::Source::parse(domain, problem, work)?;
    let mut tree = Tree::parse(plan, work)?;
    if let Some(map) = reconstruction {
        map.restore(&mut tree, work)?;
    } else {
        panda::restore(&mut tree, work)?;
    }
    tree.traversal(work)?;
    let (root_arguments, methods) = source.bind(&tree, work)?;
    let mut text = source.header();
    writeln!(
        text,
        "  (:decomposition\n    (:root :parameters ({})\n      :subtasks {})",
        root_arguments.join(" "),
        tree.tasks(&tree.roots)
    )
    .unwrap();
    for (id, method) in methods {
        let node = &tree.nodes[&id];
        writeln!(
            text,
            "    (n{id} {}\n      :method {}\n      :subtasks {})",
            node.call.text(),
            method.text(),
            tree.tasks(&node.children)
        )
        .unwrap();
    }
    writeln!(
        text,
        "  )\n  (:htn :ordered-tasks {})\n)",
        tree.tasks(&tree.actions)
    )
    .unwrap();
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DOMAIN: &str = "(define (domain d) (:types item) (:predicates (ready ?x - item))
      (:task root :parameters (?x - item)) (:task empty :parameters ())
      (:method m :parameters (?w ?x - item) :task (root ?x) :precondition (ready ?w)
        :ordered-subtasks (and (a ?x) (empty) (a ?x)))
      (:method nothing :parameters () :task (empty) :subtasks ())
      (:action a :parameters (?x - item) :effect ()))";
    const PROBLEM: &str = "(define (problem p) (:domain d) (:objects a b - item)
      (:htn :parameters (?r - item) :subtasks (root ?r)) (:init (ready b)))";

    fn tree() -> Tree {
        let entries = [
            (
                0,
                "__top[]",
                Some("<__top_method;root[a];m;0;-1,-2,-3,-4>"),
                vec![1, 2, 3, 4],
            ),
            (1, "__method_precondition_m[b]", None, vec![]),
            (2, "a[a]", None, vec![]),
            (3, "empty[]", Some("nothing"), vec![5]),
            (4, "a[a]", None, vec![]),
            (5, "__noop", None, vec![]),
        ];
        Tree {
            nodes: entries
                .into_iter()
                .map(|(id, call, method, children)| {
                    (
                        id,
                        Node {
                            call: Call::grounded(call).unwrap(),
                            method: method.map(str::to_owned),
                            children,
                            position: 0,
                        },
                    )
                })
                .collect(),
            roots: vec![0],
            actions: vec![1, 2, 5, 4],
            next_id: 6,
        }
    }

    #[test]
    fn compressed_hierarchy_repeated_actions_and_empty_method_keep_identity() {
        let mut tree = tree();
        let mut work = Work::default();
        panda::restore(&mut tree, &mut work).unwrap();
        assert_eq!(tree.roots, [6]);
        assert_eq!(tree.actions, [2, 4]);
        assert_eq!(tree.nodes[&6].children, [2, 3, 4]);
        assert!(tree.nodes[&3].children.is_empty());
        let source = source::Source::parse(DOMAIN, PROBLEM, &mut work).unwrap();
        let (root, methods) = source.bind(&tree, &mut work).unwrap();
        assert_eq!(root, ["a"]);
        assert_eq!(methods[&6].args, ["b", "a"]);
        assert!(methods[&3].args.is_empty());
    }

    #[test]
    fn binding_uses_state_at_the_guard_and_not_initial_state() {
        let domain = DOMAIN.replace(
            "(:action a",
            "(:action enable :parameters (?x - item) :effect (ready ?x)) (:action a",
        );
        let problem = PROBLEM
            .replace(
                ":subtasks (root ?r)",
                ":ordered-subtasks (and (enable b) (root ?r))",
            )
            .replace("(:init (ready b))", "(:init)");
        let mut tree = tree();
        tree.nodes.insert(
            8,
            Node {
                call: Call::grounded("enable[b]").unwrap(),
                method: None,
                children: vec![],
                position: 0,
            },
        );
        tree.next_id = 9;
        tree.roots.insert(0, 8);
        tree.actions.insert(0, 8);
        let mut work = Work::default();
        panda::restore(&mut tree, &mut work).unwrap();
        let (_, methods) = source::Source::parse(&domain, &problem, &mut work)
            .unwrap()
            .bind(&tree, &mut work)
            .unwrap();
        assert_eq!(methods[&9].args, ["b", "a"]);
    }

    #[test]
    fn inlined_empty_methods_do_not_move_guards_to_the_initial_state() {
        let mut tree = tree();
        tree.nodes.get_mut(&3).unwrap().children.clear();
        tree.nodes.remove(&5);
        tree.actions.retain(|&id| id != 5);
        tree.actions.insert(0, 8);
        tree.roots.insert(0, 8);
        tree.nodes.insert(
            8,
            Node {
                call: Call::grounded("enable[b]").unwrap(),
                method: None,
                children: vec![],
                position: 0,
            },
        );
        tree.next_id = 9;
        let domain = DOMAIN.replace(
            "(:action a",
            "(:action enable :parameters (?x - item) :effect (ready ?x)) (:action a",
        );
        let problem = PROBLEM
            .replace(
                ":subtasks (root ?r)",
                ":ordered-subtasks (and (enable b) (root ?r))",
            )
            .replace("(:init (ready b))", "(:init)");
        let mut work = Work::default();
        panda::restore(&mut tree, &mut work).unwrap();
        assert_eq!(tree.nodes[&9].position, 1);
        let (_, methods) = source::Source::parse(&domain, &problem, &mut work)
            .unwrap()
            .bind(&tree, &mut work)
            .unwrap();
        assert_eq!(methods[&9].args, ["b", "a"]);
    }

    #[test]
    fn reconstruction_continues_past_the_former_cutoff_and_checks_false_guards() {
        let mut tree = tree();
        let mut work = Work::default();
        work.charge(10_000_000);
        panda::restore(&mut tree, &mut work).unwrap();
        let problem = PROBLEM.replace("(ready b)", "");
        assert!(
            source::Source::parse(DOMAIN, &problem, &mut work)
                .unwrap()
                .bind(&tree, &mut work)
                .is_err()
        );
        assert!(work.used > 10_000_000);
    }

    #[test]
    fn malformed_compression_is_rejected() {
        for method in ["<bad>", "<m;root[a];m;0;-1>", "<m;root[a];m;0;0,-1,-2,-3>"] {
            let mut tree = tree();
            tree.nodes.get_mut(&0).unwrap().method = Some(method.into());
            assert!(panda::restore(&mut tree, &mut Work::default()).is_err());
        }
    }

    #[test]
    fn source_map_restores_declaration_order_and_keeps_guard_position() {
        let map = serde_json::json!({"version":1, "domain":DOMAIN, "problem":PROBLEM,
            "tasks":{"mf_root":{"name":"root", "arity":1,"primitive":false},
                     "mf_a":{"name":"a", "arity":1,"primitive":true},
                     "mf_empty":{"name":"empty", "arity":0,"primitive":false},
                     "__method_precondition_m":{"name":null,"arity":1,"primitive":true}},
            "methods":{"mf_m":{"name":"m","body_len":4,"children":[2,1,3]},
                       "mf_nothing":{"name":"nothing","body_len":0,"children":[]}}});
        let mut tree = tree();
        tree.nodes.get_mut(&0).unwrap().call = Call::grounded("mf_root[a]").unwrap();
        tree.nodes.get_mut(&0).unwrap().method = Some("mf_m".into());
        tree.nodes.get_mut(&0).unwrap().children = vec![1, 3, 2, 4];
        for id in [2, 4] {
            tree.nodes.get_mut(&id).unwrap().call.name = "mf_a".into();
        }
        tree.nodes.get_mut(&3).unwrap().call.name = "mf_empty".into();
        tree.nodes.get_mut(&3).unwrap().method = Some("mf_nothing".into());
        let map = Reconstruction::parse(&map.to_string()).unwrap();
        map.restore(&mut tree, &mut Work::default()).unwrap();
        assert_eq!(tree.nodes[&0].children, [2, 3, 4]);
        assert_eq!(tree.actions, [2, 4]);
        let (_, methods) = source::Source::parse(DOMAIN, PROBLEM, &mut Work::default())
            .unwrap()
            .bind(&tree, &mut Work::default())
            .unwrap();
        assert_eq!(methods[&0].args, ["b", "a"]);
    }
}
