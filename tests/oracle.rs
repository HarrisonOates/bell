use bell::{Options, Profile, Status, validate};

fn permutations(values: &[usize]) -> Vec<Vec<usize>> {
    if values.is_empty() {
        return vec![vec![]];
    }
    let mut output = vec![];
    for &first in values {
        let tail: Vec<_> = values.iter().copied().filter(|&x| x != first).collect();
        for mut p in permutations(&tail) {
            p.insert(0, first);
            output.push(p);
        }
    }
    output
}
fn obeys(order: &[usize], edges: &[(usize, usize)]) -> bool {
    edges.iter().all(|(a, b)| {
        order.iter().position(|x| x == a).unwrap() < order.iter().position(|x| x == b).unwrap()
    })
}
fn formula(kind: usize) -> &'static str {
    match kind {
        0 => "()",
        1 => "(p)",
        _ => "(not (p))",
    }
}
fn holds(kind: usize, state: bool) -> bool {
    match kind {
        0 => true,
        1 => state,
        _ => !state,
    }
}
fn digits(mut n: usize) -> [usize; 3] {
    let mut d = [0; 3];
    for v in &mut d {
        *v = n % 3;
        n /= 3;
    }
    d
}
fn conjunction(items: Vec<String>) -> String {
    if items.is_empty() {
        "()".into()
    } else {
        format!("(and {})", items.join(" "))
    }
}
fn ordering(edges: &[(usize, usize)], names: &[&str]) -> String {
    conjunction(
        edges
            .iter()
            .map(|&(a, b)| format!("(< {} {})", names[a], names[b]))
            .collect(),
    )
}

#[test]
fn mtc_matches_exhaustive_execution_for_all_three_action_single_fact_cases() {
    let options = Options {
        profile: Profile::Hddl11,
        ..Options::default()
    };
    let permutations = permutations(&[0, 1, 2]);
    let pairs = [(0, 1), (0, 2), (1, 2)];
    let mut cases = 0;
    for mask in 0..8 {
        let edges: Vec<_> = pairs
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, e)| *e)
            .collect();
        let orders: Vec<_> = permutations.iter().filter(|p| obeys(p, &edges)).collect();
        let plan = format!(
            "(define (plan s) (:domain d) (:problem p) (:decomposition (:root :subtasks ())) (:htn :tasks (and (a (a)) (b (b)) (c (c))) :ordering {}))",
            ordering(&edges, &["a", "b", "c"])
        );
        for pre in 0..27 {
            let pre = digits(pre);
            for effects in 0..27 {
                let effects = digits(effects);
                let actions: [String; 3] = std::array::from_fn(|i| {
                    format!(
                        "(:action {} :parameters () :precondition {} :effect {})",
                        ["a", "b", "c"][i],
                        formula(pre[i]),
                        formula(effects[i])
                    )
                });
                let domain = format!(
                    "(define (domain d) (:predicates (p)) {})",
                    actions.join(" ")
                );
                for initial in [false, true] {
                    for goal in 0..3 {
                        let problem = format!(
                            "(define (problem p) (:domain d) (:init {}) (:goal {}))",
                            if initial { "(p)" } else { "" },
                            formula(goal)
                        );
                        let valid = orders.iter().all(|order| {
                            let mut state = initial;
                            for &i in order.iter() {
                                if !holds(pre[i], state) {
                                    return false;
                                }
                                if effects[i] != 0 {
                                    state = effects[i] == 1;
                                }
                            }
                            holds(goal, state)
                        });
                        let report = validate(&domain, &problem, &plan, &options);
                        assert_eq!(
                            report.status,
                            if valid {
                                Status::Valid
                            } else {
                                Status::InvalidPlan
                            },
                            "edges={edges:?} pre={pre:?} effects={effects:?} init={initial} goal={goal}: {report:?}"
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 34992);
}

#[test]
fn method_checks_match_explicit_guard_insertion() {
    let options = Options {
        profile: Profile::Hddl11,
        ..Options::default()
    };
    let permutations = permutations(&[0, 1, 2]);
    let pairs = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)];
    let dags: Vec<Vec<_>> = (0..64)
        .map(|mask| {
            pairs
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, e)| *e)
                .collect::<Vec<_>>()
        })
        .filter(|edges| permutations.iter().any(|p| obeys(p, edges)))
        .collect();
    assert_eq!(dags.len(), 25);
    for hierarchy in &dags {
        // Root task 0 expands to action 0, with invisible guard event 3.
        let mut required: Vec<_> = hierarchy
            .iter()
            .map(|&(a, b)| (a, if b == 0 { 3 } else { b }))
            .collect();
        required.push((3, 0));
        for edges in &dags {
            let orders: Vec<_> = permutations.iter().filter(|p| obeys(p, edges)).collect();
            for initial in [false, true] {
                for guard in [1, 2] {
                    let valid = orders.iter().all(|actions| {
                        (0..=3).any(|slot| {
                            let mut full = (*actions).clone();
                            full.insert(slot, 3);
                            if !obeys(&full, &required) {
                                return false;
                            }
                            let mut state = initial;
                            for i in full {
                                match i {
                                    1 => state = true,
                                    2 => state = false,
                                    3 if !holds(guard, state) => return false,
                                    _ => (),
                                }
                            }
                            true
                        })
                    });
                    let domain = format!(
                        "(define (domain d) (:predicates (p)) (:task task :parameters ()) (:method method :parameters () :task (task) :precondition {} :subtasks (leaf)) (:action leaf :parameters ()) (:action set :parameters () :effect (p)) (:action clear :parameters () :effect (not (p))))",
                        formula(guard)
                    );
                    let problem = format!(
                        "(define (problem p) (:domain d) (:htn :subtasks (and (t (task)) (s (set)) (d (clear))) :ordering {}) (:init {}))",
                        ordering(hierarchy, &["t", "s", "d"]),
                        if initial { "(p)" } else { "" }
                    );
                    let plan = format!(
                        "(define (plan s) (:domain d) (:problem p) (:decomposition (:root :subtasks (and (t (task)) (s (set)) (d (clear)))) (t (task) :method (method) :subtasks (l (leaf)))) (:htn :tasks (and (l (leaf)) (s (set)) (d (clear))) :ordering {}))",
                        ordering(edges, &["l", "s", "d"])
                    );
                    let report = validate(&domain, &problem, &plan, &options);
                    assert_eq!(
                        report.status,
                        if valid {
                            Status::Valid
                        } else {
                            Status::InvalidPlan
                        },
                        "hierarchy={hierarchy:?}, order={edges:?}, init={initial}, guard={guard}: {report:?}"
                    );
                }
            }
        }
    }
}
