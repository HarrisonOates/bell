// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

use bell::{Options, Profile, Report, Status, validate};

fn options() -> Options {
    Options {
        profile: Profile::Hddl11,
        ..Options::default()
    }
}

fn plan(actions: &str, order: &str) -> String {
    if actions == "()" {
        return "(define (plan s) (:domain d) (:problem p)
          (:decomposition (:root :subtasks ())) (:htn :ordered-tasks ()))"
            .into();
    }
    format!(
        "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks ()))
      (:htn :tasks {actions} :ordering {order}))"
    )
}

fn check(d: &str, p: &str, s: &str, expected: Status) -> Report {
    let report = validate(d, p, s, &options());
    assert_eq!(report.status, expected, "{report:#?}\n{d}\n{p}\n{s}");
    report
}

#[test]
fn different_orders_can_satisfy_different_disjuncts() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:action a :parameters () :effect (and (p) (not (q))))
      (:action b :parameters () :effect (and (q) (not (p))))
      (:action use :parameters () :precondition (or (p) (q))))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (or (p) (q))))";
    let s = plan("(and (a (a)) (b (b)) (u (use)))", "(and (< a u) (< b u))");
    check(d, p, &s, Status::Valid);
    // Neither disjunct is guaranteed by itself, and the two possible states
    // after executing {a,b} must not be merged just because the done set agrees.
    for goal in ["(p)", "(q)"] {
        let r = check(d, &p.replace("(or (p) (q))", goal), &s, Status::InvalidPlan);
        assert_eq!(r.diagnostics[0].code, "goal");
        assert_eq!(r.diagnostics[0].counterexample.len(), 3);
        assert_eq!(r.diagnostics[0].location.as_ref().unwrap().file, "problem");
    }
    let r = check(
        d,
        p,
        &s.replace("(and (< a u) (< b u))", "()"),
        Status::InvalidPlan,
    );
    assert_eq!(r.diagnostics[0].code, "action_precondition");
    assert_eq!(r.diagnostics[0].counterexample.last().unwrap(), "u");
}

#[test]
fn formula_mtc_proves_a_wide_disjunctive_network_symbolically() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:action left :parameters () :effect (and (p) (not (q))))
      (:action right :parameters () :effect (and (q) (not (p))))
      (:action use :parameters () :precondition (or (p) (q))))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (or (p) (q))))";
    let mut actions: Vec<_> = (0..32)
        .map(|i| format!("(a{i} ({}))", if i % 2 == 0 { "left" } else { "right" }))
        .collect();
    actions.push("(u (use))".into());
    let edges = (0..32).map(|i| format!("(< a{i} u)")).collect::<Vec<_>>();
    let s = plan(
        &format!("(and {})", actions.join(" ")),
        &format!("(and {})", edges.join(" ")),
    );
    // 32! permitted executions, with neither p nor q necessarily true at use.
    let r = validate(d, p, &s, &options());
    assert_eq!(r.status, Status::Valid, "{r:#?}");
    // A performance assertion on the completed check, not a search cutoff.
    assert!(r.work < 200_000, "{r:#?}");
    assert_eq!(r.metrics.unwrap().makespan, 2);
}

#[test]
fn symbolic_reachability_proves_conditional_support_without_serializing_metrics() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:action toggle :parameters () :effect
        (and (when (p) (and (not (p)) (q))) (when (not (p)) (p))))
      (:action noop :parameters ()))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (q)))";
    let mut actions = vec!["(a (toggle))".into(), "(b (toggle))".into()];
    actions.extend((0..24).map(|i| format!("(n{i} (noop))")));
    let s = plan(&format!("(and {})", actions.join(" ")), "()");
    // The second toggle establishes q, but neither toggle is necessarily the
    // second one. Reachability merges equivalent prefixes of the 26! orders.
    let r = validate(d, p, &s, &options());
    assert_eq!(r.status, Status::Valid, "{r:#?}");
    // Bound the symbolic computation, without requiring the old split-based
    // algorithm's work count or imposing a validator cutoff.
    assert!(r.work < 5_000_000, "{r:#?}");
    assert_eq!(r.metrics.unwrap().makespan, 1);
}

#[test]
fn complementary_guards_establish_support_and_circular_support_does_not() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:action set :parameters () :effect (p))
      (:action clear :parameters () :effect (not (p)))
      (:action fire :parameters () :effect (and (when (p) (q)) (when (not (p)) (q)))))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (q)))";
    check(
        d,
        p,
        &plan("(and (s (set)) (c (clear)) (f (fire)))", "()"),
        Status::Valid,
    );
    let d = "(define (domain d) (:predicates (p) (q))
      (:action a :parameters () :precondition (p) :effect (when (p) (q)))
      (:action b :parameters () :precondition (q) :effect (when (q) (p))))";
    let r = check(
        d,
        p,
        &plan("(and (a (a)) (b (b)))", "()"),
        Status::InvalidPlan,
    );
    assert_eq!(r.diagnostics[0].code, "action_precondition");
}

#[test]
fn conditional_effects_depend_on_the_action_order() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:action set :parameters () :effect (p))
      (:action fire :parameters () :effect (when (p) (q))))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (q)))";
    let actions = "(and (s (set)) (f (fire)))";
    check(d, p, &plan(actions, "(< s f)"), Status::Valid);
    let r = check(d, p, &plan(actions, "()"), Status::InvalidPlan);
    assert_eq!(r.diagnostics[0].counterexample, ["f", "s"]);
    check(
        d,
        &p.replace("(:goal (q))", "(:goal (not (q)))"),
        &plan("(f (fire))", "()"),
        Status::Valid,
    );
}

#[test]
fn guards_read_the_pre_action_state_and_writes_are_simultaneous() {
    for (initial, effect, goal) in [
        ("", "(and (p) (when (p) (q)))", "(and (p) (not (q)))"),
        (
            "(p)",
            "(and (not (p)) (when (p) (q)))",
            "(and (not (p)) (q))",
        ),
        (
            "(p)",
            "(and (when (p) (q)) (when (q) (r)))",
            "(and (q) (not (r)))",
        ),
        (
            "(p)",
            "(and (when (q) (r)) (when (p) (q)))",
            "(and (q) (not (r)))",
        ),
        ("(p)", "(and (when (p) (q)) (when (p) (not (q))))", "(q)"),
        ("(p)", "(and (when (p) (not (q))) (q))", "(q)"),
        ("(p)", "(and (not (q)) (when (p) (q)))", "(q)"),
        ("(q)", "(and (not (q)) (when (p) (q)))", "(not (q))"),
        (
            "(p)",
            "(when (or (q) (not (r))) (and (q) (not (p))))",
            "(and (q) (not (p)))",
        ),
        ("", "(when (or) (q))", "(not (q))"),
        ("", "(when (and) (q))", "(q)"),
        ("", "(when (not (q)) (and))", "(not (q))"),
    ] {
        let d = format!(
            "(define (domain d) (:predicates (p) (q) (r))
          (:action a :parameters () :effect {effect}))"
        );
        let p = format!("(define (problem p) (:domain d) (:init {initial}) (:goal {goal}))");
        check(&d, &p, &plan("(a (a))", "()"), Status::Valid);
    }
}

#[test]
fn boolean_conditions_normalize_without_choosing_a_witness() {
    let d = "(define (domain d) (:constants a b) (:predicates (p) (q)))";
    for (formula, valid) in [
        ("(or)", false),
        ("(and)", true),
        ("(not (and))", false),
        ("(not (or))", true),
        ("(or () (q))", true),
        ("(and () (q))", false),
        ("(not ())", false),
        ("(or (p) (q))", true),
        ("(not (and (p) (q)))", true),
        ("(not (or (not (p)) (q)))", true),
        ("(imply (p) (q))", false),
        ("(imply (q) (p))", true),
        ("(not (imply (p) (q)))", true),
        ("(or (= a b) (p))", true),
        ("(not (or (= a a) (q)))", false),
    ] {
        let p = format!("(define (problem p) (:domain d) (:init (p)) (:goal {formula}))");
        check(
            d,
            &p,
            &plan("()", "()"),
            if valid {
                Status::Valid
            } else {
                Status::InvalidPlan
            },
        );
    }
}

#[test]
fn quantified_conditions_and_effects_respect_types_and_scope() {
    let d = "(define (domain d) (:types item other) (:predicates (p ?x - item) (q ?x - item))
      (:action a :parameters (?x - item)
        :precondition (and (exists (?x - item) (p ?x)) (not (p ?x)))
        :effect (forall (?x - item) (when (p ?x) (q ?x)))))";
    let p = "(define (problem p) (:domain d) (:objects a b - item c - other)
      (:init (p b)) (:goal (and (q b) (not (q a))
        (forall (?x - item) (imply (p ?x) (q ?x)))
        (exists (?x - item) (and (p ?x) (q ?x))))))";
    check(d, p, &plan("(a (a a))", "()"), Status::Valid);
    check(d, p, &plan("(a (a b))", "()"), Status::InvalidPlan);

    let d = "(define (domain d) (:types item other) (:predicates (p ?x - item)))";
    for (formula, valid) in [
        ("(forall (?x - item) (p ?x))", true),
        ("(exists (?x - item) (p ?x))", false),
        ("(not (forall (?x - item) (p ?x)))", false),
        ("(not (exists (?x - item) (p ?x)))", true),
    ] {
        let p = format!(
            "(define (problem p) (:domain d) (:objects c - other) (:init) (:goal {formula}))"
        );
        check(
            d,
            &p,
            &plan("()", "()"),
            if valid {
                Status::Valid
            } else {
                Status::InvalidPlan
            },
        );
    }
}

#[test]
fn disjunctive_methods_can_be_enabled_by_conditional_effects() {
    let d = "(define (domain d) (:predicates (p) (q)) (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (or (q) (p)) :subtasks (leaf))
      (:action leaf :parameters ())
      (:action set :parameters () :effect (when (not (q)) (p)))
      (:action clear :parameters () :effect (not (p))))";
    let p = "(define (problem p) (:domain d) (:htn :subtasks (and (t) (set) (clear))) (:init))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (t (t)) (s (set)) (c (clear))))
        (t (t) :method (m) :subtasks (l (leaf))))
      (:htn :tasks (and (s (set)) (c (clear)) (l (leaf))) :ordering (< s l)))";
    // The guard may fire between set and clear even if clear precedes leaf.
    check(d, p, s, Status::Valid);
    check(d, p, &s.replace("(< s l)", "()"), Status::InvalidPlan);
    check(
        d,
        p,
        &s.replace("(< s l)", "(and (< s c) (< c l))"),
        Status::Valid,
    );
}

#[test]
fn static_disjunctions_and_empty_method_guards_are_checked_as_formulas() {
    let d = "(define (domain d) (:predicates (p) (q)) (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (or (p) (q)) :subtasks ()))";
    let p = "(define (problem p) (:domain d) (:htn :subtasks (t)) (:init (q)))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (t (t))) (t (t) :method (m) :subtasks ()))
      (:htn :ordered-tasks ()))";
    check(d, p, s, Status::Valid);
    check(
        d,
        &p.replace("(:init (q))", "(:init)"),
        s,
        Status::InvalidPlan,
    );
}

#[test]
fn unused_and_inactive_branches_are_still_schema_checked() {
    let p = "(define (problem p) (:domain d) (:init (p)))";
    for fields in [
        ":precondition (or (p) (missing))",
        ":effect (when (missing) (q))",
        ":effect (when (or) (missing))",
        ":precondition (exists (?x - absent) (p))",
        ":precondition (when (p) (q))",
        ":effect (imply (p) (q))",
        ":effect (when (p) (when (q) (p)))",
        ":effect (when (p) (forall (?x - object) (q)))",
        ":effect (when (p) (not (and (p) (q))))",
    ] {
        let d = format!(
            "(define (domain d) (:predicates (p) (q))
          (:action unused :parameters () {fields}))"
        );
        check(&d, p, &plan("()", "()"), Status::InputError);
    }
}

#[test]
fn costs_remain_unconditional_even_with_false_effect_guards() {
    let d = "(define (domain d) (:requirements :action-costs) (:predicates (p) (q))
      (:functions (total-cost)) (:action a :parameters ()
        :effect (and (when (p) (q)) (increase (total-cost) 7))))";
    let p = "(define (problem p) (:domain d) (:init (= (total-cost) 0)) (:metric minimize (total-cost)))";
    let r = check(d, p, &plan("(a (a))", "()"), Status::Valid);
    assert_eq!(r.metrics.unwrap().cost, "7");
    for effect in [
        "(when (or) (increase (total-cost) 7))",
        "(when (p) (and (q) (increase (total-cost) 7)))",
        "(forall (?x - object) (when (p) (increase (total-cost) 7)))",
    ] {
        let d = d.replace("(and (when (p) (q)) (increase (total-cost) 7))", effect);
        let r = check(&d, p, &plan("()", "()"), Status::InputError);
        assert_eq!(r.diagnostics[0].code, "cost_effect");
    }
}

#[test]
fn symbolic_validation_reaches_both_verdicts_past_the_former_work_cutoff() {
    let d = "(define (domain d) (:predicates (p) (q)) (:action noop :parameters ()))";
    let actions = (0..3300)
        .map(|i| format!("(a{i} (noop))"))
        .collect::<Vec<_>>();
    let s = plan(&format!("(and {})", actions.join(" ")), "()");
    for (initial, expected) in [("(p)", Status::Valid), ("", Status::InvalidPlan)] {
        let p = format!("(define (problem p) (:domain d) (:init {initial}) (:goal (or (p) (q))))");
        let r = check(d, &p, &s, expected);
        assert!(r.work > 10_000_000, "{r:#?}");
        if expected == Status::InvalidPlan {
            assert_eq!(r.diagnostics[0].code, "goal");
            assert_eq!(r.diagnostics[0].counterexample.len(), 3300);
        }
    }
}

#[test]
fn empty_condition_normalization_preserves_source_positions_and_negative_init() {
    let d = "(define (domain d) (:predicates (p) (q)))";
    let p = "(define (problem p) (:domain d) (:goal (and () () (not (p)))) (:init (not (p))))";
    check(d, p, &plan("()", "()"), Status::Valid);
    let p = p.replace("(not (p)))) (:init", "(p))) (:init");
    check(d, &p, &plan("()", "()"), Status::InvalidPlan);

    let d = "(define (domain d) (:predicates (p)) (:action a :parameters () :precondition (or () () (missing))))";
    let p = "(define (problem p) (:domain d) (:init))";
    let r = check(d, p, &plan("()", "()"), Status::InputError);
    let location = r.diagnostics[0].location.as_ref().unwrap();
    assert_eq!(location.file, "domain");
    assert_eq!(location.column as usize, d.find("missing").unwrap() + 1);

    let d = "(define (domain d) (:predicates (p) (q)))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (and () () (not (p) (q)))))";
    let r = check(d, p, &plan("()", "()"), Status::InputError);
    let location = r.diagnostics[0].location.as_ref().unwrap();
    assert_eq!(location.file, "problem");
    assert_eq!(location.column as usize, p.find("(q)").unwrap() + 1);
}
