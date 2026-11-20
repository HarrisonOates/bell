use htn_plan_validation::{Options, Profile, Report, Status, validate};

fn check(d: &str, p: &str, s: &str) -> Report {
    validate(
        d,
        p,
        s,
        &Options {
            profile: Profile::Hddl11,
            ..Options::default()
        },
    )
}
fn status(d: &str, p: &str, s: &str, expected: Status) -> Report {
    let report = check(d, p, s);
    assert_eq!(report.status, expected, "{:#?}", report);
    report
}
const DOMAIN: &str = "(define (domain d) (:requirements :hierarchy :typing :method-preconditions)
 (:types place) (:predicates (at ?x - place))
 (:task travel :parameters (?to - place))
 (:method route :parameters (?from ?to - place) :task (travel ?to)
   :precondition (at ?from) :subtasks (step (move ?from ?to)))
 (:action move :parameters (?from ?to - place) :precondition (at ?from)
   :effect (and (not (at ?from)) (at ?to))))";
const PROBLEM: &str = "(define (problem p) (:domain d) (:objects a b - place)
 (:htn :ordered-subtasks (travel b)) (:init (at a)) (:goal (at b)))";
const PLAN: &str = "(define (plan s) (:domain d) (:problem p)
 (:decomposition (:root :subtasks (r (travel b)))
   (r (travel b) :method (route a b) :subtasks (x (move a b))))
 (:htn :ordered-tasks (x (move a b))))";

#[test]
fn validates_source_hierarchy_and_goal() {
    let r = status(DOMAIN, PROBLEM, PLAN, Status::Valid);
    let m = r.metrics.unwrap();
    assert_eq!((m.actions, m.makespan, m.cost.as_str()), (1, 1, "1"));
    status(
        &DOMAIN.to_uppercase(),
        &PROBLEM.to_uppercase(),
        &format!("; comment\n{}", PLAN.to_uppercase()),
        Status::Valid,
    );
}

#[test]
fn corrupt_hierarchies_are_rejected_with_occurrences() {
    for bad in [
        PLAN.replace("(route a b)", "(route b a)"),
        PLAN.replace("(route a b)", "(missing a b)"),
        PLAN.replace("(route a b)", "(route a)"),
        PLAN.replace("(route a b)", "(route a unknown)"),
        PLAN.replace(":subtasks (x (move a b))", ":subtasks (x (move b a))"),
        PLAN.replace(":subtasks (x (move a b))", ":subtasks ()"),
        PLAN.replace(
            ":ordered-tasks (x (move a b))",
            ":ordered-tasks (and (x (move a b)) (x (move a b)))",
        ),
        PLAN.replace(
            ":ordered-tasks (x (move a b))",
            ":ordered-tasks (and (x (move a b)) (extra (move a b)))",
        ),
    ] {
        status(DOMAIN, PROBLEM, &bad, Status::InvalidPlan);
    }
    let missing = PLAN.replace(
        "(r (travel b) :method (route a b) :subtasks (x (move a b)))",
        "",
    );
    let report = status(DOMAIN, PROBLEM, &missing, Status::InvalidPlan);
    assert_eq!(report.diagnostics[0].occurrence.as_deref(), Some("r"));
    assert!(report.diagnostics[0].location.is_some());
}

fn plain_plan(actions: &str, order: &str) -> String {
    format!(
        "(define (plan s) (:domain d) (:problem p) (:decomposition (:root :subtasks ())) (:htn :tasks {actions} :ordering {order}))"
    )
}
const EMPTY: &str = "(define (plan s) (:domain d) (:problem p) (:decomposition (:root :subtasks ())) (:htn :ordered-tasks ()))";

#[test]
fn absent_initial_htn_checks_actions_and_goal() {
    let d = "(define (domain d) (:predicates (p)) (:action set :parameters () :effect (p)))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (p)))";
    status(d, p, EMPTY, Status::InvalidPlan);
    status(
        d,
        &p.replace("(:init)", "(:init (p))"),
        EMPTY,
        Status::Valid,
    );
    status(d, p, &plain_plan("(x (set))", "()"), Status::Valid);
    let plan =
        plain_plan("(x (set))", "()").replace(":root :subtasks ()", ":root :subtasks (x (set))");
    status(d, p, &plan, Status::Valid);
}

#[test]
fn mtc_requires_every_linearization_to_work() {
    let d = "(define (domain d) (:predicates (p))
      (:action set :parameters () :effect (p))
      (:action use :parameters () :precondition (p))
      (:action clear :parameters () :effect (not (p))))";
    let p = "(define (problem p) (:domain d) (:init))";
    let actions = "(and (s (set)) (u (use)) (c (clear)))";
    status(d, p, &plain_plan(actions, "()"), Status::InvalidPlan);
    status(d, p, &plain_plan(actions, "(< s u)"), Status::InvalidPlan);
    status(
        d,
        p,
        &plain_plan(actions, "(and (< c s) (< s u))"),
        Status::Valid,
    );
    status(
        d,
        p,
        &plain_plan(actions, "(and (< s u) (< u c))"),
        Status::Valid,
    );
    status(
        d,
        p,
        &plain_plan(actions, "(and (< s u) (< u s))"),
        Status::InvalidPlan,
    );
    status(
        d,
        p,
        &plain_plan(actions, "(< missing u)"),
        Status::InvalidPlan,
    );
}

#[test]
fn restoration_can_use_different_producers() {
    let d = "(define (domain d) (:predicates (p))
      (:action add :parameters () :effect (p))
      (:action del :parameters () :effect (not (p)))
      (:action use :parameters () :precondition (p)))";
    let p = "(define (problem p) (:domain d) (:init))";
    let s = plain_plan(
        "(and (d1 (del)) (a1 (add)) (d2 (del)) (a2 (add)) (u (use)))",
        "(and (< d1 a1) (< d2 a2) (< a1 u) (< a2 u))",
    );
    status(d, p, &s, Status::Valid);
}

#[test]
fn negative_literals_and_own_effects() {
    let d = "(define (domain d) (:predicates (p))
      (:action add :parameters () :precondition (not (p)) :effect (p))
      (:action del :parameters () :precondition (p) :effect (not (p))))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (not (p))))";
    status(
        d,
        p,
        &plain_plan("(and (a (add)) (b (del)))", "(< a b)"),
        Status::Valid,
    );
    status(
        d,
        p,
        &plain_plan("(and (a (add)) (b (del)))", "()"),
        Status::InvalidPlan,
    );
}

#[test]
fn hierarchy_order_is_required_not_inserted() {
    let d = "(define (domain d) (:predicates (p))
      (:task empty :parameters ()) (:method nothing :parameters () :task (empty) :subtasks ())
      (:action a :parameters ()) (:action b :parameters ()))";
    let p =
        "(define (problem p) (:domain d) (:htn :ordered-subtasks (and (a) (empty) (b))) (:init))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (x (a)) (e (empty)) (y (b))))
       (e (empty) :method (nothing) :subtasks ()))
      (:htn :tasks (and (x (a)) (y (b))) :ordering (< x y)))";
    status(d, p, s, Status::Valid);
    let r = status(d, p, &s.replace("(< x y)", "()"), Status::InvalidPlan);
    assert_eq!(r.diagnostics[0].code, "missing_hierarchy_order");
    status(d, p, &s.replace("(< x y)", "(< y x)"), Status::InvalidPlan);
}

#[test]
fn method_checks_are_internal_and_may_hold_early() {
    let d = "(define (domain d) (:predicates (p))
      (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (p) :subtasks (a))
      (:action a :parameters ()) (:action del :parameters () :effect (not (p))))";
    let p = "(define (problem p) (:domain d) (:htn :subtasks (and (t) (del))) (:init (p)))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (t (t)) (d (del))))
       (t (t) :method (m) :subtasks (a (a))))
      (:htn :ordered-tasks (and (d (del)) (a (a)))))";
    status(d, p, s, Status::Valid);
    status(
        d,
        &p.replace("(:init (p))", "(:init)"),
        s,
        Status::InvalidPlan,
    );
    let ordered = p.replace(
        ":subtasks (and (t) (del))",
        ":ordered-subtasks (and (del) (t))",
    );
    let roots = s.replace(
        ":root :subtasks (and (t (t)) (d (del)))",
        ":root :subtasks (and (d (del)) (t (t)))",
    );
    status(d, &ordered, &roots, Status::InvalidPlan);
}

#[test]
fn method_guard_placement_depends_on_linearization() {
    let d = "(define (domain d) (:predicates (p))
      (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (p) :subtasks (a))
      (:action a :parameters ()) (:action set :parameters () :effect (p))
      (:action del :parameters () :effect (not (p))))";
    let p = "(define (problem p) (:domain d) (:htn :subtasks (and (t) (set) (del))) (:init))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (t (t)) (s (set)) (d (del))))
       (t (t) :method (m) :subtasks (a (a))))
      (:htn :tasks (and (d (del)) (s (set)) (a (a))) :ordering (< s a)))";
    status(d, p, s, Status::Valid);
    let r = status(d, p, &s.replace("(< s a)", "()"), Status::InvalidPlan);
    assert!(!r.diagnostics[0].counterexample.is_empty());
}

#[test]
fn empty_methods_still_have_preconditions() {
    let d = "(define (domain d) (:predicates (p)) (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (p) :subtasks ()))";
    let p = "(define (problem p) (:domain d) (:htn :subtasks (t)) (:init (p)))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (t (t))) (t (t) :method (m) :subtasks ()))
      (:htn :ordered-tasks ()))";
    status(d, p, s, Status::Valid);
    status(
        d,
        &p.replace("(:init (p))", "(:init)"),
        s,
        Status::InvalidPlan,
    );
}

#[test]
fn root_bindings_and_constraints() {
    let p=PROBLEM.replace("(:htn :ordered-subtasks (travel b))","(:htn :parameters (?dest - place) :ordered-subtasks (travel ?dest) :constraints (not (= ?dest a)))");
    let s = PLAN.replace(":root :subtasks", ":root :parameters (b) :subtasks");
    status(DOMAIN, &p, &s, Status::Valid);
    status(
        DOMAIN,
        &p,
        &s.replace(":parameters (b)", ":parameters (a)"),
        Status::InvalidPlan,
    );
    status(DOMAIN, &p, PLAN, Status::InvalidPlan);
}

#[test]
fn declared_types_are_checked_even_in_unused_methods() {
    let d = "(define (domain d) (:types animal - object dog - animal)
      (:predicates (p)) (:task t :parameters (?a - animal))
      (:action bark :parameters (?d - dog))
      (:method m :parameters (?a - animal) :task (t ?a) :subtasks (bark ?a)))";
    let p = "(define (problem p) (:domain d) (:init))";
    status(d, p, EMPTY, Status::InputError);
    status(
        &d.replace(
            ":method m :parameters (?a - animal)",
            ":method m :parameters (?a - dog)",
        ),
        p,
        EMPTY,
        Status::Valid,
    );
    status(
        &d.replace("animal - object", "animal - missing"),
        p,
        EMPTY,
        Status::InputError,
    );
    status(
        &d.replace("animal - object", "animal - dog"),
        p,
        EMPTY,
        Status::InputError,
    );
}

#[test]
fn unconditional_quantifiers_use_typed_domains() {
    let d = "(define (domain d) (:types item other) (:predicates (p ?i - item))
      (:action set :parameters () :effect (forall (?i - item) (p ?i))))";
    let p = "(define (problem p) (:domain d) (:objects a b - item c - other)
      (:init) (:goal (forall (?i - item) (p ?i))))";
    status(d, p, &plain_plan("(s (set))", "()"), Status::Valid);
    status(d, p, EMPTY, Status::InvalidPlan);
    status(d, &p.replace("a b - item ", ""), EMPTY, Status::Valid);
}

#[test]
fn costs_are_exact_integers_and_definedness_matters() {
    let d = "(define (domain d) (:requirements :action-costs) (:predicates (p))
      (:functions (total-cost) (price))
      (:action paid :parameters () :effect (increase (total-cost) (price)))
      (:action free :parameters ()))";
    let p = "(define (problem p) (:domain d) (:init (= (total-cost) 0) (= (price) 9223372036854775807)) (:metric minimize (total-cost)))";
    let s = plain_plan(
        "(and (a (paid)) (b (paid)) (f (free)))",
        "(and (< a b) (< b f))",
    );
    let r = status(d, p, &s, Status::Valid);
    assert_eq!(r.metrics.unwrap().cost, "18446744073709551614");
    status(
        d,
        &p.replace("(= (price) 9223372036854775807)", ""),
        &s,
        Status::InvalidPlan,
    );
    status(
        d,
        &p.replace("(= (price) 9223372036854775807)", ""),
        &plain_plan("(f (free))", "()"),
        Status::Valid,
    );
    status(
        d,
        &p.replace("9223372036854775807", "1.5"),
        &s,
        Status::InputError,
    );
    status(
        d,
        &p.replace("9223372036854775807", "-1"),
        &s,
        Status::InputError,
    );
    let bad = d.replace(
        "(increase (total-cost) (price))",
        "(and (increase (total-cost) 1) (increase (total-cost) 2))",
    );
    status(&bad, p, &s, Status::InputError);
}

#[test]
fn unsupported_features_are_not_silently_ignored() {
    let p = "(define (problem p) (:domain d) (:init))";
    for effect in [
        "(when (p) (q))",
        "(or (p) (q))",
        "(forall (?x - object) (when (p) (q)))",
    ] {
        let d = format!(
            "(define (domain d) (:predicates (p) (q)) (:action unused :parameters () :effect {effect}))"
        );
        status(&d, p, EMPTY, Status::Unsupported);
    }
    let d = "(define (domain d) (:predicates (p) (q)))";
    status(
        d,
        &p.replace("(:init)", "(:init) (:goal (or (p) (q)))"),
        EMPTY,
        Status::Unsupported,
    );
}

#[test]
fn profile_and_makespan_are_separate_from_language_validity() {
    let d = "(define (domain d) (:predicates (p)) (:action a :parameters ()))";
    let p = "(define (problem p) (:domain d) (:init))";
    let s = plain_plan("(and (a (a)) (b (a)) (c (a)))", "(< a b c)");
    assert_eq!(status(d, p, &s, Status::Valid).metrics.unwrap().makespan, 2);
    assert_eq!(
        validate(d, p, &s, &Options::default()).status,
        Status::ProfileRejected
    );
    let d = d.replace("(:predicates", "(:requirements :makespan) (:predicates");
    let p = p.replace("(:init)", "(:init) (:metric minimize (makespan))");
    assert_eq!(
        validate(&d, &p, &s, &Options::default()).status,
        Status::Valid
    );
}

#[test]
fn malformed_reports_and_limits_do_not_validate() {
    status(DOMAIN, PROBLEM, &format!("{PLAN} ()"), Status::InputError);
    status(
        DOMAIN,
        PROBLEM,
        &PLAN.replace("(:problem p)", "(:problem p) (:problem p)"),
        Status::InputError,
    );
    status(DOMAIN, &format!("{PROBLEM} junk"), PLAN, Status::InputError);
    status(
        DOMAIN,
        PROBLEM,
        "(define (plan s) (:domain d) (:problem p) (:unsolvable))",
        Status::UnsolvabilityReport,
    );
    let options = Options {
        max_work: 1,
        ..Options::default()
    };
    assert_eq!(
        validate(DOMAIN, PROBLEM, PLAN, &options).status,
        Status::LimitExceeded
    );
    let options = Options {
        max_input_bytes: 1,
        ..Options::default()
    };
    assert_eq!(
        validate(DOMAIN, PROBLEM, PLAN, &options).status,
        Status::LimitExceeded
    );
    let options = Options {
        timeout: Some(std::time::Duration::ZERO),
        ..Options::default()
    };
    assert_eq!(
        validate(DOMAIN, PROBLEM, PLAN, &options).status,
        Status::LimitExceeded
    );
}

#[test]
fn negative_initial_facts_are_typed_and_cannot_contradict_positive_facts() {
    let d = "(define (domain d) (:types item) (:predicates (p ?i - item)))";
    let p = "(define (problem p) (:domain d) (:objects a - item)\n\t(:init (not\n\t(p a))) (:goal (not (p a))))";
    status(d, p, EMPTY, Status::Valid);
    status(
        d,
        &p.replace(":init (not", ":init (p a) (not"),
        EMPTY,
        Status::InputError,
    );
    status(
        d,
        &p.replace("(not\n\t(p a))", "(not (unknown a))"),
        EMPTY,
        Status::InputError,
    );
    status(
        d,
        &p.replace("(not\n\t(p a))", "(not (p unknown))"),
        EMPTY,
        Status::InputError,
    );
    status(
        d,
        &p.replace("(not\n\t(p a))", "(not (p a) (p a))"),
        EMPTY,
        Status::InputError,
    );
    status(
        d,
        &format!(
            "\u{feff}; unicode comment: ✓\r\n{}",
            p.replace('\n', "\r\n")
        ),
        EMPTY,
        Status::Valid,
    );
}

#[test]
fn input_limits_and_required_sections_have_explicit_outcomes() {
    let d = "(define (domain d) (:predicates (p)))";
    status(
        d,
        "(define (problem p) (:domain d))",
        EMPTY,
        Status::InputError,
    );
    let p = "(define (problem p) (:domain d) (:init (= (price) 9223372036854775808)))";
    let report = status(d, p, EMPTY, Status::LimitExceeded);
    assert_eq!(report.diagnostics[0].code, "integer_range");
    status(
        &d.replace("(domain d)", "(domain _d)"),
        "(define (problem p) (:domain d) (:init))",
        EMPTY,
        Status::InputError,
    );
}

#[test]
fn malformed_input_mutations_do_not_panic() {
    for which in 0..3 {
        let source = [DOMAIN, PROBLEM, PLAN][which];
        for offset in (0..source.len()).step_by(3) {
            for replacement in ["", "(", ")", " :goal "] {
                let mut mutated = source.to_string();
                mutated.replace_range(offset..offset + 1, replacement);
                let mut inputs = [DOMAIN, PROBLEM, PLAN];
                inputs[which] = &mutated;
                check(inputs[0], inputs[1], inputs[2]);
            }
        }
    }
}

#[test]
fn nested_method_guards_can_hold_at_different_times() {
    let d = "(define (domain d) (:predicates (p))
      (:task outer :parameters ()) (:task inner :parameters ())
      (:method first :parameters () :task (outer) :precondition (p) :subtasks (inner))
      (:method second :parameters () :task (inner) :precondition (not (p)) :subtasks (leaf))
      (:action leaf :parameters ()) (:action clear :parameters () :effect (not (p))))";
    let p = "(define (problem p) (:domain d) (:htn :subtasks (and (outer) (clear))) (:init (p)))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (o (outer)) (c (clear))))
       (i (inner) :method (second) :subtasks (l (leaf)))
       (o (outer) :method (first) :subtasks (i (inner))))
      (:htn :ordered-tasks (and (c (clear)) (l (leaf)))))";
    status(d, p, s, Status::Valid);
    status(
        d,
        p,
        &s.replace(
            ":ordered-tasks (and (c (clear)) (l (leaf)))",
            ":tasks (and (c (clear)) (l (leaf)))",
        ),
        Status::InvalidPlan,
    );
}
