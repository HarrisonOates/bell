use bell::{ExecutionBackend, Options, Profile, Status, validate};

fn options() -> Options {
    Options {
        profile: Profile::Hddl11,
        execution_backend: ExecutionBackend::Symbolic,
        ..Options::default()
    }
}

fn plan(actions: &str, order: &str) -> String {
    format!(
        "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks ())) (:htn :tasks {actions} :ordering {order}))"
    )
}

#[test]
fn universal_validation_matches_unsatisfiability_of_every_two_variable_cnf() {
    // Every subset of the eight nontrivial clauses, including unit clauses.
    // Truth tables are independent of Bell's condition/effect compilation.
    let clauses = [
        ("(x)", 0b1010),
        ("(not (x))", 0b0101),
        ("(y)", 0b1100),
        ("(not (y))", 0b0011),
        ("(or (x) (y))", 0b1110),
        ("(or (x) (not (y)))", 0b1011),
        ("(or (not (x)) (y))", 0b1101),
        ("(or (not (x)) (not (y)))", 0b0111),
    ];
    let p = "(define (problem p) (:domain d) (:init))";
    let s = plan(
        "(and (tx (tx)) (fx (fx)) (ty (ty)) (fy (fy)) (u (check)))",
        "(and (< tx u) (< fx u) (< ty u) (< fy u))",
    );
    let mut valid = 0;
    let mut invalid = 0;
    for mask in 0..256 {
        let mut truth = 0b1111;
        let mut parts = vec![];
        for (i, &(clause, table)) in clauses.iter().enumerate() {
            if mask & (1 << i) != 0 {
                truth &= table;
                parts.push(clause);
            }
        }
        let formula = format!("(and {})", parts.join(" "));
        let d = format!(
            "(define (domain d) (:predicates (x) (y))
          (:action tx :parameters () :effect (x))
          (:action fx :parameters () :effect (not (x)))
          (:action ty :parameters () :effect (y))
          (:action fy :parameters () :effect (not (y)))
          (:action check :parameters () :precondition (not {formula})))"
        );
        let result = validate(&d, p, &s, &options());
        assert_eq!(
            result.status,
            if truth == 0 {
                Status::Valid
            } else {
                Status::InvalidPlan
            },
            "{formula}: {result:#?}"
        );
        if truth == 0 {
            valid += 1;
        } else {
            invalid += 1;
            let diagnostic = &result.diagnostics[0];
            assert_eq!(diagnostic.code, "action_precondition");
            assert_eq!(diagnostic.counterexample.len(), 5);
            assert_eq!(diagnostic.counterexample.last().unwrap(), "u");
            let mut assignment = 0;
            for a in &diagnostic.counterexample[..4] {
                match a.as_str() {
                    "tx" => assignment |= 1,
                    "fx" => assignment &= !1,
                    "ty" => assignment |= 2,
                    "fy" => assignment &= !2,
                    _ => panic!("{a}"),
                }
            }
            assert_ne!(truth & (1 << assignment), 0, "witness must satisfy the CNF");
        }
    }
    assert!(valid > 0 && invalid > 0);
}

#[test]
fn enabled_but_inexecutable_actions_are_failures_even_if_another_order_works() {
    let d = "(define (domain d) (:predicates (p))
      (:action set :parameters () :effect (p))
      (:action use :parameters () :precondition (p)))";
    let p = "(define (problem p) (:domain d) (:init))";
    let unordered = plan("(and (s (set)) (u (use)))", "()");
    let r = validate(d, p, &unordered, &options());
    assert_eq!(r.status, Status::InvalidPlan, "{r:#?}");
    assert_eq!(r.diagnostics[0].counterexample, ["u"]);
    let ordered = plan("(and (s (set)) (u (use)))", "(< s u)");
    assert_eq!(validate(d, p, &ordered, &options()).status, Status::Valid);
}

#[test]
fn equal_facts_and_action_sets_do_not_erase_method_check_history() {
    let d = "(define (domain d) (:predicates (p) (q)) (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (and (p) (q)) :subtasks (leaf))
      (:action a :parameters () :effect (p))
      (:action b :parameters () :effect (and (q) (not (p))))
      (:action reset :parameters () :effect (and (not (p)) (not (q))))
      (:action leaf :parameters ()))";
    let p = "(define (problem p) (:domain d)
      (:htn :subtasks (and (a) (b) (reset) (t))) (:init))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (a (a)) (b (b)) (r (reset)) (t (t))))
        (t (t) :method (m) :subtasks (l (leaf))))
      (:htn :tasks (and (a (a)) (b (b)) (r (reset)) (l (leaf)))
        :ordering (and (< a r) (< b r) (< r l))))";
    // Both orders reach identical facts after reset. Only b,a,reset has ever
    // satisfied the method guard, and its completion bit must survive reset.
    let r = validate(d, p, s, &options());
    assert_eq!(r.status, Status::InvalidPlan, "{r:#?}");
    assert_eq!(r.diagnostics[0].code, "method_precondition");
    assert_eq!(r.diagnostics[0].counterexample, ["a", "b", "r", "l"]);
    assert_eq!(
        validate(d, p, &s.replace("(< a r)", "(< a r) (< b a)"), &options()).status,
        Status::Valid
    );
}

#[test]
fn empty_method_checks_run_after_the_final_action_and_respect_predecessors() {
    let d = "(define (domain d) (:predicates (p)) (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (p) :subtasks ())
      (:action set :parameters () :effect (p)))";
    let p = "(define (problem p) (:domain d) (:htn :ordered-subtasks (and (set) (t))) (:init))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (s (set)) (t (t))))
        (t (t) :method (m) :subtasks ())) (:htn :ordered-tasks (s (set))))";
    let result = validate(d, p, s, &options());
    assert_eq!(result.status, Status::Valid, "{result:#?}");
    let d = d.replace(":effect (p)", ":effect (not (p))");
    let p = p.replace("(:init)", "(:init (p))");
    let result = validate(&d, &p, s, &options());
    assert_eq!(result.status, Status::InvalidPlan, "{result:#?}");
    assert_eq!(result.diagnostics[0].code, "method_precondition");
    assert_eq!(result.diagnostics[0].counterexample, ["s"]);
}

#[test]
fn empty_plan_checks_auxiliary_events_and_goal_without_an_action_layer() {
    let d = "(define (domain d) (:predicates (p)) (:task t :parameters ())
      (:method m :parameters () :task (t) :precondition (p) :subtasks ()))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (t (t))) (t (t) :method (m) :subtasks ()))
      (:htn :ordered-tasks ()))";
    for (init, goal, status) in [
        ("(p)", "(p)", Status::Valid),
        ("", "()", Status::InvalidPlan),
        ("(p)", "(not (p))", Status::InvalidPlan),
    ] {
        let p = format!(
            "(define (problem p) (:domain d) (:htn :subtasks (t)) (:init {init}) (:goal {goal}))"
        );
        let r = validate(d, &p, s, &options());
        assert_eq!(r.status, status, "{r:#?}");
    }
}

#[test]
fn symbolic_frontiers_compress_many_orders_and_preserve_original_metrics() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:action toggle :parameters () :effect
        (and (when (p) (and (not (p)) (q))) (when (not (p)) (p))))
      (:action noop :parameters ()))";
    let p = "(define (problem p) (:domain d) (:init) (:goal (q)))";
    let mut actions = vec!["(a (toggle))".to_owned(), "(b (toggle))".to_owned()];
    actions.extend((0..24).map(|i| format!("(n{i} (noop))")));
    let s = plan(&format!("(and {})", actions.join(" ")), "()");
    let result = validate(d, p, &s, &options());
    assert_eq!(result.status, Status::Valid, "{result:#?}");
    assert!(result.work < 5_000_000, "{result:#?}");
    let metrics = result.metrics.unwrap();
    assert_eq!(metrics.actions, 26);
    assert_eq!(metrics.makespan, 1);
    // A failing goal forces reconstruction through all frontiers, including
    // frontiers retained across BDD garbage collections.
    let p = p.replace("(:goal (q))", "(:goal (p))");
    let result = validate(d, &p, &s, &options());
    assert_eq!(result.status, Status::InvalidPlan, "{result:#?}");
    assert_eq!(result.diagnostics[0].code, "goal");
    assert_eq!(result.diagnostics[0].counterexample.len(), 26);
}

#[test]
fn nested_check_actions_fire_before_a_delete_and_do_not_change_plan_metrics() {
    let d = "(define (domain d) (:predicates (p) (fixed)) (:task t :parameters ())
      (:method guarded :parameters () :task (t) :precondition (p) :subtasks (t))
      (:method static :parameters () :task (t) :precondition (fixed) :subtasks (t))
      (:method finish :parameters () :task (t) :subtasks (leaf))
      (:action set :parameters () :effect (p))
      (:action clear :parameters () :effect (not (p)))
      (:action leaf :parameters ()))";
    let p = "(define (problem p) (:domain d)
      (:htn :subtasks (and (set) (t) (clear))) (:init (fixed)))";
    let mut s = String::from(
        "(define (plan s) (:domain d) (:problem p) (:decomposition
          (:root :subtasks (and (s (set)) (t0 (t)) (c (clear))))",
    );
    // Contract static wrappers between dynamic checks, preserving the checks'
    // relative order. All 64 dynamic checks must fire at the same boundary.
    for i in 0..128 {
        let method = if i % 2 == 0 { "guarded" } else { "static" };
        s.push_str(&format!(
            "(t{i} (t) :method ({method}) :subtasks (t{} (t)))",
            i + 1
        ));
    }
    s.push_str(
        "(t128 (t) :method (finish) :subtasks (l (leaf))))
          (:htn :ordered-tasks (and (s (set)) (c (clear)) (l (leaf)))))",
    );
    let result = validate(d, p, &s, &options());
    assert_eq!(result.status, Status::Valid, "{result:#?}");
    assert!(result.work < 5_000_000, "{result:#?}");
    let metrics = result.metrics.unwrap();
    assert_eq!(metrics.actions, 3);
    assert_eq!(metrics.makespan, 3);
    // Failure after the guards have fired exercises reverse reconstruction of
    // every internal check. User traces must still contain only real actions.
    let bad_goal = p.replace("(:init (fixed))", "(:init (fixed)) (:goal (p))");
    let result = validate(d, &bad_goal, &s, &options());
    assert_eq!(result.status, Status::InvalidPlan, "{result:#?}");
    assert_eq!(result.diagnostics[0].code, "goal");
    assert_eq!(result.diagnostics[0].counterexample, ["s", "c", "l"]);
}

#[test]
fn contracting_unconditional_wrappers_preserves_method_check_dependencies() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:task outer :parameters ()) (:task bridge :parameters ()) (:task inner :parameters ())
      (:method m-outer :parameters () :task (outer) :precondition (q) :subtasks (bridge))
      (:method m-bridge :parameters () :task (bridge) :subtasks (inner))
      (:method m-inner :parameters () :task (inner) :precondition (p) :subtasks (leaf))
      (:action change :parameters () :effect (and (q) (not (p))))
      (:action leaf :parameters ()))";
    let p = "(define (problem p) (:domain d)
      (:htn :subtasks (and (change) (outer))) (:init (p)))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition (:root :subtasks (and (a (change)) (o (outer))))
        (o (outer) :method (m-outer) :subtasks (b (bridge)))
        (b (bridge) :method (m-bridge) :subtasks (i (inner)))
        (i (inner) :method (m-inner) :subtasks (l (leaf))))
      (:htn :ordered-tasks (and (a (change)) (l (leaf)))))";
    // p holds initially, but its check must wait for the outer q check. q only
    // becomes true when p is deleted, so no legal placement exists.
    let result = validate(d, p, s, &options());
    assert_eq!(result.status, Status::InvalidPlan, "{result:#?}");
    assert_eq!(result.diagnostics[0].code, "method_precondition");
    assert_eq!(result.diagnostics[0].counterexample, ["a", "l"]);
    let p = p.replace("(:init (p))", "(:init (p) (q))");
    assert_eq!(validate(d, &p, s, &options()).status, Status::Valid);
}

#[test]
fn contracted_empty_methods_preserve_order_between_other_empty_checks() {
    let d = "(define (domain d) (:predicates (p) (q))
      (:task first :parameters ()) (:task empty :parameters ()) (:task last :parameters ())
      (:method m-first :parameters () :task (first) :precondition (q) :subtasks ())
      (:method m-empty :parameters () :task (empty) :subtasks ())
      (:method m-last :parameters () :task (last) :precondition (p) :subtasks ())
      (:action change :parameters () :effect (and (q) (not (p)))))";
    let p = "(define (problem p) (:domain d) (:init (p))
      (:htn :subtasks (and (a (change)) (f (first)) (e (empty)) (l (last)))
        :ordering (and (< f e) (< e l))))";
    let s = "(define (plan s) (:domain d) (:problem p)
      (:decomposition
        (:root :subtasks (and (a (change)) (f (first)) (e (empty)) (l (last))))
        (f (first) :method (m-first) :subtasks ())
        (e (empty) :method (m-empty) :subtasks ())
        (l (last) :method (m-last) :subtasks ()))
      (:htn :ordered-tasks (a (change))))";
    let result = validate(d, p, s, &options());
    assert_eq!(result.status, Status::InvalidPlan, "{result:#?}");
    assert_eq!(result.diagnostics[0].code, "method_precondition");
    assert_eq!(result.diagnostics[0].counterexample, ["a"]);
    let p = p.replace("(:init (p))", "(:init (p) (q))");
    assert_eq!(validate(d, &p, s, &options()).status, Status::Valid);
}
