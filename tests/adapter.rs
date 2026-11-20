use bell::{Options, Status, adapter::from_panda, validate};

const DOMAIN: &str = "(define (domain d) (:requirements :hierarchy :typing :method-preconditions)
  (:types item) (:predicates (ready ?x - item))
  (:task root :parameters (?x - item)) (:task empty :parameters ())
  (:method m :parameters (?w ?x - item) :task (root ?x) :precondition (ready ?w)
    :ordered-subtasks (and (a ?x) (empty) (a ?x)))
  (:method nothing :parameters () :task (empty) :subtasks ())
  (:action a :parameters (?x - item) :effect ()))";
const PROBLEM: &str = "(define (problem p) (:domain d) (:objects a b - item)
  (:htn :parameters (?r - item) :subtasks (root ?r)) (:init (ready b)))";
const RAW: &str = "search diagnostic
==>
1 __method_precondition_m[b]
2 a[a]
5 __noop
4 a[a]
root 0
0 __top[] -> <__top_method;root[a];m;0;-1,-2,-3,-4> 1 2 3 4
3 empty[] -> nothing 5
<==
search complete
";

#[test]
fn raw_output_recovers_hierarchy_parameters_and_occurrences() {
    let adapted = from_panda(DOMAIN, PROBLEM, RAW, None, &Options::default()).unwrap();
    assert!(adapted.text.contains(":parameters (a)"));
    assert!(adapted.text.contains(":method (m b a)"));
    assert!(adapted.text.contains("(n2 (a a))"));
    assert!(adapted.text.contains("(n4 (a a))"));
    assert!(
        adapted
            .text
            .contains(":method (nothing)\n      :subtasks ()")
    );
    assert!(!adapted.text.contains("__"));
    let report = validate(DOMAIN, PROBLEM, &adapted.text, &Options::default());
    assert_eq!(report.status, Status::Valid, "{report:?}");
    assert_eq!(report.metrics.unwrap().actions, 2);
}

#[test]
fn compressed_actions_expand_to_distinct_occurrences() {
    let domain = DOMAIN.replace("(a ?x) (empty) (a ?x)", "(a ?x) (a ?x)");
    let raw = "==>\n1 %seq#a#1#a#1%[a,a]\nroot 0\n0 root[a] -> m 1\n<==";
    let adapted = from_panda(&domain, PROBLEM, raw, None, &Options::default()).unwrap();
    let report = validate(&domain, PROBLEM, &adapted.text, &Options::default());
    assert_eq!(report.status, Status::Valid, "{report:?}");
    assert_eq!(report.metrics.unwrap().actions, 2);
}

#[test]
fn malformed_raw_graphs_are_rejected_before_recovery() {
    let cases = [
        RAW.replace("<==", ""),
        RAW.replace("root 0", "root 0 0"),
        RAW.replace("root 0", "root 0\nroot 0"),
        RAW.replace("root 0", "root 8"),
        RAW.replace("1 __method", "2 __method"),
        RAW.replace("nothing 5", "nothing 3"),
        RAW.replace("nothing 5", "nothing 99"),
        RAW.replace("nothing 5", "nothing"),
        RAW.replace("2 a[a]", "2 @0 a[a]"),
        RAW.replace("root 0", "root 18446744073709551615"),
        format!("{RAW}\n{RAW}"),
        "unsolvable".into(),
    ];
    for raw in cases {
        assert!(
            from_panda(DOMAIN, PROBLEM, &raw, None, &Options::default()).is_err(),
            "{raw}"
        );
    }
}

#[test]
fn reconstruction_has_work_time_and_input_limits() {
    for options in [
        Options {
            max_work: 1,
            ..Options::default()
        },
        Options {
            timeout: Some(std::time::Duration::ZERO),
            ..Options::default()
        },
        Options {
            max_input_bytes: 1,
            ..Options::default()
        },
    ] {
        let error = from_panda(DOMAIN, PROBLEM, RAW, None, &options)
            .err()
            .unwrap();
        assert_eq!(error.status, Status::LimitExceeded, "{error:?}");
    }
}

#[test]
fn independent_validation_rejects_bad_execution_order() {
    let domain = "(define (domain d) (:requirements :hierarchy) (:predicates (ok))
      (:task t :parameters ())
      (:method m :parameters () :task (t) :ordered-subtasks (and (a) (b)))
      (:action a :parameters () :effect ()) (:action b :parameters () :effect ()))";
    let problem = "(define (problem p) (:domain d) (:htn :subtasks (t)) (:init))";
    let raw = "==>\n2 b[]\n1 a[]\nroot 0\n0 t[] -> m 1 2\n<==";
    let adapted = from_panda(domain, problem, raw, None, &Options::default()).unwrap();
    assert_eq!(
        validate(domain, problem, &adapted.text, &Options::default()).status,
        Status::InvalidPlan
    );
}

#[test]
fn cli_only_publishes_validated_plans_and_preserves_inputs() {
    let directory = std::env::temp_dir().join(format!("bell-adapter-cli-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in [
        ("d", DOMAIN),
        ("p", PROBLEM),
        ("raw", RAW),
        ("out", "previous"),
    ] {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let run = |output: &str, extra: &[&str]| {
        std::process::Command::new(env!("CARGO_BIN_EXE_bell"))
            .current_dir(&directory)
            .args([
                "--json",
                "--input-format",
                "panda",
                "--plan-output",
                output,
                "d",
                "p",
                "raw",
            ])
            .args(extra)
            .output()
            .unwrap()
    };
    let result = run("out", &["--max-work", "1"]);
    assert_eq!(result.status.code(), Some(4));
    assert_eq!(
        std::fs::read_to_string(directory.join("out")).unwrap(),
        "previous"
    );
    let result = run("d", &[]);
    assert_eq!(result.status.code(), Some(2));
    assert_eq!(
        std::fs::read_to_string(directory.join("d")).unwrap(),
        DOMAIN
    );
    let result = run("out", &[]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stdout)
    );
    let report: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(report["status"], "valid");
    let plan = std::fs::read_to_string(directory.join("out")).unwrap();
    assert_eq!(
        validate(DOMAIN, PROBLEM, &plan, &Options::default()).status,
        Status::Valid
    );
    std::fs::write(directory.join("raw"), RAW.replace("root 0", "root 99")).unwrap();
    assert!(!run("out", &[]).status.success());
    assert_eq!(
        std::fs::read_to_string(directory.join("out")).unwrap(),
        plan
    );
    std::fs::remove_dir_all(directory).unwrap();
}
