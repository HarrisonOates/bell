use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};
static NEXT: AtomicU64 = AtomicU64::new(0);
struct Case(std::path::PathBuf);
impl Case {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "bell-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn run(&self, domain: &str, problem: &str, plan: &str, args: &[&str]) -> std::process::Output {
        for (name, source) in [
            ("domain.hddl", domain),
            ("problem.hddl", problem),
            ("plan.hddl", plan),
        ] {
            fs::write(self.0.join(name), source).unwrap();
        }
        Command::new(env!("CARGO_BIN_EXE_bell"))
            .current_dir(&self.0)
            .args(["domain.hddl", "problem.hddl", "plan.hddl"])
            .args(args)
            .output()
            .unwrap()
    }
}
impl Drop for Case {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
const DOMAIN: &str = "(define (domain d) (:predicates (p)))";
const PROBLEM: &str = "(define (problem p) (:domain d) (:init (p)) (:goal (p)))";
const PLAN: &str = "(define (plan s) (:domain d) (:problem p) (:decomposition (:root :subtasks ())) (:htn :ordered-tasks ()))";
#[test]
fn accepts_only_files_and_emits_json_with_integer_metrics() {
    let case = Case::new();
    let output = case.run(DOMAIN, PROBLEM, PLAN, &["--json"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["status"], "valid");
    assert_eq!(json["metrics"]["actions"], 0);
    assert_eq!(json["metrics"]["quality"], "0");
}
#[test]
fn failures_have_nonzero_exit_codes_and_readable_diagnostics() {
    let case = Case::new();
    let bad = PROBLEM.replace("(:init (p))", "(:init)");
    let output = case.run(DOMAIN, &bad, PLAN, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("missing_support"));
    let output = case.run(DOMAIN, PROBLEM, PLAN, &["--max-work", "1", "--json"]);
    assert_eq!(output.status.code(), Some(4));
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["status"], "limit_exceeded");
    assert!(json.get("metrics").is_none());
    let output = case.run(DOMAIN, PROBLEM, "(", &["--json"]);
    assert_eq!(output.status.code(), Some(2));
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["diagnostics"][0]["location"]["file"], "plan.hddl");
}
#[test]
fn unsolvability_is_not_a_validated_plan() {
    let output = Case::new().run(
        DOMAIN,
        PROBLEM,
        "(define (plan s) (:domain d) (:problem p) (:unsolvable))",
        &["--json"],
    );
    assert_eq!(output.status.code(), Some(5));
}
