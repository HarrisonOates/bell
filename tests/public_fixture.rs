// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0

use bell::{ExecutionBackend, Options, Status, validate};

// Public IPC 2023 Snake inputs. Generation provenance is bundled, but no
// planner, grounder, or source-map installation is needed to run these tests.
const DOMAIN: &str = include_str!("fixtures/ipc2023-snake/domain.hddl");
const CONDITIONAL: &str = include_str!("fixtures/ipc2023-snake/conditional-domain.hddl");
const DISABLED: &str = include_str!("fixtures/ipc2023-snake/disabled-head-domain.hddl");
const PROBLEM: &str = include_str!("fixtures/ipc2023-snake/problem.hddl");
const PLAN: &str = include_str!("fixtures/ipc2023-snake/plan.hddl");

#[test]
fn public_certificate_validates_with_original_and_conditional_effects() {
    for backend in [ExecutionBackend::Auto, ExecutionBackend::Symbolic] {
        let options = Options {
            execution_backend: backend,
            ..Options::default()
        };
        for domain in [DOMAIN, CONDITIONAL] {
            let report = validate(domain, PROBLEM, PLAN, &options);
            assert_eq!(report.status, Status::Valid, "{report:#?}");
            let metrics = report.metrics.unwrap();
            assert_eq!(metrics.actions, 17);
            assert_eq!(metrics.makespan, 17);
            assert_eq!(metrics.cost, "17");
        }
    }
}

#[test]
fn disabled_conditional_head_update_produces_an_action_counterexample() {
    for backend in [ExecutionBackend::Auto, ExecutionBackend::Symbolic] {
        let options = Options {
            execution_backend: backend,
            ..Options::default()
        };
        let report = validate(DISABLED, PROBLEM, PLAN, &options);
        assert_eq!(report.status, Status::InvalidPlan, "{report:#?}");
        assert_eq!(report.diagnostics[0].code, "action_precondition");
        assert!(!report.diagnostics[0].counterexample.is_empty());
    }
}
