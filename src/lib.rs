// Copyright 2026 Harrison Oates
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub mod adapter;
mod boolean;
mod encoding;
mod execution;
mod hierarchy;
mod input;
mod modal;
mod model;
mod order;
mod plan;
mod report;
mod symbolic;
mod work;

use hddl_analyzer::{AbstractSyntaxTree, LexicalAnalyzer, Parser};
use model::{Bindings, Model, Objective};
use report::Result;
pub use report::{Diagnostic, Location, Metrics, Report, Status};
use work::Work;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Profile {
    #[default]
    Ipc2027,
    Hddl11,
}

/// Execution proof strategy. Symbolic is complete for every supported grounded
/// input; Mtc is restricted to literal conditions and static method guards.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ExecutionBackend {
    #[default]
    Auto,
    Symbolic,
    Mtc,
}

#[derive(Clone, Debug)]
pub struct Options {
    pub profile: Profile,
    pub execution_backend: ExecutionBackend,
    pub max_input_bytes: usize,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            profile: Profile::Ipc2027,
            execution_backend: ExecutionBackend::Auto,
            max_input_bytes: 16 * 1024 * 1024,
        }
    }
}

/// Validate three source documents. Method checks are internal; no artificial
/// actions or planner-specific metadata are required in the submitted plan.
pub fn validate(domain: &str, problem: &str, plan: &str, options: &Options) -> Report {
    let mut work = Work::default();
    let outcome = validate_inner(domain, problem, plan, options, &mut work);
    match outcome {
        Ok(metrics) => Report {
            schema_version: 1,
            validator_version: env!("CARGO_PKG_VERSION"),
            status: Status::Valid,
            work: work.used,
            metrics: Some(metrics),
            diagnostics: vec![],
        },
        Err(error) => Report {
            schema_version: 1,
            validator_version: env!("CARGO_PKG_VERSION"),
            status: error.status,
            work: work.used,
            metrics: None,
            diagnostics: vec![error],
        },
    }
}

fn validate_inner(
    domain: &str,
    problem: &str,
    plan: &str,
    options: &Options,
    work: &mut Work,
) -> Result<Metrics> {
    for (name, source) in [("domain", domain), ("problem", problem), ("plan", plan)] {
        if source.len() > options.max_input_bytes {
            return Err(Diagnostic::new(
                Status::LimitExceeded,
                "input_size",
                format!("{name} exceeds the input size limit"),
            ));
        }
    }
    let normalize = |s: &str| {
        s.strip_prefix('\u{feff}')
            .unwrap_or(s)
            .replace('\r', "")
            .to_ascii_lowercase()
            .into_bytes()
    };
    let domain = normalize(domain);
    let mut problem = normalize(problem);
    let plan = normalize(plan);
    let domain_syntax = input::document(&domain, "domain", work)?;
    let problem_syntax = input::document(&problem, "problem", work)?;
    input::model_syntax(&domain_syntax)?;
    input::model_syntax(&problem_syntax)?;
    let negative_init = input::initial_polarities(&problem_syntax, &mut problem)?;
    let domain_source = input::ParserSource::new(&domain_syntax, &domain, work)?;
    let problem_source = input::ParserSource::new(&problem_syntax, &problem, work)?;
    let negative_init = negative_init
        .into_iter()
        .map(|position| problem_source.shifted_position(position))
        .collect();
    let goal_location = problem_syntax
        .children
        .iter()
        .find(|n| n.head() == ":goal")
        .map(|n| n.location.clone());
    let plan = plan::Plan::parse(&input::document(&plan, "plan", work)?)?;
    let domain = match Parser::new(LexicalAnalyzer::with_tab_width(&domain_source.bytes, 1))
        .parse()
        .map_err(|e| domain_source.restore_error(input::parser_error("domain", e)))?
    {
        AbstractSyntaxTree::Domain(d) => d,
        _ => {
            return Err(Diagnostic::input(
                "document_kind",
                "domain file contains a problem",
            ));
        }
    };
    let problem = match Parser::new(LexicalAnalyzer::with_tab_width(&problem_source.bytes, 1))
        .parse()
        .map_err(|e| problem_source.restore_error(input::parser_error("problem", e)))?
    {
        AbstractSyntaxTree::Problem(p) => p,
        _ => {
            return Err(Diagnostic::input(
                "document_kind",
                "problem file contains a domain",
            ));
        }
    };
    work.tick();
    let model =
        Model::new(&domain, &problem, &negative_init, work).map_err(|error| {
            match error.location.as_ref().map(|l| l.file.as_str()) {
                Some("domain") => domain_source.restore_error(error),
                Some("problem") => problem_source.restore_error(error),
                _ => error,
            }
        })?;
    if plan.domain != domain.name || plan.problem != problem.name {
        return Err(Diagnostic::invalid(
            "plan_identity",
            "plan domain/problem names do not match the inputs",
        ));
    }
    if plan.unsolvable {
        return Err(Diagnostic::new(
            Status::UnsolvabilityReport,
            "unsolvability_unverified",
            "file reports unsolvability; bell does not prove unsolvability",
        ));
    }
    let certificate = hierarchy::build(&model, &plan, work)?;
    if options.profile == Profile::Ipc2027
        && model.objective != Objective::Makespan
        && !certificate.order.total()
    {
        return Err(Diagnostic::new(
            Status::ProfileRejected,
            "partial_order_profile",
            "IPC accepts partially ordered output only for makespan; use --profile hddl-1.1 to check language validity",
        ));
    }
    let goal = model.condition(problem.goal.as_ref(), &Bindings::new(), work)?;
    execution::validate(&model, &certificate, &goal, options.execution_backend, work).map_err(
        |mut e| {
            if e.location.is_none()
                && let Some(id) = &e.occurrence
            {
                e.location = plan
                    .actions
                    .iter()
                    .find(|o| &o.id == id)
                    .map(|o| Box::new(o.location.clone()))
                    .or_else(|| {
                        plan.decompositions
                            .get(id)
                            .map(|d| Box::new(d.task.location.clone()))
                    });
            }
            if e.location.is_none() && e.occurrence.as_deref() == Some("goal") {
                e.location = goal_location.clone().map(Box::new);
            }
            e
        },
    )?;
    let count = certificate.actions.len();
    let cost = certificate.actions.iter().try_fold(0_u128, |sum, a| {
        sum.checked_add(a.cost).ok_or_else(|| {
            Diagnostic::new(
                Status::LimitExceeded,
                "cost_overflow",
                "plan cost exceeds the supported integer range",
            )
        })
    })?;
    let makespan = certificate.order.makespan();
    let (objective, quality) = match model.objective {
        Objective::Length => ("length", count.to_string()),
        Objective::Cost => ("total-cost", cost.to_string()),
        Objective::Makespan => ("makespan", makespan.to_string()),
    };
    Ok(Metrics {
        actions: count,
        makespan,
        cost: cost.to_string(),
        objective: objective.into(),
        quality,
    })
}
