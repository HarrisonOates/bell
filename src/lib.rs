pub mod adapter;
mod budget;
mod execution;
mod hierarchy;
mod input;
mod model;
mod order;
mod plan;
mod report;

use budget::Budget;
use hddl_analyzer::{AbstractSyntaxTree, LexicalAnalyzer, Parser};
use model::{Bindings, Model, Objective};
use report::Result;
pub use report::{Diagnostic, Location, Metrics, Report, Status};
use std::time::Duration;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Profile {
    #[default]
    Ipc2027,
    Hddl11,
}

#[derive(Clone, Debug)]
pub struct Options {
    pub profile: Profile,
    pub max_work: u64,
    pub timeout: Option<Duration>,
    pub max_input_bytes: usize,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            profile: Profile::Ipc2027,
            max_work: 10_000_000,
            timeout: None,
            max_input_bytes: 16 * 1024 * 1024,
        }
    }
}

/// Validate three source documents. Method checks are internal; no artificial
/// actions or planner-specific metadata are required in the submitted plan.
pub fn validate(domain: &str, problem: &str, plan: &str, options: &Options) -> Report {
    let mut budget = Budget::new(options.max_work, options.timeout);
    let outcome = validate_inner(domain, problem, plan, options, &mut budget);
    match outcome {
        Ok(metrics) => Report {
            schema_version: 1,
            validator_version: env!("CARGO_PKG_VERSION"),
            status: Status::Valid,
            work: budget.used,
            metrics: Some(metrics),
            diagnostics: vec![],
        },
        Err(error) => Report {
            schema_version: 1,
            validator_version: env!("CARGO_PKG_VERSION"),
            status: error.status,
            work: budget.used,
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
    budget: &mut Budget,
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
    let domain_syntax = input::document(&domain, "domain", budget)?;
    let problem_syntax = input::document(&problem, "problem", budget)?;
    input::model_syntax(&domain_syntax)?;
    input::model_syntax(&problem_syntax)?;
    let negative_init = input::initial_polarities(&problem_syntax, &mut problem)?;
    let goal_location = problem_syntax
        .children
        .iter()
        .find(|n| n.head() == ":goal")
        .map(|n| n.location.clone());
    let plan = plan::Plan::parse(&input::document(&plan, "plan", budget)?)?;
    let domain = match Parser::new(LexicalAnalyzer::with_tab_width(&domain, 1))
        .parse()
        .map_err(|e| input::parser_error("domain", e))?
    {
        AbstractSyntaxTree::Domain(d) => d,
        _ => {
            return Err(Diagnostic::input(
                "document_kind",
                "domain file contains a problem",
            ));
        }
    };
    let problem = match Parser::new(LexicalAnalyzer::with_tab_width(&problem, 1))
        .parse()
        .map_err(|e| input::parser_error("problem", e))?
    {
        AbstractSyntaxTree::Problem(p) => p,
        _ => {
            return Err(Diagnostic::input(
                "document_kind",
                "problem file contains a domain",
            ));
        }
    };
    budget.tick()?;
    let model = Model::new(&domain, &problem, &negative_init, budget)?;
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
    let certificate = hierarchy::build(&model, &plan, budget)?;
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
    let goal = model.condition(problem.goal.as_ref(), &Bindings::new(), budget)?;
    execution::validate(&model, &certificate, &goal, budget).map_err(|mut e| {
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
    })?;
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
