use clap::Parser;
use htn_plan_validation::{Diagnostic, Options, Profile, Report, Status, validate};
use std::{
    fs::File,
    io::Read,
    path::{Path, PathBuf},
    process::ExitCode,
    time::Duration,
};

#[derive(Parser)]
#[command(
    name = "bell",
    version,
    about = "Validate IPC HTN plans against domain and problem files",
    after_help = "Supports conjunctive conditions and unconditional effects. Disjunctions, conditional effects, existential conditions, and (either ...) types are currently unsupported.\nCost literals must be integers in 0..=9223372036854775807; sums use exact 128-bit arithmetic."
)]
struct Args {
    domain: PathBuf,
    problem: PathBuf,
    plan: PathBuf,
    #[arg(long, help = "Emit a structured JSON report")]
    json: bool,
    #[arg(long,default_value="ipc2027",value_parser=["ipc2027","hddl-1.1"])]
    profile: String,
    #[arg(long,default_value_t=10_000_000,value_parser=clap::value_parser!(u64).range(1..))]
    max_work: u64,
    #[arg(long,value_name="SECONDS",value_parser=clap::value_parser!(u64).range(1..))]
    timeout: Option<u64>,
    #[arg(long, default_value_t = 16_777_216, value_name = "BYTES")]
    max_input_bytes: usize,
}

fn failure(status: Status, code: &str, message: String) -> Diagnostic {
    Diagnostic {
        status,
        code: code.into(),
        message,
        location: None,
        occurrence: None,
        counterexample: vec![],
    }
}
fn read(path: &Path, limit: usize) -> Result<String, Diagnostic> {
    let mut source = vec![];
    let result = (|| {
        File::open(path)?
            .take((limit as u64).saturating_add(1))
            .read_to_end(&mut source)
    })();
    result.map_err(|e| failure(Status::InputError, "io", format!("{}: {e}", path.display())))?;
    if source.len() > limit {
        return Err(failure(
            Status::LimitExceeded,
            "input_size",
            format!("{} exceeds the input size limit", path.display()),
        ));
    }
    String::from_utf8(source).map_err(|_| {
        failure(
            Status::InputError,
            "encoding",
            format!("{} is not UTF-8", path.display()),
        )
    })
}
fn main() -> ExitCode {
    let args = Args::parse();
    let options = Options {
        profile: if args.profile == "ipc2027" {
            Profile::Ipc2027
        } else {
            Profile::Hddl11
        },
        max_work: args.max_work,
        timeout: args.timeout.map(Duration::from_secs),
        max_input_bytes: args.max_input_bytes,
    };
    let sources = (|| {
        Ok::<_, Diagnostic>((
            read(&args.domain, options.max_input_bytes)?,
            read(&args.problem, options.max_input_bytes)?,
            read(&args.plan, options.max_input_bytes)?,
        ))
    })();
    let mut report = match sources {
        Ok((d, p, s)) => validate(&d, &p, &s, &options),
        Err(e) => Report {
            schema_version: 1,
            validator_version: env!("CARGO_PKG_VERSION"),
            status: e.status,
            work: 0,
            metrics: None,
            diagnostics: vec![e],
        },
    };
    for d in &mut report.diagnostics {
        if let Some(l) = &mut d.location {
            let path = match l.file.as_str() {
                "domain" => Some(&args.domain),
                "problem" => Some(&args.problem),
                "plan" => Some(&args.plan),
                _ => None,
            };
            if let Some(path) = path {
                l.file = path.display().to_string();
            }
        }
    }
    if args.json {
        println!(
            "{}",
            serde_json::to_string(&report).expect("report serialization")
        );
    } else if let Some(m) = &report.metrics {
        println!(
            "valid: {} actions, cost {}, makespan {}",
            m.actions, m.cost, m.makespan
        );
    } else {
        for d in &report.diagnostics {
            eprintln!("{d}");
        }
    }
    ExitCode::from(report.status.exit_code())
}
