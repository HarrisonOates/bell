use bell::{Diagnostic, ExecutionBackend, Options, Profile, Report, Status, validate};
use clap::{Parser, ValueEnum};
use std::{
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
    process::ExitCode,
};

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum InputFormat {
    Hddl,
    Panda,
}

#[derive(Parser)]
#[command(
    name = "bell",
    version,
    about = "Validate IPC HTN plans against domain and problem files",
    after_help = "Supports Boolean and quantified conditions, and unconditional, conditional, and universal effects. Partial-order execution checking may be exponential and runs to completion without work or time cutoffs. Union (either ...) types and nondeterministic effects are unsupported.\nCost literals must be integers in 0..=9223372036854775807; sums use exact 128-bit arithmetic."
)]
struct Args {
    domain: PathBuf,
    problem: PathBuf,
    plan: PathBuf,
    #[arg(
        long,
        value_enum,
        default_value = "hddl",
        help = "Read HDDL 1.1 or adapt raw PANDA-format output"
    )]
    input_format: InputFormat,
    #[arg(long, help = "Version 1 reconstruction map for raw PANDA input")]
    source_map: Option<PathBuf>,
    #[arg(
        long,
        help = "Atomically write the HDDL 1.1 plan after successful validation"
    )]
    plan_output: Option<PathBuf>,
    #[arg(long, help = "Emit a structured JSON report")]
    json: bool,
    #[arg(long,default_value="ipc2027",value_parser=["ipc2027","hddl-1.1"])]
    profile: String,
    #[arg(long, default_value = "auto", value_parser = ["auto", "symbolic", "mtc"],
        help = "Execution backend: modal fast paths plus exact reachability, exact reachability alone, or restricted literal MTC")]
    execution_backend: String,
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
fn publish(path: &Path, text: &str, inputs: &[&Path]) -> Result<(), Diagnostic> {
    let io_error = |e| {
        failure(
            Status::InputError,
            "plan_output",
            format!("{}: {e}", path.display()),
        )
    };
    if let Ok(destination) = path.canonicalize() {
        for input in inputs {
            if input.canonicalize().ok().as_ref() == Some(&destination) {
                return Err(failure(
                    Status::InputError,
                    "plan_output",
                    "output must differ from the input files".into(),
                ));
            }
        }
    }
    let name = path.file_name().ok_or_else(|| {
        failure(
            Status::InputError,
            "plan_output",
            "output needs a file name".into(),
        )
    })?;
    let temporary = path.with_file_name(format!(
        ".{}.{}.tmp",
        name.to_string_lossy(),
        std::process::id()
    ));
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&temporary)
        .map_err(io_error)?;
    let result = (|| {
        file.write_all(text.as_bytes())?;
        file.sync_all()?;
        drop(file);
        fs::rename(&temporary, path)
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result.map_err(io_error)
}

fn run(args: &Args, options: &Options) -> Result<Report, Diagnostic> {
    let domain = read(&args.domain, options.max_input_bytes)?;
    let problem = read(&args.problem, options.max_input_bytes)?;
    let input = read(&args.plan, options.max_input_bytes)?;
    if args.source_map.is_some() && args.input_format != InputFormat::Panda {
        return Err(failure(
            Status::InputError,
            "source_map",
            "--source-map requires --input-format panda".into(),
        ));
    }
    let mut work = 0;
    let plan = if args.input_format == InputFormat::Panda {
        let source_map = args
            .source_map
            .as_ref()
            .map(|p| read(p, options.max_input_bytes))
            .transpose()?;
        let adapted =
            bell::adapter::from_panda(&domain, &problem, &input, source_map.as_deref(), options)?;
        work = adapted.work;
        adapted.text
    } else {
        input
    };
    let mut report = validate(&domain, &problem, &plan, options);
    report.work = report.work.saturating_add(work);
    if args.input_format == InputFormat::Panda {
        for diagnostic in &mut report.diagnostics {
            if let Some(location) = &mut diagnostic.location
                && location.file == "plan"
            {
                location.file = "<adapted-plan>".into();
            }
        }
    }
    if report.status == Status::Valid
        && let Some(path) = &args.plan_output
    {
        let mut inputs = vec![
            args.domain.as_path(),
            args.problem.as_path(),
            args.plan.as_path(),
        ];
        if let Some(map) = &args.source_map {
            inputs.push(map);
        }
        publish(path, &plan, &inputs)?;
    }
    Ok(report)
}

fn main() -> ExitCode {
    let args = Args::parse();
    let options = Options {
        profile: if args.profile == "ipc2027" {
            Profile::Ipc2027
        } else {
            Profile::Hddl11
        },
        max_input_bytes: args.max_input_bytes,
        execution_backend: match args.execution_backend.as_str() {
            "symbolic" => ExecutionBackend::Symbolic,
            "mtc" => ExecutionBackend::Mtc,
            _ => ExecutionBackend::Auto,
        },
    };
    let mut report = match run(&args, &options) {
        Ok(report) => report,
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
