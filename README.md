# Bell

Bell is a planner-independent HTN plan validator. Given a domain, problem, and
HDDL 1.1 certificate, it checks the decomposition and **every permitted action
linearization**, including method preconditions, conditional effects, and goals.

## Build and run

Requires Rust 1.88 or newer. The first build downloads Cargo dependencies.

```sh
cargo build --locked --release
target/release/bell domain.hddl problem.hddl plan.hddl
```

Add `--json` for a structured report. Use `--execution-backend symbolic` to run
exact BDD reachability directly; the default `auto` also uses faster proofs and
sequential replay where applicable. The default `ipc2027` profile accepts partial
orders only for makespan; `--profile hddl-1.1` checks language validity without
that competition restriction. Run `target/release/bell --help` for all options.

PANDA-format output can be adapted and validated with:

```sh
target/release/bell --input-format panda --plan-output solution.hddl \
  domain.hddl problem.hddl plan.raw
```

The converted certificate is written only after successful validation.

## Examples and documentation

```sh
cargo test --locked
python3 scripts/test_validation_examples.py --bell target/release/bell --backend symbolic
```

- [Usage, certificate format, and JSON reports](docs/usage.md)
- [Why a plan failed](docs/diagnostics.md) and [runnable examples](examples/validation/README.md)
- [Implementation](docs/architecture.md) and [symbolic validation note (PDF)](output/pdf/bell-validation.pdf)
- [Development and testing](docs/development.md), [backend benchmarks](docs/benchmarks.md)

## License

Copyright 2026 Harrison Oates. Bell's original code is licensed under the
[Apache License 2.0](LICENSE); see [NOTICE](NOTICE). Bundled third-party benchmark
files retain their separately stated [MIT licence](tests/fixtures/ipc2023-snake/LICENSE).
