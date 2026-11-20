# bell

A planner-independent Rust validator for IPC 2027 HTN solution
certificates in HDDL 1.1, named **bell**.

bell accepts domain, problem, and plan files and returns validation results
with diagnostics. HDDL-Parser provides tokenization and domain/problem parsing;
the plan reader, validation library, CLI, diagnostics, and metrics live here.

```sh
cargo build --release
target/release/bell domain.hddl problem.hddl plan.hddl
target/release/bell --json domain.hddl problem.hddl plan.hddl
```

Validation checks the decomposition from the root, inherited ordering, the modal
truth criterion, and method preconditions. Method checks are internal and need
no artificial actions in the plan. Without an initial HTN, bell checks execution
and the goal. Subtask lists currently map to source declaration order.

The default `ipc2027` profile permits partial orders only for makespan problems.
Use `--profile hddl-1.1` to check partial orders under other metrics.

The initial scope covers conjunctive conditions and unconditional effects.
Disjunctions, conditional effects, existential conditions, and union types produce
explicit unsupported-feature diagnostics. Integer literals are limited by the
parsing dependency to 0 through 9223372036854775807; sums use exact 128-bit
arithmetic. Dynamic method checks may explore exponentially many prefixes;
`--max-work` and `--timeout` produce a limit outcome, never a valid result.

## PANDA-format adapter

Bell can reconstruct an HDDL 1.1 solution directly from raw
PANDA-format planner output, without invoking `pandaPIparser -c`:

```sh
bell --input-format panda --plan-output solution.hddl \
  domain.hddl problem.hddl plan.raw
bell --json --input-format panda --plan-output solution.hddl \
  domain.hddl problem.hddl plan.raw
```

The adapter expands compressed methods/actions, contracts generated tasks,
preserves repeated occurrence IDs and empty methods, and recovers root and
method parameters in source declaration order. Missing parameter bindings are
searched over typed source objects, using method guards and the action sequence.
The input must contain one complete `==>` / `root` / `<==` block; diagnostic
lines outside it are allowed. Timed `@...` action records are rejected.

The reconstruction module constructs a candidate certificate. The existing
planner-independent validator then checks that candidate against the original
domain and problem. Only a `valid` result writes `--plan-output`, using an atomic
replacement. Failures preserve an existing output file. JSON and text validation
reports retain their usual behavior. Input files cannot be used as the output.

For a frontend that emits a version 1 reconstruction map, supply that map
instead of interpreting PANDA compiler names:

```sh
bell --input-format panda --source-map problem.sas.map.json \
  --plan-output solution.hddl domain.hddl problem.hddl plan.raw
```

The map must contain the exact supplied domain and problem text. Source inputs
are still required because grounded output omits parameter declarations and
bindings. Reconstruction and validation share `--max-work` and `--timeout`;
`--max-input-bytes` also applies to the map and raw plan. This adapter emits
sequential plans for TO or PO source problems, within Bell's supported language
fragment. It does not infer unsolvability from missing output or search logs.

The library entry point is `adapter::from_panda`. Its `AdaptedPlan` is a candidate
with a reconstruction work count; library callers must pass its text to
`validate` before treating it as a valid solution.
