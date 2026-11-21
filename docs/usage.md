# Using Bell

Bell validates one supplied certificate. It does not search for a plan, prove
optimality, or prove that a problem is unsolvable. It can validate output from any
planner that produces the supported source certificate format.

## Inputs and build

Build with Rust 1.88 or newer: `cargo build --locked --release`. Cargo downloads
the pinned parsing dependency and Rust crates on the first build. Subsequent
builds can use `--offline` if all dependencies are cached. No planner, grounder,
LaTeX installation, or Python package is required to build or use Bell.

```sh
target/release/bell domain.hddl problem.hddl plan.hddl
target/release/bell --json --execution-backend symbolic domain.hddl problem.hddl plan.hddl
```

Inputs are files, not stdin. Bell normalizes case, CRLF line endings and an
initial UTF-8 byte-order mark. Identifiers must be ASCII. The default input limit
is 16 MiB **per file**, adjustable with `--max-input-bytes BYTES`. There is no
execution work/time cutoff; a difficult exact check can take exponential work.
An externally killed process has produced no validation verdict.

## Certificates

A certificate contains the chosen decomposition and the submitted primitive
action network. All task and method arguments are ground objects. For example,
this is the [valid hierarchy example](../examples/validation/hierarchy/valid.hddl):

```lisp
(define (plan demo)
  (:domain d)
  (:problem p)
  (:decomposition
    (:root :subtasks (r (travel b)))
    (r (travel b) :method (route a b)
      :subtasks (x (move a b))))
  (:htn :ordered-tasks (x (move a b))))
```

Use the actual domain and problem names in your files; the plan name is arbitrary.

- Every occurrence has a unique ID. Repeated calls still need different IDs.
- `:root` lists the problem's initial tasks, with `:parameters (...)` when the
  initial network has parameters that need bindings.
- Each compound occurrence has one decomposition entry. Its `:method` supplies
  **all method parameters in declaration order**, including parameters absent
  from the method's task head.
- `:subtasks` lists children in source declaration order, even when they are
  unordered. This establishes the matching between the certificate and source.
- Primitive leaves appear exactly once in the plan's `:htn`, with identical IDs
  and calls. Primitive occurrences do not have decomposition entries.
- `:ordered-tasks (and ...)` denotes a sequence. `:tasks (and ...) :ordering
  (and (< a b) ...)` denotes a partial order. Use `()` for empty lists.
- The submitted order must already imply every primitive ordering inherited
  through the decomposition. Bell reports missing constraints instead of adding
  them to make the certificate pass.
- Method checks are internal. Do not insert synthetic guard actions into an
  HDDL certificate unless they are actual source-domain actions.

See [the example bundle](../examples/validation/README.md) for complete triples,
including empty methods and invalid decompositions. When a problem has no
initial task network, Bell checks the supplied actions and goal; its root can be
empty or list the primitive occurrences.

## Partial orders and backends

A partial order passes only if **all** its primitive linearizations execute and
reach the goal. For each such linearization, there must be **some** legal placement
of the method-precondition checks. Placements can differ between linearizations.
The existence of one successful action order is insufficient.

| Backend | Behaviour |
| --- | --- |
| `auto` (default) | Literal MTC where applicable, total-order replay, and a sufficient generalized modal proof; unresolved supported cases use exact symbolic reachability. |
| `symbolic` | Exact BDD reachability for every supported grounded input, including total orders; reconstructs concrete execution failures. |
| `mtc` | Restricted literal modal truth criterion: conjunctive action conditions and goal, unconditional effects, and static method conditions. Other inputs return `unsupported`. |

The generalized modal proof is sufficient but incomplete. Failure to prove a
plan there is not a rejection: `auto` continues to the exact check. The strict
`mtc` switch does not expose that generalized proof pass. For a detailed failing
execution, rerun a modal failure with `--execution-backend symbolic`.

`--profile ipc2027` is the default eligibility policy. It rejects a genuinely
partial order unless the objective is makespan. `--profile hddl-1.1` removes this
policy restriction; it does not weaken decomposition or execution checks. Totality
is determined from implied order, not the spelling of the task-list field.

## Supported language

Conditions support Boolean connectives (`and`, `or`, `not`, `imply`), equality,
and typed `forall`/`exists`. Effects support add/delete, `when`, and typed
`forall`. Quantifiers range over the finite typed object universe. Conditional
guards read the pre-action state; all active updates occur together, with adds
winning over deletes. Missing initial facts are false, and contradictory positive
and negative initial facts are rejected.

Costs are unconditional nonnegative integers. Individual numeric literals are
limited to `9223372036854775807`; sums use checked 128-bit arithmetic. General
numeric state updates, conditional costs, union (`either`) types, nondeterministic
effects, and temporal/durative actions are unsupported. Unused schemas and inactive
effect branches are still checked for language/model errors.

## Reports and exit codes

Bell reports the first failure. A successful JSON report looks like:

```json
{"schema_version":1,"validator_version":"0.1.0","status":"valid","work":123,
 "metrics":{"actions":3,"makespan":3,"cost":"3","objective":"length","quality":"3"},
 "diagnostics":[]}
```

`work` above is illustrative: it counts internal operations, not elapsed time or
states. It changes with implementation improvements and never stops a check.
`cost` and `quality` are decimal strings to preserve exact integers in JSON clients.
Metrics appear only on success. Makespan is the longest primitive chain under
unit durations; it is not the number of actions unless the order is total.

| Exit | Status | Meaning |
| ---: | --- | --- |
| 0 | `valid` | All requested checks passed. |
| 1 | `invalid_plan` | Certificate structure or some permitted execution fails. |
| 2 | `input_error` | Files, syntax, declarations, types, or adaptation are invalid. |
| 3 | `unsupported` | The language construct or chosen backend is unsupported. |
| 4 | `limit_exceeded` | Input size, parsing depth, or a supported integer/size range was exceeded. |
| 5 | `unsolvability_report` | The file claims unsolvability; Bell has not established it. |
| 6 | `internal_error` | An internal consistency check failed; report a bug. |
| 7 | `profile_rejected` | The plan violates the selected eligibility policy. |

A diagnostic includes `code`, `message`, and, when available, `occurrence`,
`location` (`file`, one-based `line` and `column`), and `counterexample` (occurrence
IDs in execution order). Locations use `domain`, `problem`, and `plan` as source
labels. Empty optional fields are omitted. See [diagnostics](diagnostics.md).

## PANDA-format adapter

```sh
target/release/bell --input-format panda --source-map problem.sas.map.json \
  --plan-output solution.hddl domain.hddl problem.hddl plan.raw
```

The adapter reconstructs a source certificate and invokes the same validator.
The optional version-1 source map records grounder transformations; it is not
needed for native HDDL certificates. Adapted output is sequential. Raw plans need
the `==>` / `<==` delimiters and a complete decomposition. A failure in generated
certificate text uses the source label `<adapted-plan>`.

`--plan-output` writes only after validation succeeds, uses an atomic replacement,
and refuses to overwrite an input file. An existing output file may be replaced
on success. Conversion is a convenience for planners emitting this format, not a
requirement for other competition entrants.

## Rust library

```rust
use bell::{validate, ExecutionBackend, Options, Profile, Status};

let options = Options {
    profile: Profile::Hddl11,
    execution_backend: ExecutionBackend::Symbolic,
    ..Options::default()
};
let report = validate(domain_text, problem_text, plan_text, &options);
assert_eq!(report.status, Status::Valid);
```

`validate` accepts three source strings and returns a `Report`. The adapter API is
in `bell::adapter`; `cargo doc --no-deps` builds API documentation locally.
