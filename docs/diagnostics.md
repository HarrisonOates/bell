# Understanding a failed validation

Start with the status and diagnostic code. `invalid_plan` means Bell found a
certificate or execution failure. `unsupported`, `input_error`, and
`profile_rejected` describe different problems; none is a proof that the planning
problem has no solution. Bell stops at its first failure, so fixing it may reveal
another. All statuses and exit codes are listed in [usage](usage.md#reports-and-exit-codes).

## Read an execution counterexample

Run the bundled threat example:

```sh
target/release/bell --profile hddl-1.1 --execution-backend symbolic \
  examples/validation/action-order/domain.hddl \
  examples/validation/action-order/problem.hddl \
  examples/validation/action-order/unprotected-precondition.hddl
```

The plan orders `s` (set `ready`) before `u` (require `ready`), but leaves `c`
(clear `ready`) unordered. Bell reports `action_precondition`, occurrence `u`,
and the failing prefix `s -> c -> u`. `s` succeeds; `c` succeeds; `u` cannot run.
The alternative `s -> u -> c` succeeding does not make this partial order valid.
Constrain the intended order in the submitted certificate, then validate again.

For action and prerequisite-method failures, the last ID in the prefix is the
action that cannot execute. For goal or final method-placement failures, the
prefix can be the complete action sequence. Look up IDs in `:htn` to recover
ground calls. Symbolic witnesses are replayed concretely before being reported.
Internal method checks are omitted from the trace.

Conditional effects require particular care: evaluate **every guard against the
same state before the action**. Accumulate active additions and deletions, then
apply them together. A delete in one effect does not disable another effect's
guard during that action. Adds win if both sets contain the same fact.

## Execution failures

| Code | What to inspect | Typical correction |
| --- | --- | --- |
| `action_precondition` | The failing occurrence's ground precondition and the state after the preceding prefix. The message does not currently enumerate false subformulas. | Supply support, remove a threat through ordering, or correct the action's arguments. |
| `method_precondition` | The chosen method, its bindings, predecessor/successor constraints, and whether its condition ever holds in its legal interval. Empty methods still need a valid check. | Correct the method/bindings, establish its condition within the interval, or change permitted action orders. |
| `goal` | The state after the complete prefix and the problem's `:goal`. | Ensure the final effects establish every required part of the goal in all orders. |
| `missing_support` | Literal MTC found no guaranteed initial support or ordered producer for a condition. | Inspect the consumer and missing literal; rerun with `symbolic` for an execution witness. |
| `unresolved_threat` | Literal MTC found a possible destroyer without a guaranteed intervening restorer. | Check producer, destroyer, consumer and order; rerun with `symbolic` for a witness. |
| `false_condition` | A conjunctive-backend condition simplifies to false. | Inspect contradictory or constant-false conditions and bindings. |

A method condition need not hold immediately before its first primitive child.
It can have been checked earlier and subsequently destroyed. Conversely, a child
method cannot be checked before its parent or before an ordered preceding task
finishes. A valid decomposition shape alone does not establish these conditions.

## Decomposition and ordering failures

| Code(s) | Meaning and next step |
| --- | --- |
| `plan_identity` | The plan's domain/problem names do not match the source files. Check you supplied the matching triple. |
| `unknown_method`, `unknown_task` | A named source schema does not exist. Check spellings and whether compiled names leaked into the source certificate. |
| `method_head`, `decomposition_task` | Ground method bindings decompose a different task, or an entry's head differs from the introduced occurrence. Check parameter order. |
| `subtask_count`, `subtask_mismatch` | Children do not match the selected method or initial network. Preserve source declaration order and supply all children. |
| `leaf_mismatch`, `missing_action` | A primitive leaf differs between decomposition and `:htn`, or is absent from `:htn`. Match both ID and grounded call. |
| `missing_decomposition` | A compound occurrence has no expansion. Add the chosen method and its children. |
| `primitive_decomposition` | A primitive occurrence was expanded as if it were compound. Remove that entry. |
| `orphan_action`, `orphan_decomposition` | An occurrence/entry cannot be reached from the problem's roots. Check IDs and the intended root network. |
| `duplicate_action_id`, `duplicate_decomposition`, `duplicate_introduction` | IDs or expansions are reused, a child is shared, or the decomposition is cyclic. Use distinct occurrences for repeated calls. |
| `unexpected_decomposition` | The problem has no initial HTN but the plan supplies compound expansions or root bindings. Check the problem file. |
| `ordering_reference` | An ordering endpoint does not name a submitted primitive occurrence. Use its occurrence ID, not its action schema name. |
| `ordering_cycle` | No linearization exists. Remove contradictory edges; an empty set of executions is not accepted vacuously. |
| `missing_hierarchy_order` | The submitted action order omits an implication of the chosen hierarchy, possibly through an empty method. Add the required edge or choose the intended decomposition. |

Structural failures occur before execution checking and generally have no
execution prefix. A source location points to the relevant declaration or
occurrence when available.

## Input, profile, and adapter failures

Syntax/parse diagnostics identify malformed documents, unmatched parentheses,
missing fields, or unsupported tokens. Model diagnostics identify undeclared
objects/types/predicates, incorrect argument counts or types, unbound parameters,
duplicate declarations, inconsistent initial facts, and invalid metric/cost
declarations. Inspect the reported source location and message before changing
the plan: Bell validates unused schemas too.

- `partial_order_profile`: use a total-order certificate for the current
  competition objective, or use `--profile hddl-1.1` when you intend a language-only
  check. Do not treat that latter result as competition eligibility.
- `unsupported_feature`: read the message. If it concerns strict MTC, use `auto`
  or `symbolic`. If it concerns unsupported language, changing backends cannot
  make that feature supported.
- `input_size`: adjust `--max-input-bytes` if the file is intentionally larger.
  Integer-range, cost-overflow and nesting-limit errors concern representation
  limits, not an execution search budget.
- `unsolvability_unverified`: Bell does not certify an unsolvability claim.
- PANDA adaptation errors: check the raw delimiters, source files and optional
  reconstruction map belong to the same run. Preserve original method parameters
  and compiled-action provenance. Native HDDL input avoids reconstruction.
- `symbolic_invariant` / `internal_error`: retain all three inputs, the command,
  Bell revision/version and complete report when filing a bug.

## Reproducing and reporting a problem

Use `--json` to retain structured diagnostics. Include the exact command,
domain, problem, certificate, and any map used for adaptation. Also record
`bell --version` and the Git revision. Minimize an example only while preserving
the same failure. Do not publish private competition domains or other confidential
inputs in a public issue; use an agreed private channel or a synthetic reproducer.

The [example runner](../examples/validation/README.md) prints the intended
failure, actual code, occurrence and counterexample. It checks expected failures
as well as valid controls; `PASS` means the observed verdict is the expected one.
