# Runnable validation examples

There are **20 cases: 13 invalid and 7 valid controls**. The small examples are
standalone versions of Bell's existing regression tests, with each case's origin
recorded in [cases.json](cases.json). They are deliberately invalid examples, not
claims that a planner emitted bad output. The public IPC 2023 Snake fixture includes a saved planner certificate and a
derived conditional-effects model; its negative control changes that model
while keeping the certificate fixed.

From the repository root:

```sh
cargo build --locked --release
python3 scripts/test_validation_examples.py
```

The runner prints the expected scenario, actual diagnostic, occurrence and
counterexample when available. `PASS` means the result matched the expectation:
an intentionally invalid plan returning exit code 1 is a passing example.
The runner exits nonzero if any status, diagnostic code, or process exit code
differs from the expected result. All 20 cases are checked with both `auto` and `symbolic`.
See [the diagnostic guide](../../docs/diagnostics.md) for how to interpret failures.

List cases, print their commands, or select just a few:

```sh
python3 scripts/test_validation_examples.py --list
python3 scripts/test_validation_examples.py --commands hierarchy/unknown-method
python3 scripts/test_validation_examples.py --backend symbolic \
  action-order/unprotected-precondition conditional-goal/bad-goal \
  method-history/no-legal-placement
```

`--bell /path/to/bell` selects another build. The runner defaults to `auto`, which
uses direct replay for the totally ordered Snake fixture. To exercise exact
BDD reachability on the entire suite, including both Snake cases:

```sh
cargo build --locked --release
python3 scripts/test_validation_examples.py --bell target/release/bell --backend symbolic
```

## Cases worth starting with

Every small example directory contains its own `domain.hddl` and `problem.hddl`,
except `empty-method`, which has a valid and invalid initial-state problem file.

| Case | What fails | Symbolic diagnostic |
| --- | --- | --- |
| [`action-order/missing-order.hddl`](action-order/missing-order.hddl) | `use` may execute before `set` | `action_precondition` |
| [`action-order/unprotected-precondition.hddl`](action-order/unprotected-precondition.hddl) | `set < use` holds, but `clear` can occur between them | `action_precondition` |
| [`action-order/cycle.hddl`](action-order/cycle.hddl) | The submitted order is cyclic | `ordering_cycle` |
| [`conditional-goal/bad-goal.hddl`](conditional-goal/bad-goal.hddl) | `fire, set` executes, but the conditional effect never establishes the goal | `goal` |
| [`hierarchy/unknown-method.hddl`](hierarchy/unknown-method.hddl) | A named method does not exist | `unknown_method` |
| [`hierarchy/wrong-method-head.hddl`](hierarchy/wrong-method-head.hddl) | Method bindings target the wrong compound task | `method_head` |
| [`hierarchy/missing-decomposition.hddl`](hierarchy/missing-decomposition.hddl) | A compound occurrence is never expanded | `missing_decomposition` |
| [`hierarchy/leaf-mismatch.hddl`](hierarchy/leaf-mismatch.hddl) | Hierarchy and primitive network disagree about an occurrence's arguments | `leaf_mismatch` |
| [`hierarchy/orphan-action.hddl`](hierarchy/orphan-action.hddl) | An extra action is not produced by the hierarchy | `orphan_action` |
| [`hierarchy-order/missing-edge.hddl`](hierarchy-order/missing-edge.hddl) | An inherited order through an empty method is missing | `missing_hierarchy_order` |
| [`method-history/no-legal-placement.hddl`](method-history/no-legal-placement.hddl) | One permitted order never allows the method guard to hold | `method_precondition` |
| [`empty-method/false-guard-problem.hddl`](empty-method/false-guard-problem.hddl) with [`plan.hddl`](empty-method/plan.hddl) | A false method guard remains an obligation even with zero actions | `method_precondition` |
| [`Snake disabled-head-domain.hddl`](../../tests/fixtures/ipc2023-snake/disabled-head-domain.hddl) with the bundled problem and plan | Disabled conditional head updates make a later action fail | `action_precondition` |

`auto` can use the literal MTC and report `missing_support` or
`unresolved_threat` for the first two action-order cases. Force `symbolic` to get
an explicit failing prefix. Structural errors do not have execution prefixes.
Bell reports its first failure; this runner does not add per-stage progress
logging inside the validator.

Run one case directly, with Bell's normal human-readable output:

```sh
target/release/bell --profile hddl-1.1 --execution-backend symbolic \
  examples/validation/action-order/domain.hddl \
  examples/validation/action-order/problem.hddl \
  examples/validation/action-order/unprotected-precondition.hddl
```

The diagnostic is `action_precondition`, with failing prefix `s -> c -> u`.
Add `--json` to see status, source location, occurrence and counterexample fields.
The `hddl-1.1` profile lets these small partial-order examples use the default
length metric instead of being rejected by IPC's makespan-only PO restriction.

## PANDA's existing negative examples

The upstream parser also ships:

- [Transport with a wrong decomposition](https://github.com/panda-planner-dev/pandaPIparser/blob/master/tests/plan-for-transport-pfile01-wrong.txt).
- [Transport using a nonexistent method](https://github.com/panda-planner-dev/pandaPIparser/blob/master/tests/plan-for-transport-pfile01-non-existing-method.txt).
- [A valid Transport control](https://github.com/panda-planner-dev/pandaPIparser/blob/master/tests/plan-for-transport-pfile01.txt).

A matching Transport domain and problem are in the public
[IPC 2023 collection](https://github.com/ipc2023-htn/ipc2023-domains/tree/main/partial-order/Transport).
These older files need two explicit compatibility adjustments for Bell:

1. Append the missing closing `<==` marker to a copy of each raw plan.
2. Change the problem's `(:domain domain_htn)` reference to `(:domain transport)`
   to match the domain declaration.

With those adjustments and `--input-format panda`, the valid plan is accepted
(8 actions). The wrong plan is rejected by the adapter with
`source task constant mismatch`; the unknown-method plan is rejected with
`unknown source method m-drive`. Both are `input_error / panda_adapter`, before
native certificate validation. The `-notop` variant is accepted: omitting the
synthetic top task is not itself a failing example.

PANDA documents its `-verify`, `-vverify` and `-vvverify` output levels in the
[plan-format documentation](https://ipc2020.hierarchical-task.net/data/format.pdf).
Its legacy plan syntax differs from Bell's native HDDL 1.1 certificate format.
