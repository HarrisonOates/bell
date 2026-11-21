# Backend comparison

Run the reproducible public comparison after a release build:

```sh
cargo build --locked --release
python3 scripts/benchmark_backends.py --output target/backend-benchmarks.json
```

The script runs each case seven times per backend and records every sample,
command and JSON report. Times include process startup, parsing, hierarchy checks
and execution validation. They are wall-clock medians, not isolated BDD timings.
Work counts are deterministic implementation counters, not states or time limits.

Example local results on 21 November 2026 (Linux x86-64; release build):

| Input | Strict MTC | Auto | Symbolic |
| --- | ---: | ---: | ---: |
| Public IPC 2023 Snake, 17 ordered actions | unsupported, 1.65 ms | valid, 1.80 ms | valid, 20.27 ms |
| Snake with conditional head updates, same certificate | unsupported, 2.29 ms | valid, 2.26 ms | valid, 38.19 ms |
| 26 unordered actions | unsupported, 0.79 ms | valid, 40.94 ms | valid, 41.95 ms |

These are small illustrative measurements on one machine, not a competition
performance claim. Re-run locally for comparisons after code changes.

## Interpreting the cases

The [public Snake fixture](../tests/fixtures/ipc2023-snake/README.md) comes from
[the IPC 2023 HTN domain collection](https://github.com/ipc2023-htn/ipc2023-domains/tree/main/total-order/Snake).
Even its original domain has state-dependent method preconditions, outside the
strict MTC backend. The derived domain also has conditional and universal effects.
Auto validates their total orders by direct replay. Forcing symbolic reachability
has overhead here, with no alternative primitive orders to share.

The [26-action input](../examples/benchmarks/unordered-26/) has two unordered
conditional toggles and 24 no-ops. Initially `p` and `q` are false. A toggle adds
`p` when it is false; when `p` is true it deletes `p` and adds `q`. Every order
therefore achieves `q`, but which occurrence produces it depends on the order.
The generalized modal proof does not settle this case. Auto falls through to
symbolic reachability, which represents the reachable sets without enumerating
the `26!` primitive orders individually.

An `unsupported` MTC result measures rejection of an input outside its fragment;
it does **not** measure validation or mean the plan is invalid. Strict `mtc` and
the sufficient generalized modal proof used inside `auto` are different paths.
The latter is incomplete and is always backed by an exact decision procedure.

To compare all backends on another certificate, including private inputs without
adding them to the repository:

```sh
python3 scripts/benchmark_backends.py --repeat 7 \
  --domain /path/domain.hddl --problem /path/problem.hddl --plan /path/plan.hddl \
  --output target/custom-backends.json
```

The script selects `--profile hddl-1.1` to measure execution without competition
eligibility filtering. Symbolic worst-case cost is still exponential, and BDD
size depends on the variable order. Bell imposes no arbitrary search cutoff.
