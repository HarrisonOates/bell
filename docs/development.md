# Developing Bell

Bell is a Rust library and CLI. Build and test with Rust 1.88 or newer; Python
3.10+ is needed only for the example, fixture and benchmark helpers. Dependencies
are pinned by `Cargo.lock`, including the HDDL parser revision in `Cargo.toml`.

```sh
cargo fmt --check
cargo test --locked
cargo clippy --locked --all-targets -- -D warnings
cargo build --locked --release
python3 scripts/test_validation_examples.py --backend auto
python3 scripts/test_validation_examples.py --backend symbolic
python3 scripts/check_conditional_fixture.py
```

The Python scripts use only the standard library and the built release binary.
Pass `--bell PATH` to use a different binary. The example runner checks expected
statuses, exit codes and diagnostic codes in `examples/validation/cases.json`.

## Test coverage

- `tests/validation.rs`: model, certificate, order, profile and metrics checks.
- `tests/conditions_effects.rs`: Boolean/quantified conditions, simultaneous
  conditional effects, unsupported constructs and method conditions.
- `tests/symbolic.rs`: exact backend, source counterexamples, history-sensitive
  checks, nested and empty methods, and wide unordered networks.
- `tests/oracle.rs`: small exhaustive comparisons against an independent literal
  execution model.
- `tests/adapter.rs`, `tests/cli.rs`: source adaptation, reports, locations and
  safe publication of converted certificates.
- Unit tests in `src/`: BDD truth tables, substitution, relational image and
  garbage collection; explicit primitive prefixes and method-check placements.
- `tests/public_fixture.rs`: a public IPC 2023 certificate, a conditional-effects
  transformation and a deliberately disabled effect.

The [Snake fixture](../tests/fixtures/ipc2023-snake/README.md) includes its source
licence, hashes and generation commands. Bowerbird was used to generate its saved
certificate; neither Bowerbird nor a grounder is required by Bell or its tests.
The Python checker independently compares every primitive action state with the
original domain, including active and inactive conditional guards. It is a small
fixture-specific interpreter, not another general HDDL validator.

For execution changes, use exhaustive small cases to test semantics and the
[benchmark script](benchmarks.md) to measure performance. Do not infer validity
from elapsed time, and distinguish an unsupported backend from a fast proof.

## Implementation and reports

Start with [the implementation guide](architecture.md) and `src/lib.rs`.
`cargo doc --no-deps` builds the public API reference. Use the structured
`Diagnostic` fields for failures; keep source occurrence IDs in counterexamples.
Internal check actions must not appear as submitted actions or change metrics.

When adding a feature, update the [language and backend descriptions](usage.md),
[diagnostic guide](diagnostics.md), and affected examples. Distinguish a malformed
input, unsupported language, invalid plan and profile rejection. A failed proof
heuristic must never reject a supported plan without an exact decision.

## Building the technical note

The checked-in PDF is generated from `output/pdf/bell-validation.tex`. Install a
LaTeX distribution with `latexmk`, `newtx`, `algorithm` and `algpseudocode`, then:

```sh
sh scripts/build_validation_note.sh
pdftoppm -png -scale-to 1600 output/pdf/bell-validation.pdf target/validation-note/page
```

Inspect every rendered page after changes. Intermediate LaTeX files stay under
`target/validation-note`; commit the source and final PDF together. LaTeX is not
a Bell runtime or Rust build dependency.

Bell's original code uses Apache-2.0; include the copyright/SPDX notice in new
source files. Preserve third-party notices and provenance when adding fixtures.
