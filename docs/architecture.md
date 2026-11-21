# How Bell validates a certificate

Bell owns the validation semantics. The external HDDL parser supplies syntax
trees; no planner's validator is linked or invoked. The complete Boolean
execution algorithm is described in the [technical note](../output/pdf/bell-validation.pdf)
and its [LaTeX source](../output/pdf/bell-validation.tex).

## Pipeline and source map

| Component | Responsibility |
| --- | --- |
| `src/main.rs` | Read files, select options, print reports, exit codes, and atomically publish validated converted plans. |
| `src/input.rs`, `src/plan.rs` | Check document structure, adapt parser-facing syntax while preserving source locations, and parse the certificate. |
| `src/model.rs` | Validate symbols, types, schemas, conditions, effects and metrics; ground the supplied calls and finite quantifiers. |
| `src/hierarchy.rs` | Match roots and each chosen method, reject missing/shared/orphan occurrences, and verify inherited ordering. |
| `src/order.rs` | DAG validation, topological order, reachability, totality and unit-duration makespan. |
| `src/execution.rs` | Backend selection, literal MTC, concrete replay, and a test-only explicit prefix reference. |
| `src/symbolic.rs` | Exact layered BDD reachability, internal method checks, and counterexample reconstruction. |
| `src/encoding.rs`, `src/boolean.rs` | Boolean conditions, simultaneous conditional updates, and an iterative reduced ordered BDD manager. |
| `src/modal.rs` | Optional sufficient generalized modal proof using regression, support, preservation and restoration. |
| `src/adapter/` | Optional PANDA output reconstruction; the result still passes through the source validator. |
| `src/report.rs`, `src/work.rs` | Structured diagnostics/metrics and informational work accounting. |
| `src/lib.rs` | Public `validate` API, orchestration, policy checks and metric reporting. |

The hierarchy pass establishes structural derivability and checks that the
submitted primitive order implies inherited constraints. It does not strengthen
the submitted order to rescue a bad plan. State-dependent method preconditions
remain execution obligations.

## Symbolic configurations

The exact backend retains dynamic facts, primitive completion bits, and completion
bits for nontrivial method checks. A check has no world effects: it records that
its condition held after its predecessors completed. Its bit persists even if a
later action destroys the condition. Facts outside the conservative write set
are folded to constants. True auxiliary events and completion markers are
contracted out, preserving paths between retained events, including empty methods.

At each primitive boundary, a topological pass runs all enabled true checks.
Firing one early cannot disable a world fact or another event. This computes the
maximal completed-check set for that prefix and decides whether any legal
placement exists. The quantifiers are **for every primitive linearization, there
exists a legal check placement**. We never universally quantify arbitrary
positions of artificial check actions.

Starting from the saturated initial configuration, frontier `k` represents all
successful prefixes of `k` primitive occurrences. Every submitted-order-enabled
action is checked for applicability and required method checks. One failure
rejects the plan; inapplicable actions must not be silently pruned. The union of
successful action images is saturated to obtain frontier `k+1`. After `n` actions,
all retained checks and the goal must hold everywhere. The rank is the number of
completed primitive occurrences, so `n` is an exact bound, not a timeout or a
bounded approximation.

## BDD implementation

ROBDDs share equal Boolean subfunctions for a fixed variable order. Bell uses
even current-state and odd next-state variable IDs. Each action updates only its
written variables. Equality factors for those updates form a partitioned
transition relation; conjunction and existential abstraction are fused, and old
variables are eliminated after their last dependency. Unwritten variables keep
their current IDs, avoiding explicit frame equations. Next-state variables are
then renamed back to current ones.

Internal check updates are separate, local transitions applied to reachable
sets. Expanding every hierarchy closure into every primitive transition creates
large formulas for unreachable histories. Similarly, Bell tests each failure
against a frontier rather than building a global disjunction of failures over
arbitrary states. Substitution reuses unaffected subgraphs and directly rebuilds
nodes when variable order is preserved.

The BDD manager uses explicit stacks, unique nodes, memoized operations and
mark/sweep collection with stable live IDs. It currently has a fixed variable
order, no dynamic reordering, and retains frontiers for witnesses. These are
performance limitations, not losses of semantic coverage. BDD size and validation
time can still be exponential. Grounding lifted quantifiers can also be expensive.

## Counterexamples and optional proofs

A failing BDD assignment is traced backwards through check updates and primitive
updates into earlier frontiers. The resulting primitive sequence is verified by
concrete replay against the original, uncontracted hierarchy. Diagnostics and
metrics therefore refer to source occurrences, never synthetic check actions.

`auto` can settle a case through literal MTC, replay of a total order, or the
generalized modal proof. The latter cannot prove every valid Boolean plan: two
unordered conditional toggles may jointly establish a goal without either named
occurrence being its guaranteed producer. An unsuccessful modal proof delegates
to exact symbolic reachability. Strict `mtc` supports only its documented fragment.
There is no recursive splitting of unordered action pairs.

## Evidence and boundaries

Tests compare execution against truth tables, exhaustive action orders, explicit
method-check insertions, and an independent prefix explorer. They also exercise
conditional effects, remembered checks, nested/empty methods, contraction,
counterexample replay, garbage collection, and plan metrics. The public Snake
fixture has independent action-state replay and a negative control.

These tests support the implementation; they are not a machine-checked proof or
a claim of official competition certification. The technical note gives the
correctness argument for finite grounded Boolean inputs and a supplied finite
decomposition certificate. Unsupported language and input/representation limits
are reported separately from plan validity.
