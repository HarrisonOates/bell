# Public IPC 2023 Snake fixture

`domain.hddl` and `problem.hddl` are unchanged copies of the public
[IPC 2023 Snake domain and pb-2slots-seed1 instance](https://github.com/ipc2023-htn/ipc2023-domains/tree/main/total-order/Snake).
They are MIT licensed by Mau Magnaguagno; the original notice is in [LICENSE](LICENSE).
The fixture includes dynamic method preconditions, empty methods, and a quantified
condition that requires all food to have been consumed.

`plan.hddl` is a 17-action certificate generated with Bowerbird, grounded with
Malleefowl, and reconstructed by Bell. Bell and Malleefowl's independent source
verifier accepted it. This is a satisficing certificate, with no optimality claim.
[provenance.json](provenance.json) records source URLs, hashes, generation commands,
and verification results. **Running the tests requires neither planner nor grounder.**

## Conditional effects

`conditional-domain.hddl` is an explicitly derived test model, not an unmodified
competition domain. In all three action schemas, the head update becomes:

```lisp
(forall (?old - location)
  (when (head ?snake ?old) (not (head ?snake ?old))))
(when (head ?snake ?previous) (head ?snake ?next))
```

The action-specific parameters replace `?previous` and `?next`. Reachable Snake
states have exactly one head, and each action requires the old head, so these
updates preserve the original transition. Both guards read the pre-action state.
An independent finite interpreter compares every state of the saved sequence:
34 guards fire and 816 are inactive. The same decomposition remains valid.

`disabled-head-domain.hddl` inverts the installation guards. Bell must reject the
unchanged certificate with an `action_precondition` counterexample.

```sh
cargo build --release
python3 scripts/check_conditional_fixture.py
```

Add `--regenerate` to reproduce the two derived domains from `domain.hddl`.
The script does not regenerate the certificate or invoke any planner.

## Regenerating a certificate

With the external tools installed, copy the original domain and problem into a
scratch directory and run the commands recorded in `provenance.json`. Capture
Bowerbird's standard output as `plan.raw`; its JSON result file contains summary
metadata, not the plan:

```sh
malleefowl-hddl --max-work=18446744073709551615 domain.hddl problem.hddl problem.sas
bowerbird --track satisficing-to --timelimit 45 --result-file engine-result.json \
  --seed 42 -g none -H 'rc(occ)' problem.sas > plan.raw
bell --input-format panda --source-map problem.sas.map.json --plan-output plan.hddl \
  domain.hddl problem.hddl plan.raw
malleefowl-hddl --max-work=18446744073709551615 convert \
  problem.sas.map.json plan.raw independent.plan
```

The last command independently verifies the reconstructed source plan. Binary
hashes identify the tools used for the saved fixture; another version may produce
a different valid certificate. The generation time limit is a planner option,
not a Bell validation cutoff.
