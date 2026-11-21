#!/usr/bin/env python3
# Copyright 2026 Harrison Oates
# SPDX-License-Identifier: Apache-2.0

"""Run the standalone validation examples and check their expected diagnostics."""

import argparse
import json
from pathlib import Path
import shlex
import subprocess
import sys


def expected_code(case, backend):
    return case.get("expected_code_auto", case["expected_code"]) if backend == "auto" else case["expected_code"]


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", nargs="*", help="Case names from --list; default: all cases")
    parser.add_argument("--bell", type=Path, default=root / "target/release/bell")
    parser.add_argument("--backend", choices=["auto", "symbolic"], default="auto")
    parser.add_argument("--list", action="store_true", help="List case names and expected outcomes")
    parser.add_argument("--commands", action="store_true", help="Also print commands for individual runs")
    args = parser.parse_args()
    cases = json.loads((root / "examples/validation/cases.json").read_text())["cases"]
    unknown = set(args.cases) - {case["name"] for case in cases}
    if unknown:
        parser.error("unknown cases: " + ", ".join(sorted(unknown)))
    if args.cases:
        cases = [case for case in cases if case["name"] in args.cases]
    if args.list:
        for case in cases:
            print(f'{case["name"]}: {case["expected_status"]} / {expected_code(case, args.backend) or "-"}')
        return 0
    bell = args.bell.resolve()
    if not bell.is_file():
        parser.error(f"Bell executable not found at {bell}; run cargo build first or pass --bell")
    failures = 0
    for case in cases:
        command = [str(bell), "--json", "--profile", "hddl-1.1", "--execution-backend", args.backend]
        command.extend(str(root / case[key]) for key in ["domain", "problem", "plan"])
        result = subprocess.run(command, capture_output=True, text=True)
        try:
            report = json.loads(result.stdout)
        except json.JSONDecodeError:
            print(f'FAIL {case["name"]}: no JSON report (exit {result.returncode})')
            print(result.stdout + result.stderr)
            failures += 1
            continue
        diagnostic = next(iter(report.get("diagnostics", [])), {})
        status, code = report.get("status"), diagnostic.get("code")
        # Auto's literal MTC can report support/threat diagnostics instead.
        expected = expected_code(case, args.backend)
        expected_exit = 0 if case["expected_status"] == "valid" else 1
        passed = status == case["expected_status"] and code == expected and result.returncode == expected_exit
        failures += not passed
        print(f'{"PASS" if passed else "FAIL"} {case["name"]}: {status} / {code or "-"}')
        if not passed:
            print(f'  Expected: {case["expected_status"]} / {expected or "-"}, exit {expected_exit}')
        print("  " + case["explanation"])
        if diagnostic:
            print("  Bell: " + diagnostic.get("message", ""))
            if diagnostic.get("occurrence"):
                print("  Occurrence: " + diagnostic["occurrence"])
            if diagnostic.get("counterexample"):
                print("  Failing prefix: " + " -> ".join(diagnostic["counterexample"]))
        if args.commands:
            print("  " + shlex.join(command))
        if result.stderr:
            print(result.stderr, end="")
    print(f"\n{len(cases) - failures}/{len(cases)} examples matched their expected outcomes.")
    return int(failures != 0)


if __name__ == "__main__":
    sys.exit(main())
