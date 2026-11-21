#!/usr/bin/env python3
# Copyright 2026 Harrison Oates
# SPDX-License-Identifier: Apache-2.0

"""Compare Bell's execution backends, keeping unsupported results explicit."""

import argparse
import json
from pathlib import Path
import platform
import statistics
import subprocess
import time


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bell", type=Path, default=root / "target/release/bell")
    parser.add_argument("--repeat", type=int, default=7)
    parser.add_argument("--output", type=Path, help="Also save samples and reports as JSON")
    for name in ("domain", "problem", "plan"):
        parser.add_argument("--" + name, type=Path, help="Benchmark a custom input triple")
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")
    inputs = [args.domain, args.problem, args.plan]
    if any(inputs) and not all(inputs):
        parser.error("--domain, --problem, and --plan must be supplied together")
    fixture = root / "tests/fixtures/ipc2023-snake"
    wide = root / "examples/benchmarks/unordered-26"
    cases = [("custom", inputs)] if all(inputs) else [
        ("ipc2023-snake", [fixture / f for f in ("domain.hddl", "problem.hddl", "plan.hddl")]),
        ("conditional-snake", [fixture / f for f in ("conditional-domain.hddl", "problem.hddl", "plan.hddl")]),
        ("unordered-26", [wide / f for f in ("domain.hddl", "problem.hddl", "plan.hddl")]),
    ]
    results = []
    print("case\tbackend\tstatus\tmedian_ms\twork")
    for name, files in cases:
        for backend in ("mtc", "auto", "symbolic"):
            command = [str(args.bell.resolve()), "--json", "--profile", "hddl-1.1",
                       "--execution-backend", backend, *map(str, files)]
            samples, reports = [], []
            for _ in range(args.repeat):
                start = time.perf_counter()
                result = subprocess.run(command, capture_output=True, text=True)
                samples.append(time.perf_counter() - start)
                report = json.loads(result.stdout)
                expected_exit = {"valid": 0, "invalid_plan": 1, "unsupported": 3}.get(report["status"])
                if expected_exit is None or result.returncode != expected_exit:
                    raise RuntimeError(f"{name}/{backend}: {result.stdout}{result.stderr}")
                reports.append(report)
            if any(r != reports[0] for r in reports):
                raise RuntimeError(f"{name}/{backend}: inconsistent reports across repeats")
            median_ms = statistics.median(samples) * 1000
            print(f"{name}\t{backend}\t{report['status']}\t{median_ms:.3f}\t{report['work']}")
            results.append({"case": name, "backend": backend, "command": command,
                            "samples_seconds": samples, "median_ms": median_ms, "report": report})
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"platform": platform.platform(), "repeat": args.repeat,
                                          "results": results}, indent=2) + "\n")


if __name__ == "__main__":
    main()
