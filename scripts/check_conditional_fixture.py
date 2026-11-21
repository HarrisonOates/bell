#!/usr/bin/env python3
"""Check the bundled IPC 2023 Snake certificate and its conditional-effects variant.

Uses only Python and Bell. The small independent interpreter checks action states
and conditional guards for this fixture; Bell checks the complete certificate.
--regenerate rewrites only the derived domains from the unchanged public source.
"""

import argparse
from collections import Counter
from copy import deepcopy
import itertools
import json
from pathlib import Path
import re
import subprocess


def parse(text):
    stack = [[]]
    for token in re.findall(r"\(|\)|[^\s()]+", re.sub(r";[^\n]*", "", text).lower()):
        if token == "(":
            stack.append([])
        elif token == ")":
            stack[-2].append(stack.pop())
        else:
            stack[-1].append(token)
    assert len(stack) == 1 and len(stack[0]) == 1
    return stack[0][0]


def field(node, key, default=None):
    return node[node.index(key) + 1] if key in node else default


def typed(tokens):
    result, pending = [], []
    position = 0
    while position < len(tokens):
        if tokens[position] == "-":
            result.extend((name, tokens[position + 1]) for name in pending)
            pending = []
            position += 2
        else:
            pending.append(tokens[position])
            position += 1
    return result + [(name, "object") for name in pending]


def render(node):
    return "(" + " ".join(map(render, node)) + ")" if isinstance(node, list) else node


def conditional_variant(source, disable=False):
    domain = deepcopy(parse(source))
    next(n for n in domain if isinstance(n, list) and n[0] == ":requirements").extend(
        [":conditional-effects", ":universal-effects"]
    )
    count = 0
    for action in domain:
        if not isinstance(action, list) or action[0] != ":action":
            continue
        effect = field(action, ":effect")
        old_head = next(p[1] for p in effect[1:] if p[0] == "not" and p[1][0] == "head")
        for i, part in enumerate(effect[1:], 1):
            if part == ["not", old_head]:
                head = ["head", old_head[1], "?old"]
                effect[i] = ["forall", ["?old", "-", "location"], ["when", head, ["not", head]]]
            elif part[0] == "head":
                guard = ["not", old_head] if disable else old_head
                effect[i] = ["when", guard, part]
        count += 1
    assert count == 3
    return (
        "; Derived from the MIT-licensed IPC 2023 Snake domain by Bell.\n"
        "; See LICENSE, provenance.json, and scripts/check_conditional_fixture.py.\n"
        + "(define " + render(domain[1]) + "\n"
        + "\n".join("  " + render(section) for section in domain[2:]) + "\n)\n"
    )


def replay_comparison(original, conditional, problem, plan):
    schemas = [
        {n[1]: n for n in parse(d) if isinstance(n, list) and n[0] == ":action"}
        for d in (original, conditional)
    ]
    problem = parse(problem)
    objects = typed(next(n[1:] for n in problem if isinstance(n, list) and n[0] == ":objects"))
    initial = {tuple(n) for s in problem if isinstance(s, list) and s[0] == ":init" for n in s[1:]}
    states = [set(initial), set(initial)]
    counts = Counter()

    def bind(expression, env):
        return tuple(env.get(t, t) for t in expression)

    def bindings(variables, env):
        variables = typed(variables)
        domains = [[n for n, t in objects if t == kind or kind == "object"] for _, kind in variables]
        for values in itertools.product(*domains):
            yield env | dict(zip((n for n, _ in variables), values, strict=True))

    def holds(expr, env, state):
        if not expr:
            return True
        head, *body = expr
        if head == "and":
            return all(holds(p, env, state) for p in body)
        if head == "not":
            return not holds(body[0], env, state)
        if head == "=":
            a, b = bind(body, env)
            return a == b
        if head == "forall":
            return all(holds(body[1], e, state) for e in bindings(body[0], env))
        return bind(expr, env) in state

    def effects(expr, env, before, add, delete):
        head, *body = expr
        if head == "and":
            for part in body:
                effects(part, env, before, add, delete)
        elif head == "forall":
            for e in bindings(body[0], env):
                effects(body[1], e, before, add, delete)
        elif head == "when":
            active = holds(body[0], env, before)
            counts["fired" if active else "inactive"] += 1
            if active:
                effects(body[1], env, before, add, delete)
        elif head == "not":
            delete.add(bind(body[0], env))
        else:
            add.add(bind(expr, env))

    network = next(n for n in parse(plan) if isinstance(n, list) and n[0] == ":htn")
    tasks = field(network, ":ordered-tasks")
    assert tasks[0] == "and"
    for identifier, call in tasks[1:]:
        for schema, state in zip(schemas, states, strict=True):
            action = schema[call[0]]
            env = dict(zip((n for n, _ in typed(field(action, ":parameters"))), call[1:], strict=True))
            assert holds(field(action, ":precondition", []), env, state), (identifier, call)
            add, delete = set(), set()
            effects(field(action, ":effect"), env, state, add, delete)
            state.difference_update(delete)
            state.update(add)
        assert states[0] == states[1], (identifier, states[0] ^ states[1])
        assert sum(f[0] == "head" for f in states[1]) == 1
    assert not any(f[0] == "mouse-at" for f in states[0])
    assert counts["fired"] and counts["inactive"]
    return {"actions": len(tasks) - 1, "guards": dict(counts), "every_state_matches_original": True}


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bell", type=Path, default=root / "target/release/bell")
    parser.add_argument("--regenerate", action="store_true", help="Regenerate the two derived domains")
    args = parser.parse_args()
    fixture = root / "tests/fixtures/ipc2023-snake"
    original = (fixture / "domain.hddl").read_text()
    for filename, disabled in (("conditional-domain.hddl", False), ("disabled-head-domain.hddl", True)):
        expected = conditional_variant(original, disable=disabled)
        path = fixture / filename
        if args.regenerate:
            path.write_text(expected)
        else:
            assert path.read_text() == expected, f"{path}: differs from the documented transformation"
    comparison = replay_comparison(original, (fixture / "conditional-domain.hddl").read_text(),
                                   (fixture / "problem.hddl").read_text(), (fixture / "plan.hddl").read_text())
    print(json.dumps(comparison, indent=2))
    for backend in ("auto", "symbolic"):
        for domain, expected in (("domain.hddl", "valid"), ("conditional-domain.hddl", "valid"),
                                 ("disabled-head-domain.hddl", "invalid_plan")):
            result = subprocess.run([str(args.bell.resolve()), "--json", "--execution-backend", backend,
                                     str(fixture / domain), str(fixture / "problem.hddl"),
                                     str(fixture / "plan.hddl")], capture_output=True, text=True)
            report = json.loads(result.stdout)
            assert report["status"] == expected, report
            assert result.returncode == (0 if expected == "valid" else 1), result.stderr
            if expected == "invalid_plan":
                assert report["diagnostics"][0]["code"] == "action_precondition", report
            print(f"PASS {backend} {domain}: {expected}")


if __name__ == "__main__":
    main()
