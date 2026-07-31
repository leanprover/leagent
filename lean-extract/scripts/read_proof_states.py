#!/usr/bin/env python3
"""Read a proof-states JSONL and print each proof as a goal/tactic trajectory.

The wire format stores goals ONCE in a per-record table and has steps reference
them by index, so reading a record means resolving those indices. This script is
the minimal reference for doing that.

Usage:
    read_proof_states.py <train.jsonl>                  # list records
    read_proof_states.py <train.jsonl> <name>           # one proof, as a tree
    read_proof_states.py <train.jsonl> <name> --states  # ... with goal states
"""
import json
import sys


def load(path):
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def walk(steps):
    """Yield (step, depth) in pre-order. `steps` nests through `children`."""
    for s in steps:
        yield s, s["depth"]
        yield from walk(s["children"])


def show_index(records):
    print(f"{'name':<46}{'steps':>6}{'depth':>6}{'goals':>6}  outcome")
    for r in sorted(records, key=lambda r: -r["step_count"]):
        print(f"{r['name']:<46}{r['step_count']:>6}{r['max_depth']:>6}"
              f"{len(r['goals']):>6}  {r['outcome']}")


def show_record(r, states=False):
    goals = {g["id"]: g for g in r["goals"]}

    print(f"{r['name']}   [{r['decl_kind']}]")
    print(f"  {r['file']}:{r['start_line']}  module {r['module']}")
    print(f"  {r['step_count']} steps, depth {r['max_depth']}, "
          f"{len(r['goals'])} distinct goals, outcome={r['outcome']}"
          + (", HAS SORRY" if r["has_sorry"] else ""))

    print("\n--- proof source " + "-" * 52)
    print("  " + r["proof_source"].replace("\n", "\n  "))

    # `initial_goals` is what the proof opened with. Goal 0 is always that state:
    # ids are renumbered into step pre-order when the record is built.
    print("\n--- opening goal " + "-" * 52)
    for gid in r["initial_goals"]:
        print("  " + goals[gid]["pretty"].replace("\n", "\n  "))

    print("\n--- trajectory " + "-" * 54)
    for s, depth in walk(r["steps"]):
        ind = "  " + "    " * depth
        # A combinator (`<;>`, all_goals, ·) is a PARENT step; its children are
        # the tactics it composed. `invocations > 1` means it re-ran one tactic
        # once per goal, and the goal lists are the union over those runs.
        inv = f"  (x{s['invocations']} invocations)" if s["invocations"] > 1 else ""
        first = s["tactic"].splitlines()[0]
        more = " …" if "\n" in s["tactic"] else ""
        print(f"{ind}[{s['index']}] {first}{more}{inv}")
        print(f"{ind}     {s['goals_before']} -> {s['goals_after']}"
              f"   ({s['tactic_kind'].split('.')[-1]})")
        if states:
            for gid in s["goals_before"]:
                print(f"{ind}     BEFORE " + goals[gid]["pretty"]
                      .replace("\n", "\n" + ind + "            "))
            if not s["goals_after"]:
                print(f"{ind}     AFTER  (no goals — closed)")
            for gid in s["goals_after"]:
                print(f"{ind}     AFTER  " + goals[gid]["pretty"]
                      .replace("\n", "\n" + ind + "            "))

    print("\n--- goal table " + "-" * 54)
    for g in r["goals"]:
        print(f"  #{g['id']}  {g['pretty'].splitlines()[-1]}"
              f"    ({len(g['hyps'])} hyp(s))")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    records = load(sys.argv[1])
    if len(sys.argv) < 3:
        show_index(records)
        return 0
    name = sys.argv[2]
    hits = [r for r in records if r["name"] == name or r["name"].endswith("." + name)]
    if not hits:
        print(f"no record named {name!r}; run without a name to list them")
        return 1
    show_record(hits[0], states="--states" in sys.argv)
    return 0


if __name__ == "__main__":
    sys.exit(main())
