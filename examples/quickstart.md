# Quickstart

A copy-paste command sequence through the whole toolchain: build, extract (four
modes), reassemble, and read the output. For the narrative version — what each
step means and why — see [`README.md`](README.md).

## Building

``` sh
make
make example
```

`make` produces two binaries and symlinks them into `bin/`:

- `bin/lean_extract` — reads a Lean project, writes JSONL records.
- `bin/lean_reassemble` — reads those records, writes Lean artifacts back.

`make example` builds `examples/tree-project`, the four-file project used below.
It is required, not optional: extraction drives Lean's frontend over each file,
which imports its dependencies' `.olean`s. Without it every command here fails
with `extraction failed for N file(s)`.

Run everything from the repo root. All output goes to `/tmp/demo-trees`, so
nothing writes into the repository.

## Extracting

The extractor has four modes, one per subsection below. They are mutually
exclusive — each replaces the others' output. All four share the same two
required arguments: `--modules`, the root module that also defines the *owned*
prefix (constants outside it are treated as library and filtered out), and
`--output`. `--source-root` defaults to `.`, so it is always worth passing.

### Simple extract

The default mode: one record per theorem and per definition across the whole
project, split into a `theorems` and a `definitions` config. This is the corpus
everything else is compared against.

```sh
./bin/lean_extract \
    --source-root ./examples/tree-project --modules Trees \
    --output /tmp/demo-trees/plain
```

```text
corpus-extract: 4 ok, 1 empty, 0 error (of 5)
corpus-extract: wrote 9 theorems + 13 definitions to /tmp/demo-trees/plain
```

Five files are discovered; `Trees.lean` only re-exports, hence "1 empty".

### Rev elab

Same corpus, but each proof *term* is re-elaborated back into a tactic script and
recorded in `proof_script`, with the rung that produced it in `proof_method`. Off
by default because it re-elaborates every proof; the scripts it emits are
typechecked, not guessed.

```sh
./bin/lean_extract \
    --source-root ./examples/tree-project --modules Trees \
    --output /tmp/demo-trees/rev-elab \
    --reverse-elab
```

Record counts are identical to the plain run — the only difference is that
`proof_script` and `proof_method` are populated rather than `null`.

### Decl

Inverts the walk: instead of the whole project, take *one* declaration plus its
transitive owned dependency closure. Each record is annotated with whether it is
needed to *state* the target or only to *prove* it. `--decl` is repeatable, and
batching is how you amortize this mode — the union of needed files is elaborated
once.

```sh
./bin/lean_extract \
    --modules     Trees --source-root ./examples/tree-project \
    --output      /tmp/demo-trees/decl \
    --decl        Trees.Tree.total_mirror
```

```text
corpus-extract: closure for Trees.Tree.total_mirror: 18 member(s) not
representable as records (2 constructors, 9 equation_compiler_helpers,
3 generated_companions, 4 recursors); see dropped.json
corpus-extract: Trees.Tree.total_mirror: closure of 29 declaration(s) across 4 module(s)
corpus-extract: wrote Trees.Tree.total_mirror → /tmp/demo-trees/decl/Trees.Tree.total_mirror (5 theorem(s), 6 definition(s))
```

Output is per-target: `/tmp/demo-trees/decl/Trees.Tree.total_mirror/`. Note the
extra `data/target.jsonl` (the target record alone) — [decl
reassembly](#decl-reassembly) depends on it.

### Proof states

Captures the *interior* of each tactic proof: the nested tactic tree with the goal
state before and after every step. The other modes only ever see a whole proof —
`body` as source text, `proof_script` as a string — so neither can express "given
this goal, the author applied this tactic, and the goal became that".

```sh
./bin/lean_extract \
    --source-root ./examples/tree-project --modules Trees \
    --output /tmp/demo-trees/proof-states \
    --proof-states
```

```text
corpus-extract: theorems: 9 captured, 0 term-proved (no tactics), 0 too large,
0 past deadline, 0 error; 28 step(s) total
corpus-extract: wrote 9 proof-state record(s) to /tmp/demo-trees/proof-states/data/proof-states/train.jsonl
```

## Reassembling

The reverse direction: given records, write Lean source back out with the proofs
replaced by `sorry`. Two shapes, differing in how many holes land in one artifact
— `materialize-repo` holes *every* record it is given in a single buildable
project, `materialize-units` emits one task per record, each holing only its own
target. Both verify their output before exiting, so a silent exit 0 means the
artifact compiled. Add `--proofs keep` to write the proofs back verbatim instead,
which gives a compilable reference state to diff against.

### Repo

``` sh
./bin/lean_reassemble materialize-repo \
    --source-root ./examples/tree-project \
    --records     /tmp/demo-trees/plain/data/theorems/train.jsonl \
    --output      /tmp/demo-trees/reasm/repo
```

Succeeds silently. The result is an ordinary Lake project under
`repos/tree-project/`, with all 9 theorems holed:

```python
import json
m = json.load(open("/tmp/demo-trees/reasm/repo/manifest.json"))
print(m["verification"], m["rewrite_summary"])
```

```text
{'status': 'passed'} {'skipped': 0, 'replaced': 9, 'proof_mode': 'sorry', 'preserved': 0, 'failed': 0, 'eligible': 9}
```

Build it like any other project — this is what makes repo mode the whole-project
correctness oracle:

```sh
cd /tmp/demo-trees/reasm/repo/repos/tree-project && lake build
```

```text
warning: Trees/Mirror.lean:22:8: declaration uses `sorry`
…
Build completed successfully (7 jobs).
```

Nine `sorry` warnings, one per holed theorem, and a successful build: every
statement, definition, and import still typechecks with all proofs removed.

### Units

``` sh
./bin/lean_reassemble materialize-units \
    --source-root ./examples/tree-project \
    --records     /tmp/demo-trees/plain/data/theorems/train.jsonl \
    --output      /tmp/demo-trees/reasm/units
```

Nine independent tasks, one per theorem:

```sh
ls /tmp/demo-trees/reasm/units/units
```

```text
0-Trees.Tree.mirror_mirror         5-Trees.sumList_reverse
1-Trees.Tree.size_mirror           6-Trees.Tree.flatten_mirror
2-Trees.Tree.length_flatten        7-Trees.Tree.length_flatten_mirror
3-Trees.Tree.sum_flatten           8-Trees.Tree.total_mirror
4-Trees.sumList_append
```

Each task's source is the **complete original module** with only *its* theorem
holed; neighbours keep their real proofs. Tasks 6 and 8 come from the same module
and differ only in which theorem is `sorry`.

Each task carries a pristine `.olean` cache, so it compiles standalone from
anywhere. `task.json` records the toolchain pin and the ordered cache roots:

```sh
ARTIFACT=/tmp/demo-trees/reasm/units
TASK="$ARTIFACT/units/8-Trees.Tree.total_mirror"
SOURCE="$TASK/src/Trees/Mirror.lean"

export LEAN_PATH="$(find "$ARTIFACT/cache/roots" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"
export LD_LIBRARY_PATH="$(find "$ARTIFACT/cache/native" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"

elan run leanprover/lean4:v4.31.0 lean -R "$TASK/src" "$SOURCE"
```

```text
…/src/Trees/Mirror.lean:24:8: warning: declaration uses `sorry`
```

Exit 0 with exactly one warning: the file compiles, with the target as its only
hole. Use `elan run` with the pin from `task.json` rather than a bare `lean` — a
different toolchain rejects the cached `.olean`s with `incompatible header`.

### Decl reassembly

Combining the two halves: feed a `--decl` closure's `data/target.jsonl` to
`materialize-units` to get exactly *one* task, for that theorem. Pass the
closure's `theorems/train.jsonl` instead and you get a task per closure member —
holing the very premise lemmas the target is meant to build on. That trap is why
`target.jsonl` is written separately.

```sh
./bin/lean_reassemble materialize-units \
    --source-root ./examples/tree-project \
    --records     /tmp/demo-trees/decl/Trees.Tree.total_mirror/data/target.jsonl \
    --output      /tmp/demo-trees/reasm/decl-unit
```

One task, `units/0-Trees.Tree.total_mirror`. Compile it the same way:

```sh
ARTIFACT=/tmp/demo-trees/reasm/decl-unit
TASK="$ARTIFACT/units/0-Trees.Tree.total_mirror"

export LEAN_PATH="$ARTIFACT/cache/roots/0"
export LD_LIBRARY_PATH="$ARTIFACT/cache/native/0"

elan run leanprover/lean4:v4.31.0 lean -R "$TASK/src" "$TASK/src/Trees/Mirror.lean"
```

```text
…/src/Trees/Mirror.lean:24:8: warning: declaration uses `sorry`
```

Now close the loop — fill the hole with the real proof and the warning goes away:

```sh
sed -i 's|^  sorry$|  rw [← sum_flatten, ← sum_flatten, flatten_mirror, sumList_reverse]|' \
    "$TASK/src/Trees/Mirror.lean"

elan run leanprover/lean4:v4.31.0 lean -R "$TASK/src" "$TASK/src/Trees/Mirror.lean"
```

Silent, exit 0. That round trip — extract a theorem, hole it, fill it, check it —
is the whole point of the pipeline.

## Data interpretation


Every `.jsonl` file is one JSON object per line, so each one loads directly as a
pandas DataFrame — one row per record.

**Layouts.** Corpus modes write a flat dataset; `--decl` writes one directory per
target with two extra files:

```text
plain/                              decl/Trees.Tree.total_mirror/
  metadata.json                       metadata.json
  data/definitions.jsonl              dropped.json          <- what had no record
  data/theorems/train.jsonl           data/definitions.jsonl
                                      data/target.jsonl     <- the target alone
                                      data/theorems/train.jsonl
```

**Setup.** Every snippet below assumes this preamble. `OUT` is the one variable to
change if you extracted somewhere else; every path is resolved against it, so no
snippet repeats a literal directory.

```python
import json
from pathlib import Path
import pandas as pd

OUT = Path("/tmp/demo-trees")          # the --output root used above

def load(*parts) -> pd.DataFrame:
    """Load one .jsonl as a DataFrame — one row per record."""
    return pd.read_json(OUT.joinpath(*parts), lines=True)

def meta(*parts) -> dict:
    """Load one .json sidecar."""
    return json.loads(OUT.joinpath(*parts).read_text())

def show(df):
    """Print a DataFrame as a left-aligned table, no index."""
    cols = list(df.columns)
    w = {c: max([len(c)] + [len(str(v)) for v in df[c]]) for c in cols}
    print("  ".join(c.ljust(w[c]) for c in cols).rstrip())
    for _, row in df.iterrows():
        print("  ".join(str(row[c]).ljust(w[c]) for c in cols).rstrip())
```

A record has 26 columns, so select before printing:

```python
thms = load("plain", "data", "theorems", "train.jsonl")
defs = load("plain", "data", "definitions.jsonl")
thms.shape          # (9, 26)
```

**What a record holds.** `signature` and `body` are verbatim source slices; `type`
is the elaborated, pretty-printed statement.

```python
r = thms.set_index("name").loc["Trees.sumList_append"]
print(r.signature)
print(r.body)
```

```text
(xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys
by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp [sumList, ih]
    omega
```

**Run summary.** `metadata.json` is the counts for the whole run:

```python
m = meta("plain", "metadata.json")
print({k: m[k] for k in ("totalRecords", "splitCounts", "countsByKind")})
```

```text
{'totalRecords': 22, 'splitCounts': {'theorems/train': 9, 'definitions/train': 13}, 'countsByKind': {'theorem': 9, 'private def': 3, 'inductive': 1, 'def': 9}}
```

**Reverse elaboration.** `proof_method` names which rung reconstructed the script,
and it is worth checking per record rather than assuming it is uniform:

```python
rev = load("rev-elab", "data", "theorems", "train.jsonl")
show(rev[["name", "proof_method"]])
```

```text
name                              proof_method
Trees.Tree.mirror_mirror          structural
Trees.Tree.size_mirror            structural
Trees.Tree.length_flatten         structural
Trees.Tree.sum_flatten            structural
Trees.sumList_append              structural
Trees.sumList_reverse             structural
Trees.Tree.flatten_mirror         structural
Trees.Tree.length_flatten_mirror  intro_exact_opaque
Trees.Tree.total_mirror           intro_exact_opaque
```

Seven proofs recover `structural`ly, keeping the `induction … with` skeleton. The
two `rw`-proved theorems collapse to `intro_exact_opaque`: a `rw` chain elaborates
to one nested `Eq.mpr` term with no tactic structure left to recover, so the
honest reconstruction is a single `exact`. In the plain run both fields are
`None`.

**Closure roles.** In `--decl` output every record says how it relates to the
target. The two data files are one closure, so concatenate them:

```python
D = ("decl", "Trees.Tree.total_mirror", "data")
closure = pd.concat([load(*D, "definitions.jsonl"),
                     load(*D, "theorems", "train.jsonl")])
show(closure[["closure_role", "kind", "name"]])
print(closure.closure_role.value_counts().to_string())
```

```text
closure_role  kind       name
statement     inductive  Trees.Tree
statement     def        Trees.Tree.brecOn.go
proof         def        Trees.Tree.flatten
statement     def        Trees.Tree.mirror
statement     def        Trees.Tree.total
proof         def        Trees.sumList
proof         theorem    Trees.Tree.flatten_mirror
proof         theorem    Trees.sumList_append
proof         theorem    Trees.Tree.sum_flatten
proof         theorem    Trees.sumList_reverse
target        theorem    Trees.Tree.total_mirror

closure_role
proof        6
statement    4
target       1
```

This is the split that matters. To *state* `t.mirror.total = t.total` you need
only `Tree`, `mirror`, and `total`. Everything else — `flatten`, `sumList`, and
all four lemmas — the original proof used but the statement never mentions. A
proof-search task keeps the statement cone as given context and treats the proof
cone as what must be rediscovered. Roles are relative to *one* target: the same
lemma is `proof` here and `statement` in another closure.

Which makes the two cones a one-line filter:

```python
statement_cone = closure[closure.closure_role == "statement"]
proof_cone     = closure[closure.closure_role == "proof"]
```

**Drops.** `dropped.json` accounts for closure members that can never have a
record — constructors, recursors, and equation-compiler helpers have no authored
source:

```python
d = meta("decl", "Trees.Tree.total_mirror", "dropped.json")
print("total:", d["total"])
show(pd.DataFrame(d["categories"])[["reason", "count"]])
```

```text
total: 18
reason                     count
constructors               2
equation_compiler_helpers  9
generated_companions       3
recursors                  4
```

11 emitted + 18 dropped = the 29 closure members, so the accounting is exact.
Only an `unexplained` category would signal a bug; there are none here.

**Proof states.** Each record holds a nested `steps` tree plus an interned `goals`
table — steps reference goals by index, so a shared state is stored once. Both
arrive as plain Python lists/dicts, so a recursive walk reads naturally:

```python
ps  = load("proof-states", "data", "proof-states", "train.jsonl")
rec = ps.set_index("name").loc["Trees.sumList_append"]

def walk(steps, depth=0):
    for s in steps:
        pad = "  " * depth
        print(f"{pad}- {s['tactic'].splitlines()[0]}")
        print(f"{pad}  {s['goals_before']} -> {s['goals_after']}")
        walk(s["children"], depth + 1)

walk(rec.steps)
for g in rec.goals:
    print(f"--- goal {g['id']} ---")
    print(g["pretty"])
```

The `induction … with` combinator becomes a **parent** step whose children are the
per-case tactics, so the source structure survives:

```text
- induction xs with
  [0] -> []
  - simp [sumList]
    [1] -> []
  - simp [sumList, ih]
    [2] -> [3]
  - omega
    [3] -> []
```

then the goal table those indices name:

```text
--- goal 0 ---
xs ys : List Nat
⊢ sumList (xs ++ ys) = sumList xs + sumList ys
--- goal 1 ---
ys : List Nat
⊢ sumList ([] ++ ys) = sumList [] + sumList ys
--- goal 2 ---
ys : List Nat
x : Nat
xs : List Nat
ih : sumList (xs ++ ys) = sumList xs + sumList ys
⊢ sumList (x :: xs ++ ys) = sumList (x :: xs) + sumList ys
--- goal 3 ---
ys : List Nat
x : Nat
xs : List Nat
ih : sumList (xs ++ ys) = sumList xs + sumList ys
⊢ x + (sumList xs + sumList ys) = x + sumList xs + sumList ys
```

Goal 3 is the arithmetic residue `simp` could not close and `omega` finished —
exactly the intermediate state no other mode exposes. To filter without walking
the tree, each record also carries a shape summary:

```python
show(ps[["name", "step_count", "max_depth", "outcome"]])
```

```text
name                              step_count  max_depth  outcome
Trees.Tree.mirror_mirror          3           1          ok
Trees.Tree.size_mirror            4           1          ok
Trees.Tree.length_flatten         4           1          ok
Trees.Tree.sum_flatten            4           1          ok
Trees.sumList_append              4           1          ok
Trees.sumList_reverse             4           1          ok
Trees.Tree.flatten_mirror         3           1          ok
Trees.Tree.length_flatten_mirror  1           0          ok
Trees.Tree.total_mirror           1           0          ok
```

The two `rw` theorems are single-step and depth 0 — the same shape that made them
`intro_exact_opaque` above. Records join to the corpus by `name`, so the two
datasets compose with a merge:

```python
joined = thms.merge(ps, on="name", suffixes=("", "_ps"))
show(joined[["name", "step_count", "kind"]].head(3))
```

Each step also carries byte offsets locating it inside the corpus record's `body`,
so the join needs no re-elaboration.
