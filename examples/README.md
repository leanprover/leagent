# Worked Example

A guided tour of the whole toolchain on a project small enough to hold in your
head. Every command below was run against `tree-project/`; the outputs quoted are
the real ones.

You will extract a corpus, reverse-elaborate proof terms into tactic scripts,
capture the goal state before and after every tactic, slice one theorem's
dependency closure, and materialize both a whole sorried repository and
standalone single-theorem tasks that verify on their own.

In a hurry? [`quickstart.md`](quickstart.md) is the same pipeline as a bare
command sequence, without the commentary.

## The example project

`tree-project/` is a four-file Lake project about binary trees. The files form a
chain, so imports and definitions are load-bearing rather than decorative:

```text
Trees/Basic.lean     Tree (inductive), size, mirror
                     size_mirror, mirror_mirror
Trees/ListSum.lean   sumList
                     sumList_append, sumList_reverse
Trees/Flatten.lean   imports Basic + ListSum
                     flatten, total
                     length_flatten, sum_flatten
Trees/Mirror.lean    imports Flatten
                     flatten_mirror, total_mirror, length_flatten_mirror
```

9 theorems and 4 hand-written definitions over one `inductive`. Nothing needs
Mathlib — the only external import is `Init` — so the tools resolve every
dependency either from a record or from core.

The headline result is `Trees.Tree.total_mirror`: *mirroring a tree preserves the
sum of its labels*. Its three-line proof routes through both base files —

```lean
theorem total_mirror (t : Tree) : t.mirror.total = t.total := by
  rw [← sum_flatten, ← sum_flatten, flatten_mirror, sumList_reverse]
```

— which makes it the interesting target: its dependency closure reaches every
module in the project, while its *statement* needs only `Tree`, `mirror`, and
`total`. The tools distinguish those two sets, and that distinction is the point
of [step 3](#3-slice-one-theorems-dependency-closure).

## Setup

Build the tools and the example project once. Everything pins Lean **4.33.0**.

```bash
cd leagent
make            # lean_extract + lean_reassemble, symlinked into bin/
make example    # the .oleans the extractor imports
```

The example project must be built: extraction drives Lean's frontend over each
file, which imports its dependencies' `.olean`s.

The commands below spell out `./.lake/build/bin/lean_extract` and
`lake exe lean_reassemble` from inside each package, since that is what the
reference docs use. If you would rather stay at the repo root, `make` leaves
equivalent binaries in `bin/`:

```bash
./bin/lean_extract    --modules Trees --source-root examples/tree-project --output /tmp/out
./bin/lean_reassemble materialize-units --source-root examples/tree-project …
```

Paths below are relative to `leagent/`. Outputs go to `/tmp`, so nothing you run
here writes into the repository.

## 1. Extract a corpus

One record per theorem and per definition, across the whole project.

```bash
cd lean-extract
./.lake/build/bin/lean_extract \
    --modules     Trees \
    --source-root ../examples/tree-project \
    --output      /tmp/ex-corpus \
    --reverse-elab
```

```text
corpus-extract: 4 ok, 1 empty, 0 error (of 5)
corpus-extract: wrote 9 theorems + 13 definitions to /tmp/ex-corpus
```

Five files are discovered; `Trees.lean` is the import-only root, hence "1 empty".
The 13 definitions are the 4 authored ones plus `Tree` and the machinery Lean
generates around an inductive.

```text
/tmp/ex-corpus/
  metadata.json
  data/definitions.jsonl
  data/theorems/train.jsonl
```

Look at one theorem record:

```bash
jq -r 'select(.name == "Trees.sumList_append")
       | .signature, .body, "type: \(.type)"' \
  /tmp/ex-corpus/data/theorems/train.jsonl
```

`signature` and `body` are verbatim source slices, `type` is the elaborated and
pretty-printed statement:

```text
(xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys
by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp [sumList, ih]
    omega
type: ∀ (xs ys : List Nat), Trees.sumList (xs ++ ys) = Trees.sumList xs + Trees.sumList ys
```

### Premises: what a proof actually leans on

`premises` is the transitive cone of *project-owned* constants a proof depends
on — the field premise-selection training keys on. It includes generated
machinery (`._f`, `.match_1`, `._proof_4`, recursors), so intersect it with the
names that actually have records to see the authored cone:

```bash
jq -rn --slurpfile thms /tmp/ex-corpus/data/theorems/train.jsonl \
       --slurpfile defs /tmp/ex-corpus/data/definitions.jsonl '
  ([$thms[], $defs[]] | map(.name)) as $known
  | $thms[]
  | "\(.name)\t\(.premises | length)\t" +
    ([.premises[] | select(IN($known[])) | ltrimstr("Trees.")] | join(" "))
' | column -ts$'\t'
```

The project's layering falls out (generated names filtered, so counts exceed the
listed cone):

```text
Trees.sumList_append               5   sumList
Trees.sumList_reverse              7   sumList sumList_append
Trees.Tree.sum_flatten             20  Tree Tree.brecOn.go Tree.flatten Tree.total sumList sumList_append
Trees.Tree.total_mirror            28  Tree Tree.brecOn.go Tree.flatten Tree.flatten_mirror Tree.mirror Tree.sum_flatten Tree.total sumList sumList_append sumList_reverse
```

`sumList_append` reaches 5 constants and depends on nothing but its own
definition; `total_mirror` reaches 28 and pulls in every authored definition and
four of the other lemmas — the whole project, as promised. Premise names that are
not among the definitions are lemmas: look them up in the theorems config.

### Tags

`tags.json` in the example project attaches metadata by module substring:

```bash
./.lake/build/bin/lean_extract \
    --modules     Trees \
    --source-root ../examples/tree-project \
    --config      ../examples/tree-project/tags.json \
    --output      /tmp/ex-tagged
```

Every record now carries `{"layer": …, "topic": …}`:

```bash
jq -r '"\(.name)\t\(.tags.layer)/\(.tags.topic)"' \
  /tmp/ex-tagged/data/theorems/train.jsonl | column -ts$'\t'
```

```text
Trees.Tree.mirror_mirror          base/tree
Trees.Tree.size_mirror            base/tree
Trees.Tree.length_flatten         middle/bridge
Trees.Tree.sum_flatten            middle/bridge
Trees.sumList_append              base/list
Trees.sumList_reverse             base/list
Trees.Tree.flatten_mirror         top/tree
Trees.Tree.length_flatten_mirror  top/tree
Trees.Tree.total_mirror           top/tree
```

Tags are what `--split-by-tag` stratifies a train/valid/test split on.

## 2. Reverse elaboration: proof terms back to tactic scripts

`--reverse-elab` (passed in step 1) re-elaborates each proof *term* into a
verified tactic script, recorded in `proof_script` with the rung that produced it
in `proof_method`.

```bash
jq -r '"\(.name)\t\(.proof_method)"' \
  /tmp/ex-corpus/data/theorems/train.jsonl | column -ts$'\t'
```

```text
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

Seven proofs recover `structural`ly — the script keeps the `induction … with`
skeleton and its case split, with each branch's term spelled out:

```text
by
  intro xs
  intro ys
  induction xs with
  | nil =>
    exact
      of_eq_true
        (Eq.trans (congrArg (Eq (Trees.sumList ys)) (Nat.zero_add (Trees.sumList ys)))
          (eq_self (Trees.sumList ys)))
  | cons x xs ih =>
    exact
      Eq.mpr
        (id
          (congrFun'
            (congrArg Eq (Eq.trans (Trees.sumList.eq_2 x (xs ++ ys)) (congrArg (HAdd.hAdd x) ih)))
            (x + Trees.sumList xs + Trees.sumList ys)))
        (Decidable.byContradiction fun a => Trees.sumList_append._proof_4 ys x xs a)
```

The `induction xs with` / `| nil` / `| cons x xs ih` skeleton is recovered from
the proof term; each branch's `simp`+`omega` collapses into the explicit term it
produced.

The two `rw`-proved theorems land on `intro_exact_opaque` instead: a `rw` chain
elaborates to one nested `Eq.mpr` term with no tactic structure left to recover,
so the honest reconstruction is a single `exact`. Both are still *verified* —
these scripts were re-elaborated and typechecked, they are not guesses. This
contrast is why `proof_method` is recorded per record rather than assumed
uniform; the ladder and its soundness guards are documented in
[`workers/docs/proof-simplification.md`](../workers/docs/proof-simplification.md).

Reverse elaboration is off by default because it re-elaborates every proof.
`--closers` additionally tries `simp`/`omega`-style goal-closing tactics for
high-level proofs, at roughly 20× the cost.

## 3. Slice one theorem's dependency closure

Instead of walking the project, take one declaration plus everything it depends
on:

```bash
./.lake/build/bin/lean_extract \
    --modules     Trees \
    --source-root ../examples/tree-project \
    --decl        Trees.Tree.total_mirror \
    --output      /tmp/ex-decl
```

```text
corpus-extract: closure for Trees.Tree.total_mirror: 18 member(s) not
representable as records (2 constructors, 9 equation_compiler_helpers,
3 generated_companions, 4 recursors); see dropped.json
corpus-extract: Trees.Tree.total_mirror: closure of 29 declaration(s) across 4 module(s)
corpus-extract: wrote Trees.Tree.total_mirror → /tmp/ex-decl/Trees.Tree.total_mirror (5 theorem(s), 6 definition(s))
```

29 closure members: 11 become records, 18 are constructors, recursors, and
equation-compiler helpers that have no authored source and so can never have one.
They are classified by reason and listed in `dropped.json`; 11 + 18 = 29, so the
accounting is exact. Only an `unexplained` drop would signal a bug — there are
none here. `--strict-closure` turns any drop into an error.

### Statement cone vs proof cone

Every record is annotated with `closure_role`:

```bash
D=/tmp/ex-decl/Trees.Tree.total_mirror/data
jq -r '"\(.closure_role)\t\(.kind)\t\(.name)"' \
  "$D/definitions.jsonl" "$D/theorems/train.jsonl" | column -ts$'\t'
```

```text
statement  inductive  Trees.Tree
statement  def        Trees.Tree.brecOn.go
proof      def        Trees.Tree.flatten
statement  def        Trees.Tree.mirror
statement  def        Trees.Tree.total
proof      def        Trees.sumList
proof      theorem    Trees.Tree.flatten_mirror
proof      theorem    Trees.sumList_append
proof      theorem    Trees.Tree.sum_flatten
proof      theorem    Trees.sumList_reverse
target     theorem    Trees.Tree.total_mirror
```

(Records come out in dependency order within each file, definitions and theorems
being separate files — not grouped by role.)

This is the split worth pausing on. To *state* `t.mirror.total = t.total` you
need exactly `Tree`, `mirror`, and `total`. Everything else — `flatten`,
`sumList`, and all four lemmas — the original proof used but the statement never
mentions. A consumer building a proof-search task keeps the statement cone as
given context and treats the proof cone as what it must rediscover.

`metadata.json` records the closure's shape, including a topological
`assemblyOrder` (dependencies first) and the non-owned imports needed to make it
resolvable:

```bash
jq '{mode, target, closureCounts, imports, droppedTotal}' \
  /tmp/ex-decl/Trees.Tree.total_mirror/metadata.json
```

```json
{ "mode": "decl-closure", "target": "Trees.Tree.total_mirror",
  "closureCounts": { "target": 1, "statement": 4, "proof": 6 },
  "imports": ["Init"], "droppedTotal": 18 }
```

### Roles are per target, not per constant

Ask for two targets in one invocation:

```bash
./.lake/build/bin/lean_extract \
    --modules     Trees \
    --source-root ../examples/tree-project \
    --decl        Trees.Tree.total_mirror \
    --decl        Trees.sumList_reverse \
    --output      /tmp/ex-decl2
```

```text
corpus-extract: Trees.Tree.total_mirror: closure of 29 declaration(s) across 4 module(s)
corpus-extract: Trees.sumList_reverse: closure of 8 declaration(s) across 1 module(s)
corpus-extract: elaborating 4 file(s) for 2 target(s) (isolated, jobs=4)…
```

Two things to notice. First, **one** 4-file elaboration serves both targets —
batching `--decl` flags is how you amortize this mode, since separate invocations
each pay full elaboration cost.

Second, compare `Trees.sumList` across the two output directories: it is `proof`
for `total_mirror` and `statement` for `sumList_reverse`. And `sumList_reverse`
itself is `proof` in the first closure and `target` in its own. The role is a
property of a record *within one closure*, which is why each target directory
carries its own copy of the record.

## 4. Extract the goal state at every step

`--proof-states` captures the *interior* of each tactic proof — the state the
prover was looking at before and after each tactic. Neither `body` (a source
slice) nor `proof_script` (a whole-proof string) can express that.

```bash
./.lake/build/bin/lean_extract \
    --modules      Trees \
    --source-root  ../examples/tree-project \
    --proof-states \
    --output       /tmp/ex-states
```

```text
corpus-extract: theorems: 9 captured, 0 term-proved (no tactics), 0 too large,
0 past deadline, 0 error; 28 step(s) total
corpus-extract: wrote 9 proof-state record(s) to /tmp/ex-states/data/proof-states/train.jsonl
```

Each record holds a nested `steps` tree plus an interned `goals` table; steps
reference goals by index, so a state shared by several steps is stored once.
Walk `sumList_append`:

```bash
jq -r 'select(.name == "Trees.sumList_append")
  | def walk($d): .[]
      | "\("  " * $d)- \(.tactic | split("\n")[0])",
        "\("  " * $d)  \(.goals_before) -> \(.goals_after)",
        (.children | walk($d + 1));
    (.steps | walk(0)),
    (.goals[] | "--- goal \(.id) ---", .pretty)
' /tmp/ex-states/data/proof-states/train.jsonl
```

First the tactic tree — the `induction … with` combinator becomes a **parent**
step whose children are the per-case tactics, so the source structure survives:

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

then the goal table those indices name — the real intermediate states:

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

Goal 0 is the opening state, goal 2 the `cons` case before `simp`, and goal 3 is
precisely the arithmetic residue `simp` could not close and `omega`
finished — the intermediate state that only this mode exposes. Records join to
the corpus by `name`, and each step carries byte offsets locating it inside the
corpus record's `body`, so the two datasets compose without re-elaborating.

Across the project: 28 steps, depth 1, no errors. The two `rw` theorems are
single-step and depth 0. Theorems proved by a bare term would be *counted* as
term-proved rather than emitted as empty rows; this project has none.

## 5. Assemble a standalone single-theorem task

Now hand the closure's target record to the reassembler. `data/target.jsonl`
holds the target *alone*, which is what makes the output a single task.

```bash
cd ../reassemble
lake exe lean_reassemble materialize-units \
    --source-root ../examples/tree-project \
    --records     /tmp/ex-decl/Trees.Tree.total_mirror/data/target.jsonl \
    --output      /tmp/ex-unit
```

Silent success, exit 0. The artifact:

```text
/tmp/ex-unit/
  manifest.json
  cache/environment.json, roots/0/…, native/0/…
  units/0-Trees.Tree.total_mirror/
    src/Trees/Mirror.lean
    task.json
```

The task source is the **complete original module** with only the target holed:

```lean
/-- Mirroring reverses the in-order traversal. -/
theorem flatten_mirror (t : Tree) : t.mirror.flatten = t.flatten.reverse := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mirror, flatten, ihl, ihr]

/-- Mirroring preserves the sum of the labels. -/
theorem total_mirror (t : Tree) : t.mirror.total = t.total := by
  sorry

/-- The two `size` facts combine … -/
theorem length_flatten_mirror (t : Tree) : t.mirror.flatten.length = t.size := by
  rw [length_flatten, size_mirror]
```

Note what did *not* happen: the neighbours keep their real proofs. The whole
module is retained rather than extracting the theorem into a fresh file, because
`open`s, section variables, notation, and private names are not reproducible out
of context.

`manifest.json` reports `"verification": {"status": "passed"}` — the materializer
ran `lean` against a pristine `.olean` cache and got exit 0 with exactly one
expected `declaration uses 'sorry'` warning.

### Replay the task yourself

The artifact is self-contained; `task.json` records the toolchain pin and the
ordered cache roots.

```bash
ARTIFACT=/tmp/ex-unit
TASK="$ARTIFACT/units/0-Trees.Tree.total_mirror"
SOURCE="$TASK/src/Trees/Mirror.lean"

export LEAN_PATH="$(find "$ARTIFACT/cache/roots" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"
export LD_LIBRARY_PATH="$(find "$ARTIFACT/cache/native" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"

elan run leanprover/lean4:v4.33.0 lean -R "$TASK/src" "$SOURCE"
```

```text
…/src/Trees/Mirror.lean:24:8: warning: declaration uses `sorry`
```

Exit 0, one warning: the task compiles, with the target as its only hole. Use
`elan run` with the pin from `task.json` rather than a bare `lean` — a different
toolchain rejects the cached `.olean`s with `incompatible header`.

Replace `sorry` with the real `rw [← sum_flatten, ← sum_flatten, flatten_mirror,
sumList_reverse]` and re-run: the warning disappears. That round trip is the
whole loop — extract a theorem, hole it, hand it to a prover, check the answer.

### One task per theorem

Pass the corpus's theorem file instead and you get 9 independent tasks, each
holing only its own target:

```bash
lake exe lean_reassemble materialize-units \
    --source-root ../examples/tree-project \
    --records     /tmp/ex-corpus/data/theorems/train.jsonl \
    --output      /tmp/ex-units-all
```

```text
/tmp/ex-units-all/units/
  0-Trees.Tree.mirror_mirror        3-Trees.Tree.sum_flatten          6-Trees.Tree.flatten_mirror
  1-Trees.Tree.size_mirror          4-Trees.sumList_append            7-Trees.Tree.length_flatten_mirror
  2-Trees.Tree.length_flatten       5-Trees.sumList_reverse           8-Trees.Tree.total_mirror
```

All 9 verified (`"status": "passed"`). Tasks 6 and 8 come from the same module and
differ only in which theorem is holed. Each source file is elaborated once and
reused across its targets, so the marginal cost per task is a byte-splice plus
one `lean` run.

This is also why the closure step writes `target.jsonl` separately: pointing
`materialize-units` at a closure's `theorems/train.jsonl` would emit a task per
closure *member*, holing the premise lemmas the target is supposed to build on.

### What the solver can actually see

Worth being explicit about, because it is easy to over-read what a unit contains.
A task holds **one** source file:

```bash
find /tmp/ex-unit/units/0-Trees.Tree.total_mirror -type f
```

```text
.../src/Trees/Mirror.lean
.../task.json
```

That file opens with `import Trees.Flatten` and nothing else. `Tree`, `mirror`,
`total`, `flatten`, `sumList`, and every premise lemma resolve from the **compiled
`.olean`s** in `cache/roots/0` — binary, not source. So a unit is enough for a
solver that can *elaborate* against the environment (query the goal, ask for a
type, run tactics), but a solver working from text alone sees only the target
module. It cannot read the definition of `total` from the artifact.

Three ways to give it the definitions, depending on what the consumer wants:

**1. Render the closure as text.** This is what the `--decl` records are for. The
statement cone is what you need just to *read* the goal — slice it from source,
since an `inductive` carries a line range but no `signature`/`body`:

```bash
D=/tmp/ex-decl/Trees.Tree.total_mirror
jq -r 'select(.closure_role == "statement" and .start_line != null)
       | "\(.file) \(.start_line) \(.end_line)"' \
  "$D/data/definitions.jsonl" "$D/data/theorems/train.jsonl" \
| while read -r f a b; do sed -n "$a,$b p" examples/tree-project/"$f"; echo; done
```

```lean
/-- A binary tree with a `Nat` at each internal node. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

/-- Reflect a tree left-to-right. -/
def mirror : Tree → Tree
  | .leaf => .leaf
  | .node l v r => .node r.mirror v l.mirror

/-- Sum of every label, computed on the tree directly. -/
def total : Tree → Nat
  | .leaf => 0
  | .node l v r => l.total + v + r.total
```

Exactly the three declarations `t.mirror.total = t.total` mentions. The proof cone
is then the premise list — statements only, since the proofs are what you are
asking for:

```bash
jq -r 'select(.closure_role == "proof" and .signature != null)
       | "\(.kind) \(.name) \(.signature)"' \
  "$D/data/definitions.jsonl" "$D/data/theorems/train.jsonl"
```

```text
def Trees.Tree.flatten : Tree → List Nat
def Trees.sumList : List Nat → Nat
theorem Trees.Tree.flatten_mirror (t : Tree) : t.mirror.flatten = t.flatten.reverse
theorem Trees.sumList_append (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys
theorem Trees.Tree.sum_flatten (t : Tree) : sumList t.flatten = t.total
theorem Trees.sumList_reverse (xs : List Nat) : sumList xs.reverse = sumList xs
```

(`signature` is a verbatim source slice, so a statement that wrapped in the source
wraps here too.)

Note this is *rendering context for a prompt*, not producing a compilable file.
Concatenating these records into one file does **not** compile: the closure spans
two namespaces (`Trees.sumList` and `Trees.Tree.flatten`), and a flat splice
cannot reproduce the `namespace`/`open`/section structure they were elaborated in.
That is the same reason units keep the whole module — see
[`docs/corpus-reassembly.md`](../docs/corpus-reassembly.md).

**2. Give it the whole project, one hole.** If the solver should see real source
for every dependency, use `materialize-repo` with `target.jsonl` — repo mode holes
only the records it is handed:

```bash
lake exe lean_reassemble materialize-repo \
    --source-root ../examples/tree-project \
    --records     /tmp/ex-decl/Trees.Tree.total_mirror/data/target.jsonl \
    --output      /tmp/ex-repo-target
```

```text
/tmp/ex-repo-target/repos/tree-project/
├── Trees/{Basic,Flatten,ListSum,Mirror}.lean
├── Trees.lean
└── lakefile.toml, lake-manifest.json, lean-toolchain
```

`{"replaced": 1}` — all four source files present and readable, exactly one
`sorry` (`Trees/Mirror.lean:25`), and `lake build` succeeds with a single
`declaration uses 'sorry'` warning. This is usually what you want for an agent
that browses files.

**3. Point it at the original checkout.** Units are designed to be consumed
alongside the corpus they came from; `record.file` plus the line ranges locate
every dependency in the source tree you extracted from.

## 6. Assemble a whole repository

`materialize-repo` holes **every** record it is given, in one buildable Lake
project.

```bash
lake exe lean_reassemble materialize-repo \
    --source-root ../examples/tree-project \
    --records     /tmp/ex-corpus/data/theorems/train.jsonl \
    --output      /tmp/ex-repo

jq '{verification, rewrite_summary}' /tmp/ex-repo/manifest.json
```

```json
{ "verification": { "status": "passed" },
  "rewrite_summary": { "skipped": 0, "replaced": 9, "proof_mode": "sorry",
                       "preserved": 0, "failed": 0, "eligible": 9 } }
```

All 9 proofs became `sorry` and the project still builds — `materialize-repo`
runs `lake build` on the rewritten copy, which is what makes it the
whole-project correctness oracle. Poke at it as an ordinary project:

```bash
cd /tmp/ex-repo/repos/tree-project && lake build
```

```text
⚠ [5/7] Replayed Trees.Mirror
warning: Trees/Mirror.lean:22:8: declaration uses `sorry`
…
Build completed successfully (7 jobs).
```

Nine `sorry` warnings, one per holed theorem, and a successful build: the
statements, definitions, and imports still typecheck with every proof removed.

### The `keep` mode and the diff oracle

`--proofs keep` runs the identical pipeline — match each record to one
declaration, get the proof range from parsed `Syntax`, check the recorded `body`
against the source — then writes the original proof back instead of a `sorry`:

```bash
lake exe lean_reassemble materialize-repo \
    --source-root ../examples/tree-project \
    --records     /tmp/ex-corpus/data/theorems/train.jsonl \
    --output      /tmp/ex-ref \
    --proofs      keep

jq '.rewrite_summary' /tmp/ex-ref/manifest.json
```

```json
{ "skipped": 0, "replaced": 0, "proof_mode": "keep",
  "preserved": 9, "failed": 0, "eligible": 9 }
```

`keep` is not a bypass, and a byte-identical result is the evidence: a wrong
range would splice back the wrong slice. Diff the two artifacts and every hunk
should be a proof body and nothing else:

```bash
diff -r --exclude=.lake --exclude=rewrite-report.json \
  /tmp/ex-ref/repos/tree-project /tmp/ex-repo/repos/tree-project
```

```text
diff …/ex-ref/repos/tree-project/Trees/Mirror.lean …/ex-repo/repos/tree-project/Trees/Mirror.lean
25c23
<   rw [← sum_flatten, ← sum_flatten, flatten_mirror, sumList_reverse]
---
>   sorry
```

Nine such hunks across four files, no other change — signatures, docstrings,
definitions, and imports all untouched. That is what validates the sorried
artifact. Under `keep`, unit verification is also *stricter*: a `sorry` warning is
expected in `sorry` mode but rejected here, since a preserved artifact should
compile with no diagnostics at all.

### Rewriting a single file

`rewrite-file` is the surgical helper — one file, validated through the Lean
worker before it is written:

```bash
lake exe lean_reassemble rewrite-file \
    --source-root ../examples/tree-project \
    --records     /tmp/ex-corpus/data/theorems/train.jsonl \
    --file        Trees/Mirror.lean \
    --output      /tmp/ex-rewritten.lean
```

All three of `Mirror.lean`'s theorems come back as `by sorry`, with the rest of
the file verbatim.

## Where to go next

Everything above generalizes to a real project by changing `--modules` and
`--source-root`. Two diagnostics worth knowing on a project you did not write:

```bash
# Files on disk that no root module imports — invisible to import-based tools,
# and rejected as --decl targets.
./.lake/build/bin/lean_extract --modules Trees \
    --source-root ../examples/tree-project --list-orphans
# → 5 file(s) on disk, 604 in import closure   (the second figure is core+Init,
#   no orphans (every discovered file is in the import closure)   so it moves with the toolchain)

# Resume an interrupted isolated run from its per-file shards.
./.lake/build/bin/lean_extract … --resume
```

Reference documentation:

- [`lean-extract/README.md`](../lean-extract/README.md) — all flags, the record
  schema, and the four extraction modes.
- [`reassemble/README.md`](../reassemble/README.md) — the three commands, proof
  modes, and the durable task-replay contract.
- [`docs/single-decl-extraction.md`](../docs/single-decl-extraction.md) — closure
  design, cone computation, and drop classification.
- [`docs/proof-state-extraction.md`](../docs/proof-state-extraction.md) — the
  tactic-tree walk and goal interning.
- [`docs/corpus-reassembly.md`](../docs/corpus-reassembly.md) — why units keep the
  whole module.

Clean up the outputs when you are done:

```bash
rm -rf /tmp/ex-corpus /tmp/ex-tagged /tmp/ex-decl /tmp/ex-decl2 /tmp/ex-states \
       /tmp/ex-unit /tmp/ex-units-all /tmp/ex-repo /tmp/ex-ref /tmp/ex-rewritten.lean
```
