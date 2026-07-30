# Single-Declaration Extraction

## Goals

A corpus extraction run today is project-scoped: it walks every source file and
emits one record per constant. This mode inverts that. Given one declaration
name, it emits that declaration together with everything it depends on, as a
self-contained set of records.

1. **Closure extraction**: for a named declaration, emit its record plus a
   record for every project-owned constant its statement and proof depend on,
   transitively. Non-owned constants (Init/Std/Mathlib) are recovered through
   imports, not records.
2. **Cone annotation**: every emitted record says whether it belongs to the
   statement cone (needed to *state* the target), the proof cone (needed only to
   *prove* it), or is the target itself. A consumer can filter to either without
   re-deriving the graph.
3. **Single-unit assembly**: the output must compose with
   `lean_reassemble materialize-units` to produce one standalone, verified Lean
   task for the target declaration, with its premise records supplying context.
   This is the acceptance criterion for the mode, and it constrains the output
   layout — see [Assembling A Single Unit](#assembling-a-single-unit).

The mode reuses the existing extraction pipeline. It adds closure computation,
file selection, ordering, and a per-target writer. It does not add a second way
to elaborate Lean or a second record schema.

## Contract

```bash
lean_extract \
  --modules     Project \
  --source-root ../project \
  --decl        Project.Btree.insert_sound \
  --decl        Project.Btree.split_len \
  --output      ./decl-out
```

`--decl` is repeatable. `--output` is a directory; each target gets a
subdirectory. `--modules` remains required: it defines the owned prefix tree,
which is what makes the closure finite.

Targets are not restricted to theorems. A `def` target lands in
`definitions.jsonl` with `closure_role = "target"`; only [unit
assembly](#assembling-a-single-unit) requires a theorem target. The flag is
named `--decl`, not `--theorem`, for that reason.

### Output Layout

Each target directory mirrors the corpus layout, so every existing consumer —
including `reassemble` — reads it unchanged:

```text
decl-out/
  Project.Btree.insert_sound/
    metadata.json
    dropped.json               # what the closure could not represent, by reason
    data/
      definitions.jsonl        # closure defs/inductives/structures/axioms
      target.jsonl             # the target record alone
      theorems/
        train.jsonl            # premise lemmas + the target
```

`data/target.jsonl` is the one addition to the layout. It is the target record
and nothing else, and it exists because `materialize-units` replaces the proof
of *every* theorem record it is given. Handing it `theorems/train.jsonl` would
sorry the premise lemmas too; handing it `target.jsonl` sorries only the target.
See [Assembling A Single Unit](#assembling-a-single-unit).

Records inside each file are written in topological order, dependencies first.
Because theorems and definitions live in separate files, no single file carries
the global concatenation order; `metadata.json` records it as `assembly_order`,
spanning both files.

A target name is used verbatim as its directory name where possible.
Path-hostile characters are sanitized the way
`LeanReassemble.Materialize.safeName` sanitizes task ids, and `metadata.json`
always carries the true `target` name.

## Pipeline

1. **Resolve targets.** `importModules` the `--modules` roots and `env.find?`
   each target. No elaboration, so this is cheap, and it yields each target's
   `ConstantInfo` and defining module.
2. **Compute both cones** from that same environment:
   - *proof cone* — the existing `CollectCommon.collectPremises`: BFS over
     `getUsedConstantsAsSet` seeded from `type ∪ value`, expanding only owned
     bodies.
   - *statement cone* — the same BFS seeded from the constants of `info.type`
     alone.
   - `proof-only = proof \ statement`.

   This needs one new primitive: a seeded variant of `collectPremises`, whose
   seed is currently hardcoded to the root's full used-constant set. Everything
   else is reuse.
3. **Select files.** Map closure names to defining modules
   (`Environment.getModuleIdxFor?`), then to paths through a module-name index
   over `Discover.discoverFiles`. Take the union across all targets.
4. **Elaborate that union once**, through the existing
   `extractViaFrontendIsolated`. That already provides per-file child processes,
   `.shards/` staging, and `--resume`. Elaborating the union once is what makes
   several `--decl` flags cheaper than several invocations.
5. **Filter and write per target.** Index the resulting records by `name`, keep
   the closure plus the target, set `closure_role`, partition into
   theorems/definitions, order topologically, write.

## Schema Change

One additive field on `ConstRecord`:

```text
closure_role : Option String   -- "target" | "statement" | "proof"
```

`null` in every other extraction mode. This does change existing runs' output
bytes — one new key per line — which is the accepted cost of annotating records
rather than keeping the role map in `metadata.json` alone.

`closure_role` is a property of a record *within one target's closure*, not of
the constant. The same lemma is `statement` for one target and `proof` for
another; each target directory carries its own copy of the record.

## Sidecar Metadata

`metadata.json` per target:

```text
toolVersion               extractor version
mode                      "decl-closure"
target                    fully-qualified target name (verbatim)
targetKind                record kind of the target
targetModule              defining module
targetFile                source path relative to --source-root
closureCounts             counts by closure_role
assemblyOrder             topological name order across both data files
imports                   union of non-owned file_imports across involved files
droppedTotal              closure members with no emitted record
droppedByReason           those counts per category (names live in dropped.json)
droppedDetail             "dropped.json"
privateNames              display-name -> {rawName, module} for private members
ownershipRoots            the --modules roots used as the owned prefix tree
extractionFlags           reverse-elab / private / internal settings
filesElaborated           source files elaborated for this closure
```

`imports` is the import header a consumer needs in order to make the non-owned
constants resolvable. Owned modules are deliberately excluded: their content is
inlined as records.

`dropped.json` (format `lean-corpus-dropped.v1`) carries the per-category name
lists that `metadata.json` only counts, because on a real proof it is the larger
of the two. It is always written, even when nothing was dropped, so a consumer
never has to distinguish "no drops" from "this extractor did not report drops":

```json
{
  "format": "lean-corpus-dropped.v1",
  "target": "LambdaCalc.Term.church_rosser",
  "total": 83,
  "note": "...",
  "categories": [
    { "reason": "constructors", "count": 15,
      "names": ["LambdaCalc.Term.Par.app", "..."] }
  ]
}
```

## Known Edges And Policy

**Two ownership predicates coexist.** The closure uses the `--modules` roots,
the way `Extract.isOwned` does — it is also the only ownership notion available
in an import-only environment. Each record's own `premises` field is computed
per-file by the collector against `CollectCommon.projectRoot` (the first
component of `mainModule`). These agree for a single-root project and diverge
for `--modules A --modules B`. Record both in `metadata.json`; do not change the
collector's field semantics, which existing datasets depend on.

**Ineligible closure members have no record, and there are many of them.**
`corpusEligible` drops constructors, recursors, projections, generated
`eq_def`/`injEq`, and range-less synthetic theorems; the cone also reaches
equation-compiler and well-founded-recursion helpers (`Foo._f`, `Foo.match_1`).
All are real nodes in the elaborated term graph with no authored source, so they
can never resolve to a record — and on a real proof they *outnumber* the emitted
records. `church_rosser` in the LambdaCalc corpus drops 83 against 42 emitted.

They are therefore **classified and counted**, not listed raw. Each gets a category
label from an environment predicate (not name shape, so the classification survives
changes to Lean's naming conventions):

| Category | Meaning |
|---|---|
| `constructors` | datatype constructor |
| `recursors` | recursor or case analyzer (`.rec`, `.casesOn`, `.brecOn`) |
| `projections` | structure projection function |
| `noConfusion_stubs` | `noConfusion` stub |
| `generated_companions` | compiler companion (`._proof_*`, `._eq_*`, `.eq_def`) |
| `equation_compiler_helpers` | equation-compiler / WF-recursion helper (`._f`, `.match_*`) |
| `synthetic_theorems` | theorem with no source range (`.injEq`, `.sizeOf_spec`) |
| `private_excluded` | excluded by `--no-private` |
| `unexplained` | **eligible but produced no record — a real gap** |

The labels are plain strings, not an enum: nothing branches on them, they are only
grouped, sorted, and displayed. `unexplained` is the one that matters
operationally, so `dropIsUnexplained` names it; it sorts first everywhere and gets
its own separate warning. The run prints one summary line:

```
corpus-extract: closure for LambdaCalc.Term.church_rosser: 83 member(s) not
representable as records (15 constructors, 9 equation_compiler_helpers, 42
generated_companions, 2 noConfusion_stubs, 13 recursors, 2 synthetic_theorems);
see dropped.json
```

`--strict-closure` turns any drop into an error for callers that need a provably
complete closure.

This is why the closure is *not* a substitute for the original source module when
assembling: the [unit path](#assembling-a-single-unit) rewrites the real file
rather than concatenating records, so these gaps do not affect it.

**Private-name ambiguity is fatal.** The premise graph walks raw `Name`s while
records are keyed by unmangled `CollectCommon.displayName`, which is *not*
injective: `_private.Mod.N.foo` unmangles to `foo`, so two private declarations in
different modules can collide. `computeClosure` tracks which raw constant claimed
each display name and fails when a second, distinct constant claims the same one —
the check is on raw identity, not on role, because two colliding constants
frequently share a role (both reached only through the proof) and a role-based
check would pass while one silently overwrote the other.

`metadata.json` keeps the display-name → raw-name/module map so a consumer can
tell apart the private names that did make it in.

**`--no-private` makes closures structurally incomplete.** A proof frequently
uses a `private` lemma in the same file. Excluding those leaves holes that are
not recoverable from imports. The mode warns prominently rather than silently
emitting a closure that cannot be assembled.

**Orphan targets are rejected.** A target defined in a file that no root module
imports is invisible to step 1. Fail with an explicit error pointing at
`--list-orphans`, rather than falling back to a project-wide elaboration scan.

**`--reverse-elab` cost scales with the closure, not the target.** Reverse
elaboration is a per-file operation, so enabling it multiplies cost by the
closure's file count even when only the target's `proof_script` is wanted.
Keeping it uniform is what keeps shard fingerprints coherent: the resume
fingerprint includes the `reverseElab` flag, so a target-only variant would
fragment the shard cache. Ship uniform; add `--reverse-elab-target-only` later
if the cost proves material.

**Closure size is not bounded.** A deep theorem's closure can reach most of the
project, so this mode is not inherently fast. The way to amortize is to pass
several `--decl` flags in one invocation: the union of needed files is elaborated
once, and each target is then projected out of the shared record pool.

`--resume` does *not* make separate invocations cheap. A successful run removes
its `.shards/` staging (the same behavior as corpus mode), so resume only helps
after an *interrupted or failed* run. The shard fingerprint is independent of
which declaration was requested, so staging that survives a failure is reusable
by a later run for a different target — but nothing is retained on success.

A useful side effect of selecting files by closure: a broken file elsewhere in the
project does not fail the run, because it is never elaborated. Corpus mode fails
on such a project; `--decl` succeeds as long as the break is outside the target's
closure.

**Flag interactions.** `--decl` is mutually exclusive with `--grind-manifest`,
`--grind-in-proof`, and `--list-orphans`. `--split-by-tag` and
`--dataset-card-config` are meaningless per-target (the card renders
whole-corpus statistics); reject them rather than silently ignoring them.

## Assembling A Single Unit

This is the mode's acceptance criterion, and the reason `data/target.jsonl`
exists — it is what selects a single task out of a closure.

`lean_reassemble materialize-units` emits one task per theorem record it is handed,
each holing out only its own target. Handing it a whole closure is therefore safe,
but it produces one task per closure member — a task for every premise lemma as
well as for the target.

`data/target.jsonl` holds the target record alone, so it yields exactly the one
task you want:

```bash
# 1. Extract the closure of one theorem. (from leagent/lean-extract)
./.lake/build/bin/lean_extract \
  --modules     Project \
  --source-root ../../source-project \
  --decl        Project.Btree.insert_sound \
  --output      ./decl-out

# 2. Materialize one unit whose only hole is the target.
cd ../reassemble
lake exe lean_reassemble materialize-units \
  --source-root ../../source-project \
  --records     ../lean-extract/decl-out/Project.Btree.insert_sound/data/target.jsonl \
  --output      /tmp/insert-sound-unit
```

The result is a single standalone task, verified by invoking `lean` directly
against a pristine `.olean` cache:

```text
/tmp/insert-sound-unit/
  manifest.json
  cache/environment.json, roots/<n>/..., native/<n>/...
  units/0-Project.Btree.insert_sound/
    src/<original/relative/path>.lean
    task.json
```

The two halves of the output play different roles:

- `data/target.jsonl` drives materialization — it selects which theorem becomes a
  task.
- `theorems/train.jsonl` and `definitions.jsonl` are the **context payload**:
  the premise statements, definitions, and proofs available to whatever is
  expected to fill that hole. `closure_role` distinguishes what is needed to
  state the target from what the original proof used.
- `metadata.json`'s `imports` and `assemblyOrder` let a consumer render the
  closure as ordered Lean source when the task is presented as text rather than
  as a file to compile.

### Getting a compilable reference state

`materialize-units --proofs keep` runs the same pipeline but writes each proof back
verbatim, so the artifact compiles with the real proofs. Because the records are
still matched to declarations and their ranges validated, a byte-identical result
is evidence that the closure's records agree with the source:

```bash
lake exe lean_reassemble materialize-units \
  --source-root ../../source-project \
  --records     ../lean-extract/decl-out/<target>/data/target.jsonl \
  --output      /tmp/reference-unit \
  --proofs      keep
```

Useful as an intermediate compilable checkout from an extractor run, and as the
oracle to diff a sorried artifact against — every differing hunk should be a proof
body. See [Proof Modes](../reassemble/README.md#proof-modes).

Only theorem targets can be materialized as units:
`Materialize.eligibleTheorems` accepts `theorem` and `private theorem` and fails
with "no theorem records found" otherwise. A `def` target still produces a valid
closure; it just has no unit form.

Unit assembly requires the same source checkout the records were extracted from.
`Rewrite.planEdits` verifies the record's module, name, start line/column, and
`body` against the elaborated source, and fails rather than guessing if any of
them drifted.

## Code Placement

```text
lean-extract/Corpus/DeclClosure.lean       the `run` driver, sequencing the two
                                           phases around one elaboration
lean-extract/Corpus/DeclClosure/Cone.lean  phase 1: resolve targets, compute both
                                           cones and the drop classification,
                                           select files — all against an
                                           import-only environment
lean-extract/Corpus/DeclClosure/Emit.lean  phase 2: order, projectClosure,
                                           renderMetadata / renderDropped,
                                           writeTarget
lean-extract/Corpus/Artifact.lean       shared artifact conventions: writeJsonl /
                                        parseJsonl / partitionByConfig / safeName
lean-extract/Corpus/CollectCommon.lean  + collectPremisesFrom (seeded),
                                          collectStatementPremises, and the shared
                                          ownership helpers (moduleOf?,
                                          isOwnedModuleName, isOwnedByRoots)
lean-extract/Corpus/Records.lean        + closureRole / "closure_role"
lean-extract/Corpus/Main.lean           + --decl / --strict-closure and
                                          declModeComplaint?
lean-extract/DeclClosureTests.lean      unit tests (lake exe decl_closure_tests)
```

`Frontend`, `CorpusManifest`'s fold, and `WorkerExtract`'s driver are unchanged.
The mode is a new client of them, not a modification.

`Corpus.Artifact` exists because the extractor and the reassembler must agree on
the artifact format. `safeName` is the sharpest case: the extractor names a
`--decl` output directory with it and `reassemble` names a unit task id with it,
so a divergent copy would silently break the correspondence between the two.
`Corpus.Extract`, `Corpus.Main`, `Corpus.DeclClosure`, and
`LeanReassemble.{Rewrite,Materialize}` all consume it.

`writeTarget` is deliberately thin: `projectClosure` makes every decision
(selection, role annotation, ordering, import union) and returns a `Projection`,
`renderMetadata` turns that into JSON, and the writer only lays bytes down. That
split is what lets the tests assert on role annotation and ordering directly
instead of writing files and parsing them back.

`collectPremises` keeps its signature and meaning — it is now a thin wrapper over
`collectPremisesFrom` seeded with `type ∪ value`, so the `premises` dataset field
is unaffected. `collectStatementPremises` is the same walk seeded from the type
alone; because `getUsedConstantsAsSet` on a `ConstantInfo` is `type ∪ value`, the
statement cone is a subset of the proof cone, and role assignment can classify a
proof-cone member by testing statement-cone membership.

## Tests

`lake exe decl_closure_tests` covers the pure closure machinery:

- topological order places dependencies before their users, ignores deps outside
  the closure, and stays total/deterministic on cycles (mutual blocks) and
  self-loops;
- `applyOrder` never drops, duplicates, or invents a record;
- `projectClosure`: role annotation, exclusion of non-closure records from the
  pool, dependency-ordered output in both configs, the target-only selection, and
  the non-owned import union;
- `renderMetadata` derives its counts and `assemblyOrder` from that projection;
- `writeTarget` produces the expected layout, and `data/target.jsonl` round-trips
  through the same reader `reassemble` uses;
- unresolved members warn by default and fail under `--strict-closure`; an absent
  *target* is always fatal;
- a record-name collision across two modules is rejected, while a same-module
  duplicate (the pool being deduped) is accepted;
- drops are grouped by reason with `unexplained` first, the per-category counts
  account for every unresolved member, and `dropped.json` renders in that order;
- `safeName` produces filesystem-safe directory names.

Cone computation needs a real `Environment`, so it is verified end to end against
a fixture project (a `Box` structure and `Box.bump` in the statement; `bump_val`
and a `private succ_pos` reachable only through the proof). That run confirms:

- `Box`/`Box.bump` are classified `statement`, `bump_val`/`succ_pos` are `proof`,
  and the target is `target`;
- a private premise is emitted under its unmangled name with the raw name
  recorded in `privateNames`;
- `--decl Fix.succ_pos` resolves a target named by its *user* name against the
  mangled `_private.…` constant;
- three targets in one invocation elaborate the file set once, and a member's
  role is relative to each target (`Box.bump` is `statement` for one, `target`
  for another);
- materializing `data/target.jsonl` produces one unit whose only `sorry` is the
  target, and it verifies standalone (`lean` exit 0, only the expected
  `declaration uses 'sorry'` warning) — whereas passing `theorems/train.jsonl`
  emits three tasks and holes out the premises, which is the trap the separate
  file exists to prevent;
- the guard matrix rejects grind modes, `--list-orphans`, `--enumerate import`,
  `--split-by-tag`, `--dataset-card-config`, `--strict-closure` without `--decl`,
  a valueless `--decl`, and an unknown target — while corpus mode with the same
  flags still runs, so the guards carry no false positives;
- a second fixture, in which two modules each define `private theorem helper` in
  the same namespace, confirms the display-name collision is caught. Both
  constants are reached only through the proof, so they share a role — which is
  precisely the case a role-comparing check would have waved through.

### Real-corpus validation

Run against `ProofBenchData/generated/LambdaCalc`, a lambda-calculus development
whose headline result is `church_rosser`:

| Target | Closure | Modules | Emitted | Dropped |
|---|---|---|---|---|
| `Term.church_rosser` | 125 | 5 | 42 | 83 |
| `Term.Par.diamond` | 97 | 4 | 25 | 72 |
| `Term.subst_subst` | 64 | 2 | 13 | 51 |

Emitted + dropped equals the closure size in every case, so the accounting is
exact — nothing is silently lost between the cone and the artifact.

Confirmed on that corpus:

- the statement cone of `church_rosser` is `Term`, `Step`, `Star` plus the
  substitution defs — exactly what `t ↠ u` needs in order to be stated, with the
  reduction machinery correctly relegated to the proof cone;
- the topological order over the 42-record closure has **zero** dependency-order
  violations, no duplicates, and no unordered records — despite the project's
  mutual `Par`/`ParStar` blocks making the graph genuinely cyclic;
- all three targets in one invocation share a **single** 5-file elaboration, at
  the same 2.4s wall-clock as extracting one;
- **no `unexplained` drops** on any target: every dropped member is machinery the
  corpus excludes by design;
- materializing `data/target.jsonl` for `church_rosser` and for `subst_subst`
  yields units whose only hole is the target, each verifying against the pristine
  cache under the pinned toolchain (`elan run leanprover/lean4:v4.31.0 lean -R …`)
  with exit 0 and a single `declaration uses 'sorry'` warning. Neighbouring
  theorems in the same file keep their real proofs.

Not yet covered on a real corpus: this project contains no `private` theorems, so
the closure's private-name unmangling path is exercised only by the synthetic
collision fixture.

## Non-Goals

- Emitting a compilable `.lean` file directly from the extractor. Assembly is
  `reassemble`'s job, via the composition above.
- `.olean` cache packaging — `materialize-units` already does this.
- The `declarations.v2` byte-span and hash fields described in
  [corpus-reassembly.md](corpus-reassembly.md).
- Any interaction with the grind extraction modes.
- Closure extraction from an already-written corpus output. Slicing an existing
  JSONL would be near-instant and needs no Lean, but it requires a full
  extraction to exist first; targeted elaboration was chosen because it is
  self-contained. The two could later share this mode's writer.
