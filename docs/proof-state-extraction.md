# Per-Step Proof State Extraction

## Goals

The corpus has two representations of a proof, both whole-proof: `body` /
`decl_source` (a verbatim source slice) and `proof_script` / `proof_method` (a
mechanically reverse-elaborated string). Neither exposes the proof's *interior*, so
the dataset cannot express the unit tactic-level proof learning needs: **given this
goal, the author applied this tactic, and the goal became that**.

`--proof-states` adds that. For every tactic-proved theorem it emits one record
holding the nested tree of author-written tactics, each step carrying the goal
states before and after it ran.

The mode reuses the existing pipeline. It adds a collector and a driver; it does
not add a second way to elaborate Lean, and it does not touch any existing schema.

## Contract

```bash
lean_extract \
  --modules     Project \
  --source-root ../project \
  --proof-states \
  --output      ./ps-out
```

Output, mirroring the layout the grind modes use:

```text
ps-out/
  metadata.json                      # mode: "proof-states", run counters
  data/proof-states/train.jsonl      # one record per tactic-proved theorem
```

`--proof-states` REPLACES corpus extraction and is mutually exclusive with
`--grind-manifest`, `--grind-in-proof`, and `--decl`. `--resume` does not apply
(there is no shard staging in this mode).

Records join to the `theorems` config by `name`.

## Data Representation

Three nested types in `Corpus/Records.lean`. Keys are snake_case; encoders are
hand-written, as everywhere else in that file.

### `ProofStateRecord` — one theorem

```text
name, module, file, start_line, start_col, end_line, end_col
decl_kind          "theorem" | "private theorem"
proof_start_byte   byte range of the proof value, file-relative
proof_end_byte
proof_source       verbatim proof text, `by` included
parent_decl        enclosing declaration for a `where`/`let rec` auxiliary; null otherwise
goals              the interned goal table
initial_goals      indices: the state the proof opened in
steps              the tactic tree
step_count         total steps, nested children included
max_depth
tactic_kinds        sorted distinct kinds, for cheap filtering
has_sorry, outcome, is_private
```

`outcome` is `ok` / `skipped_large` / `deadline_skipped` / `error`. Anything but
`ok` means `steps` is empty.

### `ProofStep` — one author-written tactic

```text
index, depth              dense pre-order index; nesting depth
tactic                    VERBATIM source text
tactic_kind, elaborator
start_line/col, end_line/col, start_byte, end_byte
goals_before              indices into `goals`
goals_after
invocations               >1 ⇒ a combinator re-ran this syntax per goal
children                  the tactics a combinator composed
```

### `ProofGoal` / `ProofHyp` — one goal state

```text
id, mvar
hyps      [{ names, type, value, is_let }]
target
pretty    "n : Nat\nih : P n\n⊢ P (n + 1)"
```

`hyps` groups consecutive same-type declarations into one entry, so `a b : Nat`
stays one row, matching the infoview.

`pretty` is **synthesized** from `hyps`/`target` rather than obtained from a second
`Meta.ppGoal` call, so the two cannot disagree. It is therefore infoview-*shaped*,
not byte-identical to the infoview.

`mvar` is diagnostic only. It is **not** an identity key: the same metavariable
renders differently under different snapshots (see below).

## How the InfoTree maps to what is displayed

This is the part that has to be right; the rest is plumbing.

### Step → source bytes

Each kept node's `TacticInfo.stx` carries a real source range, so `tactic` is the
author's text sliced from the file — never `reprint`ed or pretty-printed.

Byte offsets make a step locatable inside the existing corpus schema without
re-elaborating:

```text
step.start_byte - record.proof_start_byte  =  the step's offset within that
                                              theorem's ConstRecord.body
```

That identity is the join between the two datasets and is verified end to end
(480/480 steps on the LambdaCalc corpus). `ProofStateRecord` carries byte offsets
even though `ConstRecord` does not — they are the fields
[corpus-reassembly.md](corpus-reassembly.md) proposes for `declarations.v2` and
that were never implemented. A new schema can have them without perturbing any
existing bytes.

### Goal → `Expr`: the snapshot rule

A goal is an `MVarId`, meaningful only relative to a `MetavarContext`. `TacticInfo`
carries two:

```lean
mctxBefore : MetavarContext ;  goalsBefore : List MVarId
mctxAfter  : MetavarContext ;  goalsAfter  : List MVarId
```

**`goals_before` must be rendered under `mctxBefore` and `goals_after` under
`mctxAfter`.** One snapshot for both silently mis-instantiates metavariables, so a
target shows `?m` where a concrete term belongs. Hence one
`ContextInfo.runMetaM` entry per direction per step — the same restoration
`Corpus/GrindInProof.lean` performs for a grind call site.

Rendering mirrors `Meta.ppGoal`: `lctx.sanitizeNames`, `withLCtx … localInstances`,
skip `isAuxDecl` / `isImplementationDetail`, `simpMacroScopes` each name,
`instantiateMVars` each type, width 120 (the `ppExpr120` convention).

### `have` is not a `let`

A `have`-bound hypothesis is a **nondep `ldecl`**: its value is deliberately
opaque, the infoview hides it, and core warns it "might not be type correct"
(`Lean/LocalContext.lean`). `renderGoal` therefore treats a nondep `ldecl` exactly
as `Meta.ppGoal` does — like a `cdecl`, value-less and eligible for same-type
grouping. A genuine (dependent) `let` *is* its value, so that value is kept.

This is not cosmetic. Rendering nondep values emitted the whole `casesOn` term the
elaborator built for each `have` — divergent from the infoview, and **41% of the
output** on the LambdaCalc corpus (863 KB → 511 KB).

### Goal interning

In a linear proof, step *k*'s `goals_after` is step *k+1*'s `goals_before`.
Inlining goals would nearly double the file and hide that identity, so each record
carries a `goals` table and steps hold indices. On LambdaCalc: 735 references over
447 distinct goals.

Interning keys on **rendered content**, never on `MVarId` — the same metavariable
renders differently under different snapshots, so an `MVarId`-keyed cache would
serve a stale rendering. Content keying is trivially correct. It saves wire size,
not render cost; a snapshot-keyed memo could be added later if measurement warrants.

Ids are then **renumbered into step pre-order**, because `visitM` is bottom-up and
would otherwise give the *opening* goal the highest id (`initial_goals: [2]` on a
three-goal proof). After renumbering, goal 0 is always the state the proof opened
in, and any goal the final tree no longer references is dropped, so the table
cannot carry orphans.

### Which nodes become steps

A node is kept iff all three hold:

1. it is `Info.ofTacticInfo`;
2. `stx.getKind` is in the **`tactic` or `conv` parser category**, read from the
   file's own environment (`Lean.Parser.getParserCategory?` → `ParserCategory.kinds`);
3. it has a canonical source range (`getRange? (canonicalOnly := true)`).

Selection by parser category, rather than by a denylist of containers, is a
deliberate choice. The raw tree also contains `tacticSeq`, `tacticSeq1Indented`,
`tacticSeqBracketed`, `null`, `by`, `byTactic`, `cdotTk`, `«;»`, `«<;>»`,
`withAnnotateState`, `convSeq`, … and **atoms report their own text as their kind**,
so a kind-shaped denylist is both long and open-ended. The category *is* the
definition of "a tactic a user can write", it comes from the environment the file
elaborated in, and it therefore survives Lean upgrades and picks up
project-defined tactics for free.

Both categories are needed: `Conv.conv` is in `tactic`, its interior (`Conv.lhs`, …)
is in `conv`, and `convSeq` is in neither — filtering on `tactic` alone would
record a `conv` proof's outer step only.

Combinators are kept. `induction … with`, `<;>`, `all_goals`, `·` (`Lean.cdot`),
`first`, `repeat`, `try`, `conv` are all categorized, and become parent steps whose
children are the composed tactics — that nesting is the tree.

**No macro-collapse rule is needed.** Macro expansions do appear as same-range
children (`trivial` → `apply`, `rfl` → `eqRefl`, `try` → `first`), but the expansion
is invariably either uncategorized or canonically range-less, so rules 2/3 already
drop it and the outermost author form survives. That is an empirical claim about
Lean's elaborators, so `ProofStatesTests.testCategoryFilter` asserts the
non-membership it depends on — if a future Lean categorizes an expansion, that test
fails rather than the dataset silently gaining duplicate steps.

### Combinator merge

`all_goals t` / `t <;> u` / `repeat t` re-invoke `evalTactic` on the **same
syntax** once per goal, producing N sibling nodes each with a single-goal
`goalsBefore`. Since the unit of data here is one tactic *as written*, siblings
sharing `(range, kind)` merge: goals become the ordered unions, children
concatenate, `invocations` records N.

This is the deliberate **inverse** of `Corpus/GrindInProof.lean`, which keeps those
siblings separate precisely because one grind verification condition per goal is
*its* unit of data.

Merging happens **before** sorting, and the order matters twice: `visitM` returns
siblings in elaboration order, which for a combinator is the order the tactic ran
on its goals, so merging first builds the unions in that meaningful order; and
after merging, no two steps can share `(start_byte, end_byte, kind)`, which makes
the sort total and the output deterministic (`qsort` is not stable). Sorting first
reversed a union to `[2, 1]` — caught by
`ProofStatesTests.testMergePreservesGoalOrder`.

### Theorem attribution

Steps are grouped by `ContextInfo.parentDecl?`, the same attribution
`GrindInProof` uses, so mutual blocks and `where` auxiliaries land on the right
declaration rather than on the command.

Theorems proved by a bare term (`:= rfl`) produce no tactic nodes at all. They are
**counted** (`theoremsTermProved`) rather than emitted as empty rows, so a consumer
never has to distinguish "no tactics" from "not captured".

## Bounding

Rendering every goal at every step is the cost centre, so this follows the pattern
the repo already settled on:

- **Step ceiling** (`stepCeiling = 400`) per theorem. The count is known before any
  `ppExpr` runs, so this refuses the work up front — the argument
  `CorpusManifest.reverseNodeCeiling` makes for size pre-filters over time budgets.
  Over it: `outcome = "skipped_large"`, no steps.
- **Per-file wall-clock deadline** (80% of `proofStateFileTimeoutMs`), shedding the
  tail to `deadline_skipped` rather than losing the file.
- Per-file errors are logged and counted; one bad file never sinks the run.

## Code Placement

```text
lean-extract/Corpus/ProofStates.lean         the collector: visitM walk, the pure
                                             tree algebra, goal rendering, interning
lean-extract/Corpus/ProofStatesExtract.lean  the per-file driver
lean-extract/Corpus/Records.lean             + the three record types
lean-extract/Corpus/Main.lean                + --proof-states, the mode branch,
                                               and the generalized mode guards
lean-extract/ProofStatesTests.lean           unit tests (lake exe proof_states_tests)
```

`Frontend`, `CorpusManifest`, `WorkerExtract`, `SourceSyntax`, `ReverseElab`, and
all of `reassemble` are unchanged. This mode is a new *client* of the frontend
substrate, the same relationship `--decl` has
([single-decl-extraction.md](single-decl-extraction.md)).

The tree algebra is deliberately `Info`-free — `RawStep` holds only ranges, kinds,
and goal ids — so every transform is a pure function testable without constructing
an `InfoTree`. That is the same split that makes `projectClosure` testable.

`Main.lean`'s mode guards were generalized from a hardcoded pair to
`alternateModes` / `requestedAlternateModes`, since with three mutually exclusive
early-return modes an unchecked combination would silently run only the first.

## Tests

`lake exe proof_states_tests` — 20 pure cases: sibling merge (union, `invocations`,
the empty-invocation `repeat` case, discrimination by range and by kind, nesting,
and goal-order preservation); ordering and its determinism under ties; dense
pre-order indexing, `depth`, `count`, `max_depth`, `tactic_kinds`; verbatim
slicing; reparenting; goal renumbering and orphan dropping; interning by content;
`pretty` synthesis; `have`-vs-`let`; the step ceiling and deadline passthrough; JSON
round-trip through the reader consumers use; a golden key set per type; the
parser-category filter guard; `mutual`-member descent; and auxiliary range
classification plus multi-auxiliary keying.

`TestFixtures/ProofStates/Basic.lean` is the end-to-end fixture, one declaration per
behaviour: flat, term-proved, nested, combinator-merged, a `where` auxiliary whose
parent is trivial, two auxiliaries (one tactic-proved, one term-proved), and a
`def`'s auxiliary. It lives in `lean-extract` rather than `reassemble/TestProject`,
whose `records.jsonl` and byte-for-byte rewrite comparisons new declarations would
perturb.

## Real-corpus validation

Against `ProofBenchData/generated/LambdaCalc` (11 files):

| | |
|---|---|
| Records | 64 tactic-proved theorems |
| Term-proved, skipped | 40 |
| Steps | 480 (avg 7.5/theorem, max 53 in `Term.subst_subst`) |
| Distinct goals | 447, from 735 references |
| Max nesting depth | 5 (`Term.Par.triangle`) |
| Errors / deadline / oversize | 0 / 0 / 0 |
| Unhandled-form warnings | 0 |
| Output | 511 KB |

Thirteen invariants were checked programmatically over that output, all clean:

- every record joins to a corpus theorem, and `proof_source` equals that record's
  `body` byte-for-byte;
- all 480 steps slice back out of `ConstRecord.body` at
  `start_byte - proof_start_byte` and match `tactic` exactly;
- every goal reference is in range; ids are dense; no orphan goals; goal 0 is the
  opening state; `initial_goals` matches the first top-level step;
- every child lies within its parent's byte span, and children are in source order;
- `depth`, `step_count`, and `max_depth` agree with the tree;
- every `pretty` is reproducible from its own `hyps`/`target`.

Semantically spot-checked on `Term.Par.triangle`: the nested `induction`/`cases`
branches, the `have` sub-proof, and the goal threading (step 7 produces goal 8,
consumed by steps 10 and 11) all match the source proof's structure.

## One command, several constants

Two syntactic forms declare more than one constant per command, and each needed
handling — a `Command.declaration` walk alone finds neither.

### `mutual` blocks

`SourceSyntax.proofRange?` is built on `findByKind`, which stops at the first
pre-order match. Applied to a whole `mutual` command it therefore returns the *first*
member's proof; every later member failed its `proofRanges` lookup and vanished.
`declarationNodes` descends to the members first.

Recognition is by node **kind**, deliberately not by `declarationId? .isSome`: that
test is true for any ancestor containing a `declId` — including the `mutual` block
and the anonymous `null` wrapper around its members — so a `declarationId?`-guarded
walk halts *above* the members and reports one declaration where there are two.

### `where` / `let rec` auxiliaries

An auxiliary is lifted by Lean into its own separately kernel-checked constant with
its own `findDeclarationRanges?`, so it gets its own record. This matters more than
the row count suggests: the auxiliary is frequently the **substantive** lemma, the
parent's proof being a one-line `exact aux …`. In the fixture, the parent has 1 step
and the auxiliary has 4 — dropping the auxiliary would lose the only interesting
trajectory.

Syntactically an auxiliary is a term-level `Term.letRecDecl` nested in its parent's
`whereDecls`, not a sibling declaration:

```text
Command.declaration
  Command.theorem
    Command.declValSimple          ← proofRange? finds this: the PARENT's proof
    Termination.suffix
    null
      Term.whereDecls
        Term.letRecDecl            ← the auxiliary
```

so it needs its own range function. `SourceSyntax.auxProofRange?` is the analogue of
`proofRange?`: in both auxiliary forms the value is the **last child**, per the
parsers in `Lean/Parser/Term.lean` —

```text
letIdDecl   := letIdLhs >> " := " >> termParser      → [letId, null, type, «:=», value]  → .simple
letEqnsDecl := letIdLhs >> (" := " <|> matchAlts)    → [letId, null, type, matchAlts]    → .equations
```

— mapping onto the same `DeclValueKind` distinction `proofRange?` already draws.
`auxDeclarationNodes` collects them, descending fully because auxiliaries can nest
and one `where` clause routinely declares several.

Nothing else changed: `collectFile` already iterated every file-local theorem
constant (auxiliaries included), already filtered to `.thmInfo`, and `walkTree`
already attributed steps to auxiliaries via `parentDecl?`. Supplying the missing
range was the whole fix.

`parent_decl` names the enclosing declaration for an auxiliary and is `null` for a
top-level theorem, so a consumer can group a proof with its auxiliaries or filter
them out. It is derived from the **source syntax**, not by splitting the constant
name: an auxiliary is named `<parent>.<aux>`, but so is any namespaced theorem, so
name-splitting would misclassify ordinary declarations.

Auxiliaries that are not tactic-proved theorems fall through the existing filters
with no extra code — a term-proved auxiliary is counted in `theoremsTermProved`, and
a `def`'s auxiliary is not emitted at all.

### The warning that found this

The auxiliary gap surfaced only because the "no proof range" path **warns** instead
of skipping silently:

```
corpus-extract: proof-states: no proof range for X.aux at 14:2 in …; skipping
(its declaration form may not be handled)
```

That warning was added *because* of the `mutual` bug, and it fired on the first run
afterward. It stays in place as the detector for the next unhandled form — a silent
skip in an extractor is a latent missing-data bug.

## Non-Goals

- **Per-target proof states in `--decl` output.** The natural follow-up; it needs
  no new representation, only a second writer.
- **Re-running or synthesizing tactics.** This mode observes; it never re-executes
  a tactic (unlike the grind modes) and never invents one (unlike `ReverseElab`).
- **Term-proof trajectories.** A `:= rfl` proof has no tactic structure to record.
- **A flat, columnar step table.** The nested form preserves the source structure;
  a consumer that wants rows can flatten on `index` / `depth`.

## Notes

The three hand-written encoders — one of them recursive — are the largest new
maintenance burden here, and they are exactly what
[json-library-spec.md](json-library-spec.md) exists to eliminate. This feature adds
~140 lines of the kind of code that spec proposes deleting, and is a good second
customer for stage 2 of its migration. The golden key-set test is the interim
guard.
