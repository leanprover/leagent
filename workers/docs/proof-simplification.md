# Proof simplification (reverse-elaboration)

`WorkerPlugins.ReverseElab` turns a **proof term** (a Lean `Expr`) back into a
short, human-legible **tactic script** — e.g. it rewrites the elaborated term

```lean
fun x => LeanSQLite.FileId.casesOn x (Eq.refl FileId.DB) (Eq.refl FileId.Journal)
```

into

```lean
by intro x
   cases x with
   | DB => exact Eq.refl LeanSQLite.FileId.DB
   | Journal => exact Eq.refl LeanSQLite.FileId.Journal
```

This is the reverse of normal elaboration (script → term), so we call it
*reverse-elaboration*. It backs the `proof_script` / `proof_method` fields of the
corpus (`--reverse-elab`).

The hard part is not generating a candidate — it is generating one that is
**correct** and **honestly labeled**. The whole design rests on a single
guarantee: *every script we emit is re-checked against the original proof, and
anything that doesn't reproduce it is rejected.* Generation can therefore be
optimistic and heuristic; verification is what makes the output sound.

---

## 1. The core idea: a verified candidate ladder

For a proof `v : ty`, we build an **ordered list of candidate scripts**, from
most-decomposed/most-readable to least, and return the **first one that
verifies**. If none verify we emit nothing (`method := "fail"`).

```
        for candidate in ladder (best → worst):
            if verify(candidate, against = v):
                return candidate          -- first success wins
        return fail
```

Because a later rung (`exact <the whole term>`) reproduces *any* proof, the
ladder almost always terminates in a verified script; the earlier rungs are
attempts to do better than a giant `exact`. The `method` label records which
rung won, so a downstream consumer can tell a genuine decomposition apart from a
fallback.

### The ladder (highest priority first)

Let `body` be the proof term after peeling its leading `fun` binders (those
become an `intro` spine), and let an **atomic** body be one shallow enough
(`Expr.approxDepth < 8`) to count as a legible term rather than an automation
blob (a `simp`/`omega`/`rw`/`decide` residue).

| # | Candidate | `method` label | Emitted when |
|---|-----------|----------------|--------------|
| 0 | `intro …; <structural decomposition>` | `structural` | the body is a `casesOn`/`have`/`by_cases`/recursor/constructor (see §2) |
| 1 | `intro …; rfl` | `rfl` / `intro_rfl` | body is reflexivity-headed (`Eq.refl`/`Iff.refl`/`rfl`/`HEq.refl`) |
| 2 | `intro …; exact <term>` | `exact` / `intro_exact` | body is **atomic** (small, readable) |
| 3 | `intro …; <closer>` | `simp` / `omega` / `intro_simp` / … | only with `--closers` (see §4) |
| 4 | `intro …; exact <blob>` | `exact_opaque` / `intro_exact_opaque` | body is **non-atomic** (automation residue) — verified but unreadable |
| 5 | `exact <whole term>` | `exact_whole` | always (no `intro` peeling); the universal fallback |

Each candidate is generated twice — once with the default delaborator and once
with `delabExplicit` (explicit args, universes, full names, `pp.proofs`) — since
the explicit form is more likely to round-trip even if it is uglier. The first
of the pair that verifies wins.

The labels encode **how much real decomposition happened**, deliberately:

- `structural`, `intro_rfl`, `intro_exact` — genuine decompositions.
- `*_opaque` — verified, but the `exact`'d body is an automation blob; the
  `intro`s are real structure, the body is not.
- `exact_whole` — verified, but *zero* decomposition (one big `exact`).
- `fail` — nothing verified; `script` is empty.

A quality metric over the corpus must not count an `_opaque`/`_whole` blob as a
genuine simplification — hence the honest labels.

---

## 2. Structural recognizers (Tier-2)

Rung 0 is where actual *simplification* happens: instead of one `exact`, recurse
into the term's structure and emit branching tactics. `buildStructured` peels the
`intro` spine, then dispatches on the head of the body:

| Term shape | Recognized as | Tactic emitted |
|------------|---------------|----------------|
| `@letFun α β v (fun x => b)` (a `have`) or `let x := v; b` | intermediate value | `have x : ty := by <reverse v>`, then recurse into `b` |
| `dite c (fun h => t) (fun h => e)` | case split on a decidable prop | `by_cases h : c` then `next => …` per branch |
| `T.casesOn major minors…` | case analysis on an inductive | `cases major with \| ctor fields => …`, recursing per branch |
| `T.rec …` (genuine recursor) | structural recursion | `induction … with …`, recursing per minor premise |
| `Ctor a b …` (structure/inductive constructor) | constructor application | `refine ⟨…⟩` / `exact` of the constructor, recursing into fields |

The recursion bottoms out at non-structural sub-terms, which become `exact`
(atomic) or `exact_opaque` (blob) leaves — the same ladder, applied locally.

**Tier-3 automation is deliberately *not* reversed.** Sub-terms that are
`omega`/`simp`/`rw`/`decide` residue (dependent-motive `congrArg`, embedded
matchers) do not round-trip through delaboration. Rather than emit a fragile,
wrong guess, we keep them verbatim inside a verified `exact` labeled `*_opaque`.
(`--closers`, §4, is the opt-in attempt to do better.)

### Recognizer gotchas (load-bearing details)

- **`casesOn` vs `.rec` argument layout differ.** For `T.casesOn` the major
  premise sits at `numParams + 1 + numIndices` (*before* the minor premises);
  for `T.rec` the major is **last**. Getting this wrong picks the wrong
  discriminant.
- **`Nat.recAux` / `Nat.casesAuxOn` are `abbrev`s, not recursors.**
  `isRecCore` / `isCasesOnRecursor` return *false* on them, so
  `unfoldAuxEliminator` delta-unfolds them to the real `T.rec`/`T.casesOn` first.
- **`cases` branch binders:** name only the constructor's `numFields` in the
  `| ctor a b =>` pattern. Hypotheses `cases` reverted over the discriminant are
  auto-reintroduced into the branch — naming them in the pattern is wrong.
- **`by_cases` branches** are addressed positionally with `next => seq`, *not*
  `case pos/neg`: the `by_cases` macro tags goals with inaccessible dagger names
  that don't round-trip.
- **Binder hygiene:** inaccessible/hygienic binder names (rendered with `✝`, or
  anonymous) can't be source identifiers, so the `intro` spine renames them to
  fresh `x0`, `x1`, … (`sanitizeBinder`).

---

## 3. Verification: two stages, and why it must be sound

Generation is heuristic, so **verification is the contract**. There are two
stages, and both apply the same soundness guards.

### Stage A — `tryElab` (in-memory)

Run the candidate `Syntax` against a fresh metavariable goal of type `ty`:

1. `runTactic` the candidate; if any goal is **left open**, reject.
2. Instantiate the resulting proof term `v'`.
3. Reject if `v'.hasSorry`.
4. Accept iff `isDefEq v v'`.

### Stage B — `verifyRendered` (re-parse the string)

`runTactic` (in-memory `Syntax`) is **more permissive** than a fresh
parse→elaborate — notably about hygienic `case` tags — so a candidate can pass
Stage A yet produce a *string* that is not a valid proof. Since the string is
what we actually store, we re-check it:

1. `runParserCategory … term` on the rendered `by …` **string**; reject on parse
   error.
2. Elaborate it against `ty` **with `errToSorry := false`**.
3. Reject if the result `hasSorry`; accept iff `isDefEq v e`.

A candidate is emitted only if **both** stages pass.

### The proof-irrelevance trap (the single most important point)

> On a `Prop` goal, **any** two proofs of the same proposition are definitionally
> equal. So `isDefEq v v'` is **vacuously true** for *any* `v'` of type `ty` —
> including a `sorryAx`-filled term produced by a tactic that only half-closed
> the goal.

With Lean's default `errToSorry := true`, a partially-failing tactic block
silently becomes `sorry` and would then be *accepted* by a naive defeq check.
This actually happened: an earlier version stored **80/261 (31%) invalid
scripts**. The fix, mandatory at every check above and in any audit harness:

1. **elaborate with `errToSorry := false`** so a failed elaboration *throws*
   (caught → rejected) instead of silently becoming `sorry`; and
2. **reject `Expr.hasSorry`** before the `isDefEq`.

Any round-trip or audit harness *without* these guards is itself unsound and will
report a false "0 failures".

### Don't-abort-the-run discipline

Verification uses **`tryCatchRuntimeEx`**, not a plain `try`/`catch`. Lean's
`Core.tryCatch` auto-rethrows *runtime* exceptions (heartbeat / recursion
timeouts) before a normal handler runs, so a bare `catch` would let a single
candidate's timeout escape and abort the entire extraction. `tryCatchRuntimeEx`
catches those too — degrading the bad candidate to "doesn't verify" and falling
back — while still re-raising genuine interrupts so the run stays cancellable.

Each verification attempt also runs under a **fresh per-attempt heartbeat
baseline** (`withCurrHeartbeats`) and a **bounded cap** (`maxHeartbeats := budget`,
~4M raw), so a pathological candidate (re-elaborating a giant `omega` blob) times
out *locally* without consuming the whole-run budget. State is isolated with
`withoutModifyingState` / `withNewMCtxDepth`, so neither stage perturbs the
surrounding environment walk.

---

## 4. `--closers` (opt-in)

By proof irrelevance, *any* tactic that closes the goal is a valid proof. So for
an opaque (non-atomic) body we can try a menu of goal-closers — `simp`, `omega`,
`simp_all`, `decide`, … — and, if one verifies, emit the high-level tactic the
author likely wrote instead of a giant `exact` blob (`intro_omega`, `intro_simp`,
…). This ranks above the opaque `exact` so a recovered one-liner wins.

It is **off by default**: trying the menu across every opaque proof, each under
its own (tighter) heartbeat cap and double verification, is ~20× slower
(~10 min vs ~40 s on the LeanSQLite corpus). Closers are verified with a smaller
budget than the structural/exact path — a closer that needs the full budget to
fire is not the fast proof we were hoping to recover.

---

## 5. Results & limits

On the LeanSQLite corpus (283 theorems, **sound** verifier):

- **132 / 283** genuine decompositions (of which **50** `structural`),
- **71** `fail`,
- the rest `*_opaque` / `exact_whole` (verified, low/zero decomposition),
- **0 / 212** stored scripts invalid on an independent re-elaboration audit.

The remaining `fail`s are `rw`/`simp`/`match` residue with dependent-motive
`congrArg` and embedded matchers that don't round-trip through delaboration even
as a whole-term `exact`. Emitting `fail` (no script) for those is correct, not a
bug — closing the gap would require partial `rw`/`simp` recovery (a fragile
Tier-3 we deliberately don't attempt).

> Historical note: pre-soundness-fix numbers (187/283, 104 structural, 22 fail,
> "382/382 round-trip") were **unsound** — proof irrelevance + `errToSorry` let
> the verifier accept `sorry`-laced scripts. The honest counts above are lower
> *and* correct.

---

## 6. Where this runs

`ReverseElab` is a pure-helper module (no `initialize` block) shared by:

- **`WorkerPlugins.CorpusManifest`** — calls `reverseProof info.type v` for each
  theorem (gated on the request's `reverseElab` flag), *inside the worker*. This
  is the intended home: the worker is a real frontend, so the tactics the
  candidates use (`cases`, `rfl`, `simp`, …) are registered and re-elaboration
  happens in the file's true context.
- the legacy import-based extractor in `lean-extract` (`Corpus/Extract.lean`),
  via the same entry point.

Both share **one copy** of this code precisely because the verify-and-fallback
guards are soundness-critical and must never diverge between callers.

### Entry point

```lean
structure ScriptResult where
  script : String   -- the `by …` block, or "" on failure
  method : String   -- structural / rfl / exact / *_opaque / exact_whole / fail

def reverseProof (ty v : Expr) (enableClosers : Bool := false) : MetaM ScriptResult
```

`reverseProof` builds the candidate ladder for `v : ty`, returns the first
candidate that passes both verification stages (with its label), or
`{ script := "", method := "fail" }`.
