/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean.Data.Lsp.TextSync
import Lean.Data.Lsp.Utf16
import Lean.Data.Position

/-!
Compute a single LSP `TextDocumentContentChangeEvent` from the difference between two snapshots
of a file's text.

Strategy: scan the strings forward and backward to find the smallest interval `[firstDiff, lastDiff]`
that contains all changed bytes, then emit one `rangeChange` for that interval. If the strings are
identical we emit nothing; if the diff covers more than half the file we emit a `fullChange` since
the worker will re-elaborate from the top either way.

This is not a minimum edit script — it's a coarse single-range edit. That's intentional: the file
worker only restarts elaboration at the command boundary at-or-above the edit, so a tight range is
no better than a slightly looser one in practice, and a single-range diff is cheap.
-/

namespace Workers

open Lean Lsp

/-- Find the smallest interval `[i, jOld)` of `oldText`'s bytes (and the corresponding `[i, jNew)`
of `newText`'s bytes) that contains all differences. Both endpoints are aligned to UTF-8 codepoint
boundaries — we walk back into any continuation bytes we may have landed inside.

Returns `none` if the strings are byte-identical. -/
private def diffRange (oldText newText : String) : Option (Nat × Nat × Nat) := Id.run do
  if oldText == newText then
    return none
  let oldBytes := oldText.toByteArray
  let newBytes := newText.toByteArray
  let oldEnd := oldBytes.size
  let newEnd := newBytes.size
  let limit := min oldEnd newEnd
  -- Forward scan: first differing byte.
  let mut i : Nat := 0
  while i < limit && oldBytes[i]! == newBytes[i]! do
    i := i + 1
  -- If `i` lands in the middle of a multi-byte codepoint, walk back to the leading byte.
  -- Continuation bytes have the bit pattern `10xxxxxx`.
  while i > 0 && (oldBytes[i]! &&& 0xC0) == 0x80 do
    i := i - 1
  -- Backward scan: matching suffix length.
  let mut jOld := oldEnd
  let mut jNew := newEnd
  while jOld > i && jNew > i && oldBytes[jOld - 1]! == newBytes[jNew - 1]! do
    jOld := jOld - 1
    jNew := jNew - 1
  -- If `jOld` (and `jNew`) land in the middle of a multi-byte codepoint, walk forward.
  while jOld < oldEnd && (oldBytes[jOld]! &&& 0xC0) == 0x80 do
    jOld := jOld + 1
    jNew := jNew + 1
  return some (i, jOld, jNew)

/-- Compute a `TextDocumentContentChangeEvent` for the edit from `oldText` to `newText`.

Both arguments should be normalized to LF line endings before calling, matching what we store
after each `didOpen` / `didChange` we send to the worker. Returns `none` if the texts are equal.

If the changed region covers more than half of `oldText`, we emit a `fullChange` instead of a
`rangeChange`. -/
def diffToChange (oldText newText : String) : Option TextDocumentContentChangeEvent := Id.run do
  let some (i, jOld, jNew) := diffRange oldText newText | return none
  let oldSize := oldText.utf8ByteSize
  let changedBytes := jOld - i
  if oldSize > 0 && 2 * changedBytes > oldSize then
    return some (.fullChange newText)
  let oldMap := oldText.toFileMap
  let startPos := oldMap.utf8PosToLspPos ⟨i⟩
  let endPos   := oldMap.utf8PosToLspPos ⟨jOld⟩
  let replacement := String.Pos.Raw.extract newText ⟨i⟩ ⟨jNew⟩
  return some (.rangeChange { start := startPos, «end» := endPos } replacement)

end Workers
