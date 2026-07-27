/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.Elab.DeclarationRange

/-! Shared navigation and source-range helpers for declaration syntax. -/

namespace Corpus.SourceSyntax

open Lean

/-- Return the first node, in pre-order, whose kind is in `kinds`. -/
partial def findByKind (stx : Syntax) (kinds : List SyntaxNodeKind) : Option Syntax :=
  if kinds.contains stx.getKind then some stx
  else match stx with
    | .node _ _ args => args.findSome? (findByKind · kinds)
    | _ => none

/-- Return a declaration's identifier node, when it has one. -/
def declarationId? (cmdStx : Syntax) : Option Syntax :=
  findByKind cmdStx [``Lean.Parser.Command.declId]

/-- For `Command.declaration`, return the inner declaration syntax.

Lean's parser stores a declaration command as `[modifiers, declaration]`, while
`Lean.Elab.getDeclarationSelectionRef` expects the inner declaration node. -/
def innerDeclarationSyntax (cmdStx : Syntax) : Syntax :=
  cmdStx.getArg 1

/-- Return the syntax Lean uses as the declaration-range selection reference. -/
def declarationSelectionRef? (cmdStx : Syntax) : Option Syntax :=
  if cmdStx.getKind == ``Lean.Parser.Command.declaration then
    some (Lean.Elab.getDeclarationSelectionRef (innerDeclarationSyntax cmdStx))
  else if (declarationId? cmdStx).isSome then
    some (Lean.Elab.getDeclarationSelectionRef cmdStx)
  else
    none

def signatureKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.declSig, ``Lean.Parser.Command.optDeclSig]

def valueKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
   ``Lean.Parser.Command.whereStructInst]

/-- The declaration value forms that can contain a theorem proof. -/
inductive DeclValueKind where
  | simple
  | equations
  | whereBody
  deriving BEq, Repr

/-- Find and classify a declaration's value node. -/
def declarationValue? (cmdStx : Syntax) : Option (DeclValueKind × Syntax) := do
  let value ← findByKind cmdStx valueKinds
  if value.getKind == ``Lean.Parser.Command.declValSimple then
    return (.simple, value)
  if value.getKind == ``Lean.Parser.Command.declValEqns then
    return (.equations, value)
  if value.getKind == ``Lean.Parser.Command.whereStructInst then
    return (.whereBody, value)
  none

/-- Extract a syntax node's source and trim trailing ASCII whitespace. -/
def sliceTrimmed (stx : Syntax) (source : String) : Option String := do
  let range ← stx.getRange?
  pure (String.Pos.Raw.extract source range.start range.stop).trimAsciiEnd.copy

/-- Extract the source signature and value from a declaration command. -/
def signatureBodyOf (cmdStx : Syntax) (source : String) :
    Option String × Option String :=
  let signature := (findByKind cmdStx signatureKinds).bind (sliceTrimmed · source)
  let body := (declarationValue? cmdStx).bind fun
    | (.simple, value) => sliceTrimmed value[1] source
    | (_, value) => sliceTrimmed value source
  (signature, body)

/-- Return the complete source range of a declaration command. -/
def commandRange? (cmdStx : Syntax) : Option Lean.Syntax.Range :=
  cmdStx.getRange?

/-- Return the range replaced when erasing a declaration value.

For `:= term`, only `term` is selected. Equation and `where` forms include their
entire value syntax and therefore require a replacement beginning with `:=`. -/
def proofRange? (cmdStx : Syntax) : Option (DeclValueKind × Lean.Syntax.Range) := do
  let (kind, value) ← declarationValue? cmdStx
  let range ← match kind with
    | .simple => value[1].getRange?
    | .equations | .whereBody => value.getRange?
  return (kind, range)

/-- Position key for a syntax node's leading source position. -/
def syntaxKey? (fileMap : FileMap) (stx : Syntax) : Option (Nat × Nat) := do
  let rawPos ← stx.getPos?
  let pos := fileMap.toPosition rawPos
  return (pos.line, pos.column)

/-- Position key for a declaration's source-local identifier token. -/
def declarationNameKey? (fileMap : FileMap) (cmdStx : Syntax) : Option (Nat × Nat) := do
  let rawPos ← match declarationId? cmdStx with
    | some declId => declId[0].getPos?
    | none => cmdStx.getPos?
  let pos := fileMap.toPosition rawPos
  return (pos.line, pos.column)

/-- Position key corresponding to `findDeclarationRanges?.selectionRange.pos`. -/
def declarationKey? (fileMap : FileMap) (cmdStx : Syntax) : Option (Nat × Nat) :=
  (declarationSelectionRef? cmdStx).bind (syntaxKey? fileMap ·) <|>
    declarationNameKey? fileMap cmdStx

/-- All source positions that may identify this declaration in downstream maps. -/
def declarationKeys (fileMap : FileMap) (cmdStx : Syntax) : Array (Nat × Nat) := Id.run do
  let mut keys := #[]
  if let some key := declarationNameKey? fileMap cmdStx then
    keys := keys.push key
  if let some key := declarationKey? fileMap cmdStx then
    if !keys.contains key then
      keys := keys.push key
  return keys

/-- Map named declaration positions to their source signatures and values. -/
def buildSourceMap (source : String) (commands : Array Syntax) :
    Std.HashMap (Nat × Nat) (Option String × Option String) := Id.run do
  let fileMap := source.toFileMap
  let mut result : Std.HashMap (Nat × Nat) (Option String × Option String) := {}
  for cmdStx in commands do
    if (declarationId? cmdStx).isSome then
      for key in declarationKeys fileMap cmdStx do
        result := result.insert key (signatureBodyOf cmdStx source)
  return result

/-- Map declaration positions to complete command source. -/
def buildDeclSourceMap (source : String) (commands : Array Syntax) :
    Std.HashMap (Nat × Nat) String := Id.run do
  let fileMap := source.toFileMap
  let mut result : Std.HashMap (Nat × Nat) String := {}
  for cmdStx in commands do
    if (declarationId? cmdStx).isSome then
      if let some commandSource := sliceTrimmed cmdStx source then
        for key in declarationKeys fileMap cmdStx do
          result := result.insert key commandSource
  return result

end Corpus.SourceSyntax
