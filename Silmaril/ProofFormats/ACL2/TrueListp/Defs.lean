module

public import Silmaril.ProofFormats.ACL2.Translated.Defs

@[expose] public section

namespace Silmaril.ProofFormats.ACL2.TrueListp

open Silmaril.Logic.ACL2 TranslatedSource
open Silmaril.Logic.ACL2.Translated (Raw RawArgs Primitive ifName)

export TranslatedSource (quoteName countName properList readName readArity readTerm readArgs
  readDeclaration readEntry)

def functionName : Name := ⟨"ACL2", "TRUE-LISTP"⟩
abbrev Declaration := TranslatedSource.Declaration

structure Export where
  definition : Declaration
  equality : Declaration
  measure : Raw
  domain : Name
  relation : Name
  arities : List (Name × Nat)

/-- Decode the concrete, pinned export. All names in the terms and metadata are qualified. -/
def read (text : String) : Option Export := do
  let [definition, equality, measure, domain, relation, arities] ← records text | none
  return ⟨← readDeclaration definition, ← readDeclaration equality, ← readTerm measure,
    ← readName domain, ← readName relation, ← (← properList arities).mapM readEntry⟩

def Export.signature (source : Export) : Signature :=
  TranslatedSource.signature source.arities

def Export.members (source : Export) : Signature :=
  source.definition.members

theorem Export.memberArity (source : Export) {k : Nat} (f : source.members.Symbol k) :
    source.definition.formals.length = k :=
  source.definition.memberArity f

def validEquality (d : Declaration) : Bool :=
  match d.formals, d.body with
  | [x, y], .call name (.cons (.var a) (.cons (.var b) .nil)) =>
      decide (d.name = Translated.Recursive.eqName ∧ d.arity = 2 ∧ x ≠ y ∧
        name = Primitive.equal.name ∧ a = x ∧ b = y)
  | _, _ => false

/-- This profile admits ACL2-COUNT on the single bound argument under the default ordinal order. -/
def Export.measureSlot (source : Export) : Option (Fin source.definition.formals.length) :=
  if source.definition.formals.length = 1 then
    TranslatedSource.measureSlot source.definition.formals source.measure source.domain source.relation
  else none

def expectedArities : List (Name × Nat) :=
  [(ifName, 3), (Translated.Recursive.conspName, 1), (Translated.Recursive.cdrName, 1), (functionName, 1),
    (Translated.Recursive.eqName, 2), (Primitive.equal.name, 2), (countName, 1)]

def Export.matchesProfile (source : Export) : Bool :=
  decide (source.definition.name = functionName ∧ source.definition.arity = 1 ∧
    source.definition.formals.length = source.definition.arity ∧ source.arities = expectedArities) &&
    validEquality source.equality

/-- A lowered body carries both the source-indexed checker output and the equality witnessing
the structural projection used to build the recursive block. -/
structure Lowered (source : Export) where
  profile : source.matchesProfile = true
  checked : Translated.Checked source.signature source.definition.formals source.definition.body
  equality : Translated.Checked Signature.empty source.equality.formals source.equality.body
  measured : Fin source.definition.formals.length
  measureChecked : source.measureSlot = some measured
  body : Recursive.Body Signature.empty source.members source.definition.formals.length
  lowered : Translated.Recursive.lowerBody source.members checked = some body

def lower (source : Export) : Option (Lowered source) :=
  if profile : source.matchesProfile = true then do
    let checked ← Translated.lower source.signature source.definition.formals source.definition.body
    let equality ← Translated.lower Signature.empty source.equality.formals source.equality.body
    match hMeasure : source.measureSlot,
        hBody : Translated.Recursive.lowerBody source.members checked with
    | some measured, some body => some ⟨profile, checked, equality, measured, hMeasure, body, hBody⟩
    | _, _ => none
  else none

/-- The singleton block used by the ordinary termination certificate checker. -/
def Lowered.block {source : Export} (checked : Lowered source) :
    Recursive.Block Signature.empty :=
  source.definition.block checked.body

def Lowered.measureArgument {source : Export} (checked : Lowered source) :
    Recursive.MeasureArgument source.members :=
  source.definition.measureArgument checked.measured

end Silmaril.ProofFormats.ACL2.TrueListp
