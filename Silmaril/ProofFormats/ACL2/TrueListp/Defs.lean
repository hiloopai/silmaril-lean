module

public import Silmaril.Formats.SExp.CommonLisp.Defs
public import Silmaril.Logic.ACL2.Translated.Recursive.Defs
public import Silmaril.Logic.ACL2.Recursive.Certificate

@[expose] public section

namespace Silmaril.ProofFormats.ACL2.TrueListp

open Silmaril.Logic.ACL2 Silmaril.Formats.CommonLisp
open Silmaril.Logic.ACL2.Translated (Raw RawArgs Primitive ifName)

def functionName : Name := ⟨"ACL2", "TRUE-LISTP"⟩
def quoteName : Name := ⟨"COMMON-LISP", "QUOTE"⟩
def countName : Name := ⟨"ACL2", "ACL2-COUNT"⟩

def properList : Datum → Option (List Datum)
  | .nil => some []
  | .cons head tail => (head :: ·) <$> properList tail
  | _ => none

/-- The exporter writes resolved home-package identities. The Lisp reader only supplies
the two escaped constituents, and the object layer checks their ACL2 character range. -/
def readName : Datum → Option Name
  | .atom (.qualified package spelling true) => do
      let name : Name := ⟨package, spelling⟩
      let _ ← Standard.Symbol.ofName? name
      return name
  | _ => none

def readArity : Datum → Option Nat
  | .atom (.rational q) => if q.den = 1 ∧ 0 ≤ q.num then some q.num.toNat else none
  | _ => none

mutual
  def readTerm : Datum → Option Raw
    | .atom symbol => Raw.var <$> readName (.atom symbol)
    | .cons head tail => do
        let name ← readName head
        if name = quoteName then
          let .cons obj .nil := tail | none
          return .quote (.symbol (← readName obj))
        else if name = ifName then
          let .cons test (.cons yes (.cons no .nil)) := tail | none
          return .ite (← readTerm test) (← readTerm yes) (← readTerm no)
        else
          return .call name (← readArgs tail)
    | .nil => none

  def readArgs : Datum → Option RawArgs
    | .nil => some .nil
    | .cons head tail => do return .cons (← readTerm head) (← readArgs tail)
    | _ => none
end

structure Declaration where
  name : Name
  arity : Nat
  formals : List Name
  body : Raw

def readDeclaration (sexp : Datum) : Option Declaration := do
  let [name, arity, formals, body] ← properList sexp | none
  return ⟨← readName name, ← readArity arity, ← (← properList formals).mapM readName,
    ← readTerm body⟩

def readEntry (sexp : Datum) : Option (Name × Nat) := do
  let [name, arity] ← properList sexp | none
  return (← readName name, ← readArity arity)

structure Export where
  definition : Declaration
  equality : Declaration
  measure : Raw
  domain : Name
  relation : Name
  arities : List (Name × Nat)

/-- Decode the concrete, pinned export. All names in the terms and metadata are qualified. -/
def read (text : String) : Option Export := do
  let [.atom (.string "silmaril-acl2-recursive-v1"),
    .atom (.string "bc6f4f49e81a0711214a8d91f0d06e0e084d2204"),
    .atom (.string "66d80ea68f664b931f8982b607fe2305f3cec0e4"),
    .atom (.string "50247ed0609257bcf08c4c6d365ccf1695bd2cbd2dfedff0f7bc516f9ce828b1"),
    definition, equality, measure, domain, relation, arities] ←
      parse? text >>= properList | none
  return ⟨← readDeclaration definition, ← readDeclaration equality, ← readTerm measure,
    ← readName domain, ← readName relation, ← (← properList arities).mapM readEntry⟩

def Export.signature (source : Export) : Signature :=
  ⟨fun name => (source.arities.find? fun entry => decide (entry.1 = name)).map Prod.snd⟩

def Export.members (source : Export) : Signature :=
  Signature.empty.add source.definition.name source.definition.formals.length

theorem Export.memberArity (source : Export) {k : Nat} (f : source.members.Symbol k) :
    source.definition.formals.length = k := by
  have h := f.property
  change (if f.val = source.definition.name then some source.definition.formals.length
    else none) = some k at h
  split at h <;> simp_all

def validEquality (d : Declaration) : Bool :=
  match d.formals, d.body with
  | [x, y], .call name (.cons (.var a) (.cons (.var b) .nil)) =>
      decide (d.name = Translated.Recursive.eqName ∧ d.arity = 2 ∧ x ≠ y ∧
        name = Primitive.equal.name ∧ a = x ∧ b = y)
  | _, _ => false

/-- This profile admits ACL2-COUNT on the single bound argument under the default ordinal order. -/
def Export.measureSlot (source : Export) : Option (Fin source.definition.formals.length) :=
  match source.definition.formals with
  | [x] => do
      let .call name (.cons (.var a) .nil) := source.measure | none
      guard (name = countName ∧ a = x ∧ source.domain = ⟨"ACL2", "O-P"⟩ ∧
        source.relation = ⟨"ACL2", "O<"⟩)
      return ⟨0, Nat.zero_lt_succ _⟩
  | _ => none

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
    Recursive.Block Signature.empty where
  members := source.members
  fresh _ := rfl
  body f := source.memberArity f ▸ checked.body

def Lowered.measureArgument {source : Export} (checked : Lowered source) :
    Recursive.MeasureArgument source.members :=
  fun f => checked.measured.cast (source.memberArity f)

end Silmaril.ProofFormats.ACL2.TrueListp
