module

public import Silmaril.Formats.SExp.CommonLisp.Defs
public import Silmaril.Logic.ACL2.Translated.Recursive.Defs
public import Silmaril.Logic.ACL2.Recursive.Certificate

@[expose] public section

namespace Silmaril.ProofFormats.ACL2.TranslatedSource

open Silmaril.Logic.ACL2 Silmaril.Formats.CommonLisp
open Silmaril.Logic.ACL2.Translated (Raw RawArgs ifName)

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

/-- Read the common header of a logical export from the pinned stock ACL2 8.7 world. -/
def records (text : String) : Option (List Datum) := do
  let .atom (.string "silmaril-acl2-recursive-v1") ::
      .atom (.string "bc6f4f49e81a0711214a8d91f0d06e0e084d2204") ::
      .atom (.string "66d80ea68f664b931f8982b607fe2305f3cec0e4") ::
      .atom (.string "50247ed0609257bcf08c4c6d365ccf1695bd2cbd2dfedff0f7bc516f9ce828b1") ::
      fields ← parse? text >>= properList | none
  return fields

def signature (arities : List (Name × Nat)) : Signature :=
  ⟨fun name => (arities.find? fun entry => decide (entry.1 = name)).map Prod.snd⟩

def Declaration.members (d : Declaration) : Signature :=
  Signature.empty.add d.name d.formals.length

theorem Declaration.memberArity (d : Declaration) {k : Nat} (f : d.members.Symbol k) :
    d.formals.length = k := by
  have h := f.property
  change (if f.val = d.name then some d.formals.length else none) = some k at h
  split at h <;> simp_all

/-- Resolve an ACL2-COUNT measure argument in the same lexical scope as the body. -/
def measureSlot (scope : List Name) (measure : Raw) (domain relation : Name) :
    Option (Fin scope.length) := do
  let .call name (.cons (.var formal) .nil) := measure | none
  guard (name = countName ∧ domain = ⟨"ACL2", "O-P"⟩ ∧ relation = ⟨"ACL2", "O<"⟩)
  let .var slot _ ← Translated.lower Signature.empty scope (.var formal)
  return slot

/-- Use the declared name and arity to assemble a singleton block from its lowered body. -/
def Declaration.block (d : Declaration)
    (body : Recursive.Body Signature.empty d.members d.formals.length) :
    Recursive.Block Signature.empty where
  members := d.members
  fresh _ := rfl
  body f := d.memberArity f ▸ body

def Declaration.measureArgument (d : Declaration) (slot : Fin d.formals.length) :
    Recursive.MeasureArgument d.members :=
  fun f => slot.cast (d.memberArity f)

end Silmaril.ProofFormats.ACL2.TranslatedSource
