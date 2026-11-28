module

public import Silmaril.ProofFormats.ACL2.Translated.Defs

@[expose] public section

namespace Silmaril.ProofFormats.ACL2.BinaryAppend

open Silmaril.Logic.ACL2 TranslatedSource
open Silmaril.Logic.ACL2.Translated (Raw Primitive ifName)
open Silmaril.Logic.ACL2.Translated.Recursive (endpName conspName cdrName carName)

def functionName : Name := ⟨"ACL2", "BINARY-APPEND"⟩
def atomName : Name := ⟨"COMMON-LISP", "ATOM"⟩
def notName : Name := ⟨"COMMON-LISP", "NOT"⟩

structure Export where
  definition : Declaration
  endp : Declaration
  atom : Declaration
  not : Declaration
  measure : Raw
  domain : Name
  relation : Name
  arities : List (Name × Nat)

def read (text : String) : Option Export := do
  let [definition, endp, atom, not, measure, domain, relation, arities] ← records text | none
  return ⟨← readDeclaration definition, ← readDeclaration endp, ← readDeclaration atom,
    ← readDeclaration not, ← readTerm measure, ← readName domain, ← readName relation,
    ← (← properList arities).mapM readEntry⟩

def Export.signature (source : Export) : Signature :=
  TranslatedSource.signature source.arities

def Export.measureSlot (source : Export) : Option (Fin source.definition.formals.length) :=
  TranslatedSource.measureSlot source.definition.formals source.measure source.domain source.relation

def unaryDefinition (name : Name) (check : Name → Raw → Bool) (d : Declaration) : Bool :=
  match d.formals with
  | [formal] => decide (d.name = name ∧ d.arity = 1) && check formal d.body
  | _ => false

def checkEndp (formal : Name) : Raw → Bool
  | .call name (.cons (.var arg) .nil) => decide (name = atomName ∧ arg = formal)
  | _ => false

def checkAtom (formal : Name) : Raw → Bool
  | .call name (.cons (.call inner (.cons (.var arg) .nil)) .nil) =>
      decide (name = notName ∧ inner = conspName ∧ arg = formal)
  | _ => false

def checkNot (formal : Name) : Raw → Bool
  | .ite (.var test) (.quote (.symbol yes)) (.quote (.symbol no)) =>
      decide (test = formal ∧ yes = Standard.Symbol.nil.toName ∧ no = Standard.Symbol.truth.toName)
  | _ => false

def expectedArities : List (Name × Nat) :=
  [(ifName, 3), (endpName, 1), (atomName, 1), (notName, 1),
    (conspName, 1), (Primitive.cons.name, 2), (carName, 1), (cdrName, 1),
    (functionName, 2), (countName, 1)]

def Export.matchesProfile (source : Export) : Bool :=
  decide (source.definition.name = functionName ∧ source.definition.arity = 2 ∧
    source.definition.formals.length = source.definition.arity ∧ source.definition.formals.Nodup ∧
    source.arities = expectedArities) &&
    unaryDefinition endpName checkEndp source.endp &&
    unaryDefinition atomName checkAtom source.atom &&
    unaryDefinition notName checkNot source.not

/-- Retain the source-indexed body and the checked dependencies used to normalize its guard. -/
structure Lowered (source : Export) where
  profile : source.matchesProfile = true
  checked : Translated.Checked source.signature source.definition.formals source.definition.body
  endp : Translated.Checked source.signature source.endp.formals source.endp.body
  atom : Translated.Checked source.signature source.atom.formals source.atom.body
  not : Translated.Checked source.signature source.not.formals source.not.body
  measured : Fin source.definition.formals.length
  measureChecked : source.measureSlot = some measured
  body : Recursive.Body Signature.empty source.definition.members source.definition.formals.length
  lowered : Translated.Recursive.lowerBody source.definition.members checked = some body

def lower (source : Export) : Option (Lowered source) :=
  if profile : source.matchesProfile = true then do
    let checked ← Translated.lower source.signature source.definition.formals source.definition.body
    let endp ← Translated.lower source.signature source.endp.formals source.endp.body
    let atom ← Translated.lower source.signature source.atom.formals source.atom.body
    let not ← Translated.lower source.signature source.not.formals source.not.body
    match hMeasure : source.measureSlot,
        hBody : Translated.Recursive.lowerBody source.definition.members checked with
    | some measured, some body => some ⟨profile, checked, endp, atom, not, measured, hMeasure, body, hBody⟩
    | _, _ => none
  else none

end Silmaril.ProofFormats.ACL2.BinaryAppend
