module

public import Silmaril.Logic.ACL2.Standard.ObjectOrder.Defs
public import Silmaril.Logic.ACL2.X86Run.Status.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

/-- Remaining X86ISA field predicates in the translated element dispatcher. They
represent the non-NIL projections of ENV-ALISTP and TLBP. -/
structure FieldPredicates where
  environment : Object → Bool
  tlb : Object → Bool

inductive FieldType where
  | any
  | boolean
  | keyword
  | natural
  | signed (width : Nat)
  | unsigned (width : Nat)
  | environment
  | tlb
  | tty
  deriving Repr

def unsignedByteP (w : Nat) (v : Object) : Bool :=
  v.integerValue?.any (fun n => decide (0 ≤ n ∧ n < (2 : Int) ^ w))

/-- TTY-BUFFERP recognizes proper lists of unsigned 8-bit integers. -/
def ttyBufferP : Object → Bool
  | .cons val tail => unsignedByteP 8 val && ttyBufferP tail
  | x => decide (x = .nil)

def FieldType.accepts (p : FieldPredicates) (v : Object) : FieldType → Bool
  | .any => true
  | .boolean => decide (v = .nil ∨ v = .truth)
  | .keyword => match v with
    | .symbol s => decide (s.package.toLeanString = "KEYWORD")
    | _ => false
  | .natural => v.integerValue?.any (fun n => decide (0 ≤ n))
  | .signed w =>
    let limit := (2 : Int) ^ (w - 1)
    decide (0 < w) && v.integerValue?.any (fun n => decide (-limit ≤ n ∧ n < limit))
  | .unsigned w => unsignedByteP w v
  | .environment => p.environment v
  | .tlb => p.tlb v
  | .tty => ttyBufferP v

structure FieldRule where
  name : Object
  fallback : Object
  fieldType : FieldType

def fieldRule (rules : List FieldRule) (name : Object) : FieldRule :=
  (rules.find? (fun r => decide (r.name = name))).getD ⟨name, .nil, .any⟩

/-- The X86REC-P1 entry-list recursion. XR keys remain arbitrary objects. Both
field functions use CAR of the key, including the NIL result on atomic keys. -/
def entriesP (rules : List FieldRule) (p : FieldPredicates) : Object → Bool
  | .cons (.cons k v) tail =>
    let rule := fieldRule rules k.car
    entriesP rules p tail &&
      rule.fieldType.accepts p v &&
      decide (v ≠ rule.fallback) &&
      (if tail = .nil then true else ObjectOrder.before k tail.car.car)
  | x => decide (x = .nil)

def recordPrimitives (rules : List FieldRule) (p : FieldPredicates) : RecordPrimitives :=
  ⟨entriesP rules p, ObjectOrder.before⟩

end Silmaril.Logic.ACL2.X86Run.Status
