module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Defs

/-! # Schedule case tests and branch-local operands -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (Region Tm)
open NamedFlat (BindingTypes)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)

variable {F : Type} {Γ : List PacketType} {a b : PacketType} {sig : PrimitiveSignature F}

/-- The operand supplies one sum to the sole dispatch. Both case payloads
stay at slot zero, and older slots move past the schedule. -/
def scheduleCaseWithBindings (test : Operand sig Γ (.coprod a b))
    (left right : Region F × BindingTypes PacketType) : Region F × BindingTypes PacketType :=
  let scheduled := test.schedule
  let shift := Silmaril.DeBruijn.lift scheduled.requests.shift
  scheduled.wrapRegion
    (.case (scheduled.value.erase position) (left.1.renameVars shift) (right.1.renameVars shift))
    (.node none .empty left.2 right.2)

def scheduleCase (test : Operand sig Γ (.coprod a b)) (left right : Region F) : Region F :=
  (scheduleCaseWithBindings test (left, .empty) (right, .empty)).1

structure CaseTest (sig : PrimitiveSignature F) (Γ : List PacketType) (written : Tm F) where
  leftType : PacketType
  rightType : PacketType
  operand : Operand sig Γ (.coprod leftType rightType)
  source_eq : written = operand.written

def readCaseTest [DecidableEq F] (sig : PrimitiveSignature F) (Γ : List PacketType) (test : Tm F) :
    Option (CaseTest sig Γ test) := do
  let ⟨.coprod a b, arg⟩ ← readOperand sig Γ test | none
  if exactTest : test = arg.written then some ⟨a, b, arg, exactTest⟩ else none

def productTypes (sig : PrimitiveSignature F) (Γ : List PacketType) (value : Tm F) :
    Option (PacketType × PacketType) := do
  let ⟨.product a b, _⟩ ← readOperand sig Γ value | none
  return (a, b)

/-- Schedule an operand inside its current arm. Record the checked type
of every generated case-result binder alongside the emitted syntax. -/
def scheduleWithBindings [DecidableEq F] (sig : PrimitiveSignature F) {labels : Nat}
    (types : Fin labels → PacketType) :
    List PacketType → Region F → Option (Region F × BindingTypes PacketType)
  | Γ, .br label arg =>
    if within : label < labels then
      (readArgument sig Γ (types ⟨label, within⟩) arg).map (fun found => scheduleJumpWithBindings label found.val)
    else none
  | Γ, .let₁ (.op op argument) tail =>
    (readArgument sig Γ (sig.argument op) argument).bind fun arg =>
      (scheduleWithBindings sig types (sig.reply op :: Γ) tail).map (hoistWithBindings op arg.val)
  | Γ, .let₁ value tail => (readOperand sig Γ value).bind fun found =>
    (scheduleWithBindings sig types (found.1 :: Γ) tail).map fun (body, bindings) =>
      (.let₁ value body, .node none .empty bindings .empty)
  | Γ, .let₂ value tail => (productTypes sig Γ value).bind fun (a, b) =>
    (scheduleWithBindings sig types (b :: a :: Γ) tail).map fun (body, bindings) =>
      (.let₂ value body, .node none .empty bindings .empty)
  | Γ, .case test left right => (readCaseTest sig Γ test).bind fun found =>
    (scheduleWithBindings sig types (found.leftType :: Γ) left).bind fun left =>
      (scheduleWithBindings sig types (found.rightType :: Γ) right).map (scheduleCaseWithBindings found.operand left)
  | _, .cfg .. => none

def scheduleCases [DecidableEq F] (sig : PrimitiveSignature F) {labels : Nat}
    (types : Fin labels → PacketType) (Γ : List PacketType) (written : Region F) : Option (Region F) :=
  (scheduleWithBindings sig types Γ written).map Prod.fst

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed
