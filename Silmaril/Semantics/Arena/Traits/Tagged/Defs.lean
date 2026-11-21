module

public import Silmaril.Semantics.Arena.Traits.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Traits.Tagged

variable {Kind : Type} {Key Name Obj : Kind → Type}

/-- The kind is part of handle identity, even if all key carriers are `Nat`. -/
abbrev Handle (Key : Kind → Type) := Sigma Key

abbrev Spaces (Key Name Obj : Kind → Type) := (kind : Kind) → Arena.State (Key kind) (Name kind) (Obj kind)
abbrev Cell (Name Obj : Kind → Type) := Σ kind, Slot (Name kind) (Obj kind)

/-- An erased payload lane can store malformed cells. A hole is still `none`;
an occupied reservation still has an explicit tag and slot. -/
abbrev Table (Key Name Obj : Kind → Type) := Handle Key → Option (Cell Name Obj)

def pack (spaces : Spaces Key Name Obj) : Table Key Name Obj :=
  fun handle => (spaces handle.1 handle.2).map (Sigma.mk handle.1)

def Coherent (table : Table Key Name Obj) : Prop :=
  ∀ handle cell, table handle = some cell → cell.1 = handle.1

inductive TagFault (Kind : Type) where
  | wrongKind (found : Kind)
  deriving DecidableEq, Repr

def readSlot [DecidableEq Kind] (table : Table Key Name Obj) (kind : Kind) (key : Key kind) :
    Except (TagFault Kind) (Option (Slot (Name kind) (Obj kind))) :=
  match table ⟨kind, key⟩ with
  | none => .ok none
  | some ⟨actual, slot⟩ =>
    if eq : actual = kind then .ok (some (eq ▸ slot)) else .error (.wrongKind actual)

def read [DecidableEq Kind] (table : Table Key Name Obj) (kind : Kind) (key : Key kind) :
    Except (TagFault Kind) (Mutable.Cell (Obj kind)) :=
  (readSlot table kind key).map (·.map Slot.payload)

def decode [DecidableEq Kind] (table : {table : Table Key Name Obj // Coherent table}) : Spaces Key Name Obj :=
  fun kind key => match readSlot table.val kind key with
    | .ok slot => slot
    | .error _ => none

def overwrite [DecidableEq Kind] [∀ kind, DecidableEq (Key kind)] (table : Table Key Name Obj)
    (kind : Kind) (key : Key kind) (slot : Option (Slot (Name kind) (Obj kind))) : Table Key Name Obj :=
  fun query => if (⟨kind, key⟩ : Handle Key) = query then slot.map (Sigma.mk kind) else table query

def update [DecidableEq Kind] [∀ kind, DecidableEq (Key kind)] (spaces : Spaces Key Name Obj)
    (kind : Kind) (key : Key kind) (slot : Option (Slot (Name kind) (Obj kind))) : Spaces Key Name Obj :=
  fun query => if eq : kind = query then eq ▸ (spaces kind).replaceAt key slot else spaces query

/-- Edge of the raw tagged table: reject a wrong tag rather than treating it
as a vacant slot. A successful edit uses exactly the ordinary `Change` law. -/
def change [DecidableEq Kind] [∀ kind, DecidableEq (Key kind)] (kind : Kind) (key : Key kind)
    (operation : Mutable.Change (Obj kind)) :
    Mutable.Mutation (Table Key Name Obj) (Sum (TagFault Kind) Arena.Fault) Unit := fun table =>
  match readSlot table kind key with
  | .error fault => .error (.inl fault)
  | .ok cell => ((operation.apply cell).mapError Sum.inr).map fun slot => ((), overwrite table kind key slot)

def changeSpaces [DecidableEq Kind] [∀ kind, DecidableEq (Key kind)] (kind : Kind) (key : Key kind)
    (operation : Mutable.Change (Obj kind)) : Mutable.Mutation (Spaces Key Name Obj) Arena.Fault Unit := fun spaces =>
  (operation.apply (spaces kind key)).map fun slot => ((), update spaces kind key slot)

def arena [DecidableEq Kind] [∀ kind, DecidableEq (Key kind)] (kind : Kind) :
    ArenaApi (Spaces Key Name Obj) (Key kind) (Obj kind) Empty where
  read spaces key := (spaces kind key).map Slot.payload
  change key operation := Step.ofModel (changeSpaces kind key operation)

end Silmaril.Semantics.Arena.Traits.Tagged
