module

public import Silmaril.Formats.Arrow.LargeBinary.Defs

/-! LargeUtf8 checks the signed i64 Binary geometry, then interprets only
present slots as UTF-8. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8

abbrev Buffers := Binary.Buffers
abbrev Column := List (Option String)

inductive Error where
  | binary (cause : Binary.Error)
  | invalidUtf8 (slot : Nat)
  deriving DecidableEq, Repr

/-- A null still has checked offsets. Its bytes are unobserved, as in the
plain Utf8 reader. -/
def readSlot (buffers : Buffers) (index : Nat) : Except Error (Option String) := do
  let selected ← (LargeBinary.readSlot buffers index).mapError .binary
  match selected with
  | none => .ok none
  | some bytes =>
    match String.fromUTF8? bytes.toByteArray with
    | none => .error (.invalidUtf8 index)
    | some text => .ok (some text)

def readColumn (limits : Limits) (nullable : Bool) (node : FieldNode) (buffers : Buffers) :
    Except Error Column := do
  (Binary.checkColumn limits nullable node buffers).mapError .binary
  let _ ← (LargeBinary.readOffset buffers 0).mapError .binary
  let values ← (List.range node.length).mapM (readSlot buffers)
  if values.countP Option.isNone ≠ node.nullCount then .error (.binary (.ipc (.malformed .validityBitmap)))
  else .ok values

def SlotWire (buffers : Buffers) (index : Nat) (value : Option String) : Prop :=
  ∃ lo hi valid, LargeBinary.OffsetWire buffers index lo ∧ LargeBinary.OffsetWire buffers (index + 1) hi ∧
    lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
    if valid then
      let bytes := (buffers.data.slice lo (hi - lo)).toByteArray
      bytes.IsValidUTF8 ∧ value.map String.toByteArray = some bytes
    else value = none

def ColumnWire (node : FieldNode) (buffers : Buffers) (values : Column) : Prop :=
  (∃ initial, LargeBinary.OffsetWire buffers 0 initial) ∧
    List.Forall₂ (SlotWire buffers) (List.range node.length) values ∧
    values.countP Option.isNone = node.nullCount

end Silmaril.Formats.Arrow.LargeUtf8
