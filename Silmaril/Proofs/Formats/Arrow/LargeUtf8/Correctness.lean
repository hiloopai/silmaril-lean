module

public import Silmaril.Formats.Arrow.LargeUtf8.Defs
import Silmaril.Formats.Arrow.Binary.Thms
import Silmaril.Prelude.Bytes.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeUtf8

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open LargeUtf8

private theorem utf8_exact {bytes : ByteArray} {text : String}
    (read : String.fromUTF8? bytes = some text) : bytes.IsValidUTF8 ∧ text.toByteArray = bytes := by
  unfold String.fromUTF8? at read
  split at read
  · rename_i valid
    cases read
    exact ⟨valid, rfl⟩
  · cases read

private theorem readSlot_sound {buffers : Buffers} {index : Nat} {value : Option String}
    (read : readSlot buffers index = .ok value) : SlotWire buffers index value := by
  unfold readSlot at read
  cases bytesRead : LargeBinary.readSlot buffers index with
  | error cause => simp [bytesRead, Except.mapError, Bind.bind, Except.bind] at read
  | ok result =>
    have physical : Binary.Offsets.SlotWire .i64 buffers index result :=
      Binary.Offsets.readSlot_sound bytesRead
    obtain ⟨lo, hi, valid, first, next, order, bitmap, selected⟩ := physical
    refine ⟨lo, hi, valid, first, next, order, bitmap, ?_⟩
    cases valid
    · change result = none at selected
      subst result
      simpa [bytesRead, Except.mapError, Bind.bind, Except.bind, eq_comm] using read
    · change result = some (buffers.data.slice lo (hi - lo)) at selected
      subst result
      cases decoded : String.fromUTF8? (buffers.data.slice lo (hi - lo)).toByteArray with
      | none => simp [bytesRead, decoded, Except.mapError, Bind.bind, Except.bind] at read
      | some text =>
        simp [bytesRead, decoded, Except.mapError, Bind.bind, Except.bind] at read
        subst value
        simpa using utf8_exact decoded

private theorem readSlots_sound {buffers : Buffers} {slots : List Nat} {values : LargeUtf8.Column}
    (read : slots.mapM (readSlot buffers) = .ok values) :
    List.Forall₂ (SlotWire buffers) slots values := by
  induction slots generalizing values with
  | nil =>
    cases read
    exact .nil
  | cons slot rest ih =>
    rw [List.mapM_cons] at read
    cases first : readSlot buffers slot <;> cases next : rest.mapM (readSlot buffers) <;>
      simp [first, next, Bind.bind, Except.bind, Pure.pure, Except.pure] at read
    subst values
    exact .cons (readSlot_sound first) (ih next)

theorem readColumn_sound {limits : Limits} {nullable : Bool} {node : FieldNode}
    {buffers : Buffers} {values : LargeUtf8.Column}
    (read : readColumn limits nullable node buffers = .ok values) :
    Binary.checkColumn limits nullable node buffers = .ok () ∧ ColumnWire node buffers values := by
  unfold readColumn at read
  cases checked : Binary.checkColumn limits nullable node buffers with
  | error cause => simp [checked, Except.mapError, Bind.bind, Except.bind] at read
  | ok checkedUnit =>
    cases checkedUnit
    cases initial : LargeBinary.readOffset buffers 0 with
    | error cause => simp [checked, initial, Except.mapError, Bind.bind, Except.bind] at read
    | ok first =>
      cases slots : (List.range node.length).mapM (readSlot buffers) with
      | error cause => simp [checked, initial, slots, Except.mapError, Bind.bind, Except.bind] at read
      | ok result =>
        simp only [checked, initial, slots, Except.mapError, Bind.bind, Except.bind] at read
        split at read
        · cases read
        · rename_i count
          cases read
          exact ⟨rfl, ⟨first, Binary.Offsets.readOffset_sound initial⟩,
            readSlots_sound slots, not_not.mp count⟩

theorem slot_octets {buffers : Buffers} {index : Nat} {value : Option String}
    (wf : buffers.data.wf = true) (wire : SlotWire buffers index value) :
    ∃ lo hi valid, LargeBinary.OffsetWire buffers index lo ∧ LargeBinary.OffsetWire buffers (index + 1) hi ∧
      lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
      if valid then (buffers.data.slice lo (hi - lo)).toByteArray.IsValidUTF8 ∧
        value.map (fun text => text.toByteArray.data.toList) =
          some ((buffers.data.toList.drop lo).take (hi - lo))
      else value = none := by
  obtain ⟨lo, hi, valid, first, next, order, bitmap, valueBytes⟩ := wire
  refine ⟨lo, hi, valid, first, next, order, bitmap, ?_⟩
  cases valid
  · exact valueBytes
  · obtain ⟨valid, bytes⟩ := valueBytes
    have within : lo + (hi - lo) ≤ buffers.data.len := by
      rw [Nat.add_sub_of_le order]
      exact next.2.2
    refine ⟨valid, ?_⟩
    have octets := congrArg (Option.map fun data : ByteArray => data.data.toList) bytes
    simpa [Option.map_map, Function.comp_def, KBytes.toByteArray,
      KBytes.toList_slice _ _ _ wf within] using octets

end Silmaril.Proofs.Formats.Arrow.LargeUtf8
