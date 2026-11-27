module

public import Silmaril.Formats.Arrow.Binary.Defs
public import Silmaril.Prelude.Bytes.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.Binary

open Silmaril Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Binary

theorem readOffset_sound {buffers : Buffers} {index offset : Nat}
    (read : readOffset buffers index = .ok offset) : OffsetWire buffers index offset := by
  unfold readOffset at read
  split at read
  · rename_i word raw
    split at read
    · cases read
    split at read
    · cases read
    · rename_i negative outside
      cases read
      exact ⟨raw, Nat.lt_of_not_ge negative, Nat.le_of_not_gt outside⟩
  · cases read

theorem readSlot_sound {buffers : Buffers} {index : Nat} {value : Option KBytes}
    (read : readSlot buffers index = .ok value) : SlotWire buffers index value := by
  unfold readSlot at read
  cases loEq : readOffset buffers index with
  | error cause => simp [loEq, Bind.bind, Except.bind] at read
  | ok lo =>
    cases hiEq : readOffset buffers (index + 1) with
    | error cause => simp [loEq, hiEq, Bind.bind, Except.bind] at read
    | ok hi =>
      simp only [loEq, hiEq, Bind.bind, Except.bind] at read
      split at read
      · cases read
      · rename_i ordered
        split at read
        · cases read
        · rename_i valid bit
          cases read
          exact ⟨lo, hi, valid, readOffset_sound loEq, readOffset_sound hiEq,
            Nat.le_of_not_gt ordered, bit, rfl⟩

private theorem readSlots_sound {buffers : Buffers} {slots : List Nat} {values : Binary.Column}
    (read : slots.mapM (readSlot buffers) = .ok values) :
    List.Forall₂ (SlotWire buffers) slots values := by
  induction slots generalizing values with
  | nil =>
    cases read
    exact .nil
  | cons slot rest ih =>
    rw [List.mapM_cons] at read
    cases first : readSlot buffers slot <;> cases next : rest.mapM (readSlot buffers) <;>
      simp [first, next, Bind.bind, Except.bind, pure, Except.pure] at read
    subst values
    exact .cons (readSlot_sound first) (ih next)

theorem readColumn_sound {limits : Limits} {nullable : Bool} {node : FieldNode}
    {buffers : Buffers} {values : Binary.Column}
    (read : readColumn limits nullable node buffers = .ok values) :
    checkColumn limits nullable node buffers = .ok () ∧ ColumnWire node buffers values := by
  unfold readColumn at read
  cases checked : checkColumn limits nullable node buffers with
  | error cause => simp [checked, Bind.bind, Except.bind] at read
  | ok checkedUnit =>
    cases checkedUnit
    cases initial : readOffset buffers 0 with
    | error cause => simp [checked, initial, Bind.bind, Except.bind] at read
    | ok first =>
      cases slots : (List.range node.length).mapM (readSlot buffers) with
      | error cause => simp [checked, initial, slots, Bind.bind, Except.bind] at read
      | ok result =>
        simp only [checked, initial, slots, Bind.bind, Except.bind] at read
        split at read
        · cases read
        · rename_i count
          cases read
          exact ⟨rfl, ⟨first, readOffset_sound initial⟩, readSlots_sound slots,
            not_not.mp count⟩

theorem bindBody_sound {limits : Limits} {batch : RecordBatch} {body : KBytes}
    {node : FieldNode} {buffers : Buffers}
    (bound : bindBody limits batch body = .ok (node, buffers)) : BodyWire batch body node buffers := by
  unfold bindBody at bound
  split at bound
  · cases bound
  split at bound
  · cases bound
  split at bound
  · rename_i actual validity offsets data nodes descriptors
    split at bound
    · rename_i fit
      cases bound
      exact ⟨nodes, fit.1, validity, offsets, data, descriptors, fit.2, rfl⟩
    · cases bound
  · cases bound

theorem readBatch_sound {limits : Limits} {schemaMetadata recordMetadata body : KBytes}
    {observed : Observed} (read : readBatch limits schemaMetadata recordMetadata body = .ok observed) :
    BatchWire limits schemaMetadata recordMetadata body observed := by
  unfold readBatch at read
  cases schema : readSchema limits schemaMetadata with
  | error cause => simp [schema, Except.mapError, Bind.bind, Except.bind] at read
  | ok field =>
    cases metadata : Silmaril.Formats.Arrow.readMessage limits recordMetadata with
    | error cause => simp [schema, metadata, Except.mapError, Bind.bind, Except.bind] at read
    | ok message =>
      obtain ⟨header, bodyLength⟩ := message
      cases header with
      | schema fields => simp [schema, metadata, Except.mapError, Bind.bind, Except.bind] at read
      | recordBatch batch =>
        simp only [schema, metadata, Except.mapError, Bind.bind, Except.bind] at read
        split at read
        · cases read
        · rename_i length
          split at read
          · cases read
          · rename_i alignment
            cases bound : bindBody limits batch body with
            | error cause => simp [bound] at read
            | ok physical =>
              obtain ⟨node, buffers⟩ := physical
              cases column : readColumn limits field.nullable node buffers with
              | error cause => simp [bound, column] at read
              | ok values =>
                simp only [bound, column] at read
                cases read
                refine ⟨schema, not_not.mp alignment, batch, node, buffers, ?_,
                  bindBody_sound bound, readColumn_sound column⟩
                simpa [not_not.mp length] using metadata

theorem slot_octets {buffers : Buffers} {index : Nat} {value : Option KBytes}
    (dataWf : buffers.data.wf = true) (wire : SlotWire buffers index value) :
    ∃ lo hi valid, OffsetWire buffers index lo ∧ OffsetWire buffers (index + 1) hi ∧
      lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
      value.map KBytes.toList =
        if valid then some ((buffers.data.toList.drop lo).take (hi - lo)) else none := by
  obtain ⟨lo, hi, valid, first, next, order, bitmap, rfl⟩ := wire
  refine ⟨lo, hi, valid, first, next, order, bitmap, ?_⟩
  cases valid
  · rfl
  · have within : lo + (hi - lo) ≤ buffers.data.len := by
      rw [Nat.add_sub_of_le order]
      exact next.2.2
    simp [KBytes.toList_slice _ _ _ dataWf within]

end Silmaril.Proofs.Formats.Arrow.Binary
