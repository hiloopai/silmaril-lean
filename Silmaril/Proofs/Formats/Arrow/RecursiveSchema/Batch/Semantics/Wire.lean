module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Batteries.Data.List.Lemmas

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics

open Silmaril.Formats.Arrow (Buffer FieldNode)
open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch hiding Error PayloadWire readFirst
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics
open Silmaril.Formats.Parquet
open Silmaril.Formats.Arrow.Body (sliceBuffer validAt offsetAt)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem readPresence_wire {body : KBytes} {index : Nat} {node : FieldNode}
    {buffer : Buffer} {nullable : Bool} {visible : Array Bool} {presence : Presence}
    (read : readPresence body index node buffer nullable visible = .ok presence) :
    PresenceWire body node buffer nullable visible presence := by
  unfold readPresence at read
  split at read
  · contradiction
  · rename_i size
    obtain ⟨bits, decoded, read⟩ := bind_ok read
    dsimp only at read
    split at read
    · contradiction
    · rename_i count
      split at read
      · contradiction
      · rename_i check
        cases Except.ok.inj read
        have same : List.Forall₂ (fun slot bit =>
            validAt (sliceBuffer body buffer) slot = some bit) (List.range node.length) bits :=
          (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun slot bit readBit => by
            cases word : validAt (sliceBuffer body buffer) slot <;> simp [word] at readBit ⊢
            exact readBit
        exact ⟨rfl, Decidable.of_not_not size, by simpa using same,
          Decidable.of_not_not count, check⟩

private theorem signedWords_wire {α : Type} {width length : Nat} {bytes : KBytes}
    {value : List UInt8 → α} {words : List α}
    (read : Plain.decodeFixedWidth width length value ⟨bytes.toByteArray⟩ = .ok words) :
    SignedWords width length value bytes words := by
  obtain ⟨_, witness, original, count, sized, decoded⟩ := Plain.decodeFixedWidth_ok_iff.mp read
  exact ⟨witness, original, count, sized, decoded⟩

private theorem readPayload_wire {body : KBytes} {index length : Nat}
    {kind : Formats.Arrow.RecursiveSchema.Wire.Kind} {buffer : Option Buffer} {payload : Payload}
    (read : readPayload body index length kind buffer = .ok payload) :
    PayloadWire body length kind buffer payload := by
  cases kind <;> cases buffer <;> simp only [readPayload] at read
  any_goals contradiction
  · rename_i buffer
    cases decoded : Plain.decodeInt32 length ⟨(sliceBuffer body buffer).toByteArray⟩ with
    | error cause => simp [decoded, Except.map, Except.mapError] at read
    | ok words =>
      simp [decoded, Except.map, Except.mapError] at read
      subst payload
      exact .int32 (signedWords_wire decoded)
  · rename_i buffer
    cases decoded : Plain.decodeInt64 length ⟨(sliceBuffer body buffer).toByteArray⟩ with
    | error cause => simp [decoded, Except.map, Except.mapError] at read
    | ok words =>
      simp [decoded, Except.map, Except.mapError] at read
      subst payload
      exact .int64 (signedWords_wire decoded)
  · cases Except.ok.inj read
    exact .struct
  · obtain ⟨offsets, decoded, read⟩ := bind_ok read
    cases Except.ok.inj read
    apply PayloadWire.list
    simpa using (List.mapM_eq_ok_iff_forall₂.mp decoded).imp (fun slot value readOffset => by
      cases word : offsetAt (sliceBuffer body ‹Buffer›) slot <;> simp [word] at readOffset ⊢
      exact readOffset)

private theorem decodeColumns_wire {body : KBytes} {visible : Array Bool}
    {readColumn : Nat → Field → FieldLayout → Except Error (Column × Nat)}
    (columnLaw : ∀ {index field layout column next},
      readColumn index field layout = .ok (column, next) →
      ColumnWire body visible field layout column)
    {index fields layouts columns next}
    (read : decodeColumns readColumn index fields layouts = .ok (columns, next)) :
    ColumnsWire body visible fields layouts columns := by
  induction fields generalizing index layouts columns next with
  | nil =>
    cases layouts <;> simp [decodeColumns] at read
    obtain ⟨rfl, _⟩ := read
    exact .nil
  | cons field fields ih =>
    cases layouts with
    | nil => simp [decodeColumns] at read
    | cons layout layouts =>
      simp only [decodeColumns] at read
      obtain ⟨⟨column, afterColumn⟩, first, read⟩ := bind_ok read
      obtain ⟨⟨tail, afterTail⟩, rest, read⟩ := bind_ok read
      cases Except.ok.inj read
      exact .cons (columnLaw first) (ih rest)

private theorem decodeColumn_wire {body : KBytes} {depth : Nat} {visible : Array Bool}
    {index field layout column next}
    (read : decodeColumn body depth visible index field layout = .ok (column, next)) :
    ColumnWire body visible field layout column := by
  induction depth generalizing visible index field layout column next with
  | zero => simp [decodeColumn] at read
  | succ depth ih =>
    obtain ⟨name, nullable, kind, fields⟩ := field
    obtain ⟨node, bitmap, buffer, layouts⟩ := layout
    simp only [decodeColumn] at read
    obtain ⟨presence, readPresence, read⟩ := bind_ok read
    obtain ⟨payload, readPayload, read⟩ := bind_ok read
    obtain ⟨⟨children, afterChildren⟩, readChildren, read⟩ := bind_ok read
    cases Except.ok.inj read
    exact .node (readPresence_wire readPresence) (readPayload_wire readPayload)
      (decodeColumns_wire (fun h => ih h) readChildren)

private theorem payload_buffer {carrier : Carrier} {cursor : Cursor} {node : FieldNode}
    {kind payload length next} (wire : Formats.Arrow.RecursiveSchema.Batch.PayloadWire carrier cursor node kind payload length next)
    {buffer : Buffer} (member : buffer ∈ payload.toList) :
    BufferWire carrier cursor buffer := by
  cases wire with
  | struct => simp at member
  | values _ selected _ =>
    simp at member
    subst buffer
    exact selected
  | offsets selected _ _ =>
    simp at member
    subst buffer
    exact selected

private theorem layout_buffers {carrier : Carrier} {depth length fields start layouts next}
    (wire : FieldsWire carrier depth length fields start layouts next) :
    ∀ buffer ∈ layouts.flatMap buffers, ∃ cursor, BufferWire carrier cursor buffer := by
  apply FieldsWire.rec
    (motive_1 := fun _ _ _ _ layout _ _ =>
      ∀ buffer ∈ buffers layout, ∃ cursor, BufferWire carrier cursor buffer)
    (motive_2 := fun _ _ _ _ layouts _ _ =>
      ∀ buffer ∈ layouts.flatMap buffers, ∃ cursor, BufferWire carrier cursor buffer) _ _ _ wire
  · intro depth length name nullable kind children start node validity payload childLength
      childStart childLayouts next arity nodeWire validityWire extent payloadWire childWire ih buffer member
    simp only [buffers, List.mem_cons, List.mem_append] at member
    rcases member with (rfl | inPayload) | inChild
    · exact ⟨_, validityWire⟩
    · exact ⟨_, payload_buffer payloadWire inPayload⟩
    · exact ih buffer inChild
  · simp
  · intro depth length field fields start layout layouts middle next headWire tailWire head tail buffer member
    simp only [List.flatMap_cons, List.mem_append] at member
    exact member.elim (head buffer) (tail buffer)

theorem decode_wire {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    {frame : Frame limits schema input offset} {observed : Observation}
    (read : decode frame = .ok observed) : ObservationWire frame observed := by
  unfold decode at read
  obtain ⟨⟨columns, _⟩, decoded, read⟩ := bind_ok read
  cases Except.ok.inj read
  refine ⟨frame.wire, rfl, decodeColumns_wire decodeColumn_wire decoded, ?_⟩
  intro buffer member
  obtain ⟨cursor, wire⟩ := layout_buffers frame.layout.fields.wire buffer member
  exact (frame.region_exact wire).2.2

theorem readFirst_wire {limits : Limits} {input : KBytes} {first : First limits input}
    {observed : Observation} (read : readFirst limits input = .ok (first, observed)) :
    ObservationWire first.batch observed := by
  simp only [readFirst, bind, Except.bind] at read
  cases checked : Formats.Arrow.RecursiveSchema.Batch.readFirst limits input with
  | error cause => simp [Except.mapError, checked] at read
  | ok layout =>
    simp only [Except.mapError, checked] at read
    cases decoded : decode layout.batch with
    | error cause => simp [decoded] at read
    | ok value =>
      simp [decoded, pure, Except.pure] at read
      obtain ⟨rfl, rfl⟩ := read
      exact decode_wire decoded

theorem required_at {body : KBytes} {node : FieldNode} {buffer : Buffer}
    {visible : Array Bool} {presence : Presence} {index : Nat}
    (wire : PresenceWire body node buffer false visible presence)
    (slot : index < node.length) (reached : presence.visible[index]? = some true) :
    presence.valid[index]? = some true := by
  have size : presence.valid.size = node.length := by
    simpa using wire.fromBitmap.length_eq.symm
  have validSlot : index < presence.valid.size := by omega
  have none := wire.required
  simp only [requiredNull, Bool.false_eq_true, ite_false] at none
  have checked := List.find?_eq_none.mp none index (List.mem_range.mpr validSlot)
  rw [reached] at checked
  rw [Array.getElem?_eq_getElem validSlot] at checked ⊢
  cases bit : presence.valid[index] <;> simp_all

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics
