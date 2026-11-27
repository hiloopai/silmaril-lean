module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Thms
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch

open Silmaril.Formats.Arrow (Buffer EnvelopeWire readEnvelope_iff readBody_iff metadata_exact body_exact)
open Silmaril.Formats.Arrow.Body (sliceBuffer offsetAt offsetAt_iff)
open Silmaril.Formats.Arrow.RecursiveSchema (Schema SchemaWire)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch

private theorem fields_slots {carrier : Carrier} {depth length fields start layouts next}
    (wire : FieldsWire carrier depth length fields start layouts next) :
    start.slots ≤ carrier.slotLimit → next.slots ≤ carrier.slotLimit := by
  apply FieldsWire.rec
    (motive_1 := fun _ _ _ start _ next _ =>
      start.slots ≤ carrier.slotLimit → next.slots ≤ carrier.slotLimit)
    (motive_2 := fun _ _ _ start _ next _ =>
      start.slots ≤ carrier.slotLimit → next.slots ≤ carrier.slotLimit) _ _ _ wire
  · intro depth length name nullable kind children start node validity payload childLength
      childStart childLayouts next arity nodeWire validityWire extent payloadWire childWire ih _
    apply ih
    cases payloadWire <;> exact nodeWire.slots_bound
  · exact fun h => h
  · intro depth length field fields start layout layouts middle next headWire tailWire head tail bound
    exact tail (head bound)

theorem frame_wire {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : FrameWire frame := by
  obtain ⟨len, bodyBytes⟩ := body_exact frame.source_wf frame.body_read
  have bound := (readBody_iff _ _ _ _ _).mp frame.body_read |>.2.2.2.1
  exact ⟨(readEnvelope_iff _ _ _ _ frame.source_wf).mp frame.envelope,
    metadata_exact frame.source_wf frame.envelope, frame.metadata, bodyBytes, ⟨len, bound⟩,
    frame.layout.fields.wire, frame.layout.exact_nodes, frame.layout.exact_buffers,
    fields_slots frame.layout.fields.wire (Nat.zero_le _)⟩

theorem first_wire {limits : Limits} {input : KBytes} (first : First limits input) :
    ∃ size, first.offset = 8 + size ∧
      EnvelopeWire limits.schema.ipc input.toList 0 (.metadata size) ∧
      (input.slice 8 size).toList = (input.toList.drop 8).take size ∧
      SchemaWire limits.schema (input.slice 8 size) first.schema ∧ FrameWire first.batch := by
  obtain ⟨size, cursor, envelope, bytes, schema⟩ :=
    Silmaril.Formats.Arrow.RecursiveSchema.readFrame_wire first.schema_read
  exact ⟨size, cursor, envelope, bytes, schema, frame_wire first.batch⟩

theorem region_exact {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) {cursor : Cursor} {buffer : Buffer}
    (wire : BufferWire frame.carrier cursor buffer) :
    frame.bodyStart + buffer.offset + buffer.length ≤ frame.next ∧
      (sliceBuffer frame.body buffer).len = buffer.length ∧
      (sliceBuffer frame.body buffer).toList =
        (input.toList.drop (frame.bodyStart + buffer.offset)).take buffer.length := by
  have fit : buffer.offset + buffer.length ≤ frame.body.len := wire.region.2.2
  obtain ⟨len, original⟩ := body_exact frame.source_wf frame.body_read
  have range := (readBody_iff _ _ _ _ _).mp frame.body_read
  have wf : frame.body.wf = true := by
    rw [range.2.2.2.2]
    exact KBytes.wf_slice _ _ _ frame.source_wf range.2.2.2.1
  refine ⟨by unfold Frame.next; omega, KBytes.len_slice _ _ _, ?_⟩
  rw [sliceBuffer, KBytes.toList_slice _ _ _ wf fit, original, List.drop_take,
    List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]
  rfl

private theorem offset_last {offsets : KBytes} {length final : Nat}
    (wire : OffsetPrefix offsets length final) : offsetAt offsets length = some final := by
  cases wire with
  | zero word => exact word
  | step _ word _ => exact word

theorem offset_last_word {offsets : KBytes} {length final : Nat}
    (wire : OffsetPrefix offsets length final) :
    offsets.readLE (4 * length) 4 = some final ∧ final < 2^31 :=
  (offsetAt_iff _ _ _).mp (offset_last wire)

theorem offset_window {offsets : KBytes} {length final : Nat}
    (wire : OffsetPrefix offsets length final) {index : Nat} (range : index < length) :
    ∃ lo hi, offsets.readLE (4 * index) 4 = some lo ∧
      offsets.readLE (4 * (index + 1)) 4 = some hi ∧ lo ≤ hi ∧ hi ≤ final ∧ final < 2^31 := by
  induction wire generalizing index with
  | zero => omega
  | @step previousIndex previous current earlier word order ih =>
    have currentWire := (offsetAt_iff _ _ _).mp word
    by_cases last : index = previousIndex
    · subst index
      exact ⟨previous, current, (offset_last_word earlier).1, currentWire.1, order,
        Nat.le_refl _, currentWire.2⟩
    · obtain ⟨lo, hi, loWire, hiWire, ordered, bounded, _⟩ := ih (index := index) (by omega)
      exact ⟨lo, hi, loWire, hiWire, ordered, Nat.le_trans bounded order, currentWire.2⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch
