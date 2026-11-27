module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Thms
import Silmaril.Formats.Arrow.MixedFlat.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Formats.Arrow.Layout.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat.LargeUtf8
open Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream

theorem readRecord_sound {limits : MixedFlat.Limits} {framing : Framing} {input : KBytes}
    {fields : List MixedFlat.LargeUtf8.Field} {rowsBefore offset size : Nat} {batch : Batch}
    (read : readRecord limits framing input fields rowsBefore offset size = .ok batch) :
    RecordWire limits framing input fields rowsBefore offset size batch := by
  unfold readRecord at read
  cases metadataRead : MixedFlat.LargeUtf8.readMetadata limits fields
      (input.slice (offset + framing.prefixSize) size) with
  | error => simp [metadataRead, Bind.bind, Except.bind, Except.mapError] at read
  | ok metadata =>
    let range : Range := ⟨offset, framing.prefixSize, size, metadata.bodyLength⟩
    cases bodyRead : Arrow.readBody limits.observation.ipc input range.bodyStart range.bodyLength with
    | error =>
      simp [metadataRead, bodyRead, range, Bind.bind, Except.bind, Except.mapError] at read
    | ok body =>
      cases budget : Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount) with
      | error => simp [metadataRead, bodyRead, range, budget, Bind.bind, Except.bind, Except.mapError] at read
      | ok admitted =>
        cases admitted
        cases decoded : MixedFlat.LargeUtf8.readParsed limits fields metadata body with
        | error =>
          simp [metadataRead, bodyRead, range, budget, decoded, Bind.bind, Except.bind, Except.mapError] at read
        | ok observed =>
          simp [metadataRead, bodyRead, range, budget, decoded, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] at read
          subst batch
          exact ⟨metadata, body, metadataRead, rfl, bodyRead, budget, readParsed_sound decoded⟩

private theorem readBatches_sound (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (fields : List MixedFlat.LargeUtf8.Field) (remaining ordinal rowsBefore offset : Nat) :
    let result := readBatches limits framing input fields remaining ordinal rowsBefore offset
    TraceWire limits framing input fields remaining ordinal rowsBefore offset result.batches result.termination := by
  induction remaining generalizing ordinal rowsBefore offset with
  | zero =>
    rw [readBatches]
    cases envelope : framing.readEnvelope limits.observation.ipc input offset with
    | error cause => exact .stop (.envelope envelope)
    | ok framed =>
      cases framed with
      | eos =>
        by_cases full : offset + framing.prefixSize = input.len
        · simpa [full] using TraceWire.stop (StopWire.eos (ordinal := ordinal) (remaining := 0)
            (rowsBefore := rowsBefore) (fields := fields) envelope full)
        · simpa [full] using TraceWire.stop (StopWire.trailing (ordinal := ordinal) (remaining := 0)
            (rowsBefore := rowsBefore) (fields := fields) envelope full)
      | metadata size => exact .stop (.batchLimit envelope)
  | succ fuel ih =>
    rw [readBatches]
    cases envelope : framing.readEnvelope limits.observation.ipc input offset with
    | error cause => exact .stop (.envelope envelope)
    | ok framed =>
      cases framed with
      | eos =>
        by_cases full : offset + framing.prefixSize = input.len
        · simpa [full] using TraceWire.stop (StopWire.eos (ordinal := ordinal) (remaining := fuel + 1)
            (rowsBefore := rowsBefore) (fields := fields) envelope full)
        · simpa [full] using TraceWire.stop (StopWire.trailing (ordinal := ordinal) (remaining := fuel + 1)
            (rowsBefore := rowsBefore) (fields := fields) envelope full)
      | metadata size =>
        cases record : readRecord limits framing input fields rowsBefore offset size with
        | error cause =>
          simpa only [record] using TraceWire.stop (StopWire.record (ordinal := ordinal)
            (fuel := fuel) envelope record)
        | ok batch =>
          simpa only [record] using TraceWire.more envelope (readRecord_sound record)
            (ih (ordinal + 1) (rowsBefore + batch.observed.rowCount) batch.range.next)

theorem read_sound {limits : MixedFlat.Limits} {framing : Framing} {input : KBytes}
    {observed : MixedFlat.LargeUtf8.Stream.Observed} (read : read limits framing input = .ok observed) :
    StreamWire limits framing input observed := by
  by_cases wf : input.wf = true
  · cases schema : readSchemaFrame limits.observation.ipc framing input with
    | error => simp [MixedFlat.LargeUtf8.Stream.read, wf, schema, Bind.bind, Except.bind] at read
    | ok header =>
      obtain ⟨fields, offset⟩ := header
      simp [MixedFlat.LargeUtf8.Stream.read, wf, schema, Bind.bind, Except.bind, Pure.pure, Except.pure] at read
      subst observed
      cases envelope : framing.readEnvelope limits.observation.ipc input 0 with
      | error => simp [readSchemaFrame, envelope, Bind.bind, Except.bind, Except.mapError] at schema
      | ok framed =>
        cases framed with
        | eos => simp [readSchemaFrame, envelope, Bind.bind, Except.bind, Except.mapError] at schema
        | metadata size =>
          cases decoded : MixedFlat.LargeUtf8.readSchema limits.observation.ipc
              (input.slice framing.prefixSize size) with
          | error =>
            simp [readSchemaFrame, envelope, decoded, Bind.bind, Except.bind, Except.mapError] at schema
          | ok parsed =>
            simp [readSchemaFrame, envelope, decoded, Bind.bind, Except.bind, Except.mapError,
              Pure.pure, Except.pure] at schema
            obtain ⟨rfl, rfl⟩ := schema
            exact ⟨wf, size, envelope, decoded, readBatches_sound _ _ _ _ _ _ _ _⟩
  · simp [MixedFlat.LargeUtf8.Stream.read, wf] at read

theorem error_ordinal {limits : MixedFlat.Limits} {framing : Framing} {input : KBytes}
    {fields : List MixedFlat.LargeUtf8.Field} {remaining ordinal rowsBefore offset failed failedOffset : Nat}
    {batches : List Batch} {cause : Cause}
    (wire : TraceWire limits framing input fields remaining ordinal rowsBefore offset batches
      (.error failed failedOffset cause)) :
    failed = ordinal + batches.length := by
  generalize terminalEq : Termination.error failed failedOffset cause = terminal at wire
  induction wire with
  | stop stop => cases stop <;> simp_all
  | more _ _ _ ih =>
    have same := ih terminalEq
    simp only [List.length_cons]
    omega

theorem original_buffer {limits : Arrow.Limits} {input body : KBytes} {range : Range}
    {fields : List MixedFlat.Field} {metadata : MixedFlat.Metadata} (inputWf : input.wf = true)
    (read : Arrow.readBody limits input range.bodyStart range.bodyLength = .ok body)
    (plan : MixedFlat.Plan fields metadata body) {group : MixedFlat.Group metadata.batch.rowCount}
    (assigned : group ∈ plan.assignment.groups) {buffer : Buffer} (member : buffer ∈ group.buffers) :
    range.bodyStart + buffer.offset + buffer.length ≤ range.next ∧ range.next ≤ input.len ∧
    (Body.sliceBuffer body buffer).len = buffer.length ∧
    (Body.sliceBuffer body buffer).toList =
      (input.toList.drop (range.bodyStart + buffer.offset)).take buffer.length := by
  have wireMember : buffer ∈ metadata.batch.buffers := by
    rw [← plan.assignment.buffersExact]
    exact List.mem_flatMap.mpr ⟨group, assigned, member⟩
  have fit := (plan.ordered.mem_fits wireMember).2.2
  obtain ⟨len, original⟩ := Arrow.body_exact inputWf read
  obtain ⟨sliceLen, slice⟩ := plan.buffer_exact assigned member
  have within := (Arrow.readBody_iff _ _ _ _ _).mp read |>.2.2.2.1
  change range.bodyStart + range.bodyLength ≤ input.len at within
  refine ⟨by unfold Binary.Stream.Range.next; omega, within, sliceLen, ?_⟩
  rw [slice, original, List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

end Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream
