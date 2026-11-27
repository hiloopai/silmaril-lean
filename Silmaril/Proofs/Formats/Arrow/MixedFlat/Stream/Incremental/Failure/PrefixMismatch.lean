module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.PrefixMismatch
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)
open MixedFlat.Stream (BatchRange)
open Arrow.Framing.Incremental (Window metadataBytes)

theorem feed_field_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset index : Nat}
    {cause : MixedFlat.ColumnError}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (.batch ordinal offset (.record (.decode (.field index cause))))) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        FieldFailureWire cursor.limits (.leaf size packed) fields running range index cause := by
  obtain ⟨_, clash, _⟩ | ⟨frame, _, _, typed, tag, raw, decoded⟩ := feed_late_failure phase failed
  · contradiction
  · obtain ⟨ordinalExact, offsetExact, typedExact⟩ := MixedFlat.Stream.Incremental.Error.batch.inj tag
    rw [← typedExact] at decoded
    obtain ⟨frameOffset, wire, bodyWf⟩ := completed_frame_at held incoming raw
    obtain ⟨metadata, metadataRead, available, dataBudget, rowsBudget, extent, parsed⟩ :=
      decode_field_checked decoded
    obtain ⟨metadataMatch, bodyRead⟩ := packed_frame wire bodyWf
    rw [metadataMatch] at metadataRead
    refine ⟨ordinalExact, offsetExact, frameRange frame, frameOffset.trans offsetExact.symm,
      wire.1, available, metadata, metadataBytes frame.body, metadataRead, extent, bodyRead,
      dataBudget, rowsBudget, parsed⟩

theorem record_field_error {limits : MixedFlat.Stream.Incremental.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange} {index : Nat}
    {cause : MixedFlat.ColumnError}
    (wire : FieldFailureWire limits input fields running range index cause) :
    MixedFlat.Stream.readRecord limits.mixed input fields running.rows range.offset range.metadataSize =
      .error (.decode (.field index cause)) := by
  obtain ⟨_, _, metadata, body, metadataRead, extent, bodyRead, _, budget, parsed⟩ := wire
  simp only [BatchRange.metadataSlice] at metadataRead
  simp only [BatchRange.bodyStart] at bodyRead
  simp [MixedFlat.Stream.readRecord, metadataRead, extent, BatchRange.bodyStart, bodyRead,
    budget, parsed, bind, Except.bind, Except.mapError]

theorem field_terminal {limits : MixedFlat.Stream.Incremental.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange} {index : Nat}
    {cause : MixedFlat.ColumnError}
    (wire : FieldFailureWire limits input fields running range index cause) :
    let remaining := limits.mixed.observation.ipc.batches - running.ordinal
    MixedFlat.Stream.Events.readNext limits.mixed input fields remaining running.ordinal running.rows range.offset =
      .error (.message running.ordinal range.offset (.decode (.field index cause))) ∧
    MixedFlat.Stream.readBatches limits.mixed input fields remaining running.ordinal running.rows range.offset =
      .error (.batch running.ordinal (.decode (.field index cause))) := by
  have nonempty : limits.mixed.observation.ipc.batches - running.ordinal ≠ 0 := by
    have available := wire.2.1
    omega
  have read := record_field_error wire
  refine ⟨?_, ?_⟩
  · simp only [MixedFlat.Stream.Events.readNext, wire.1, Except.mapError, bind, Except.bind, nonempty, ite_false]
    split
    · rename_i fault rejected
      rw [read] at rejected
      have same := Except.error.inj rejected
      subst fault
      rfl
    · rename_i _ accepted
      rw [read] at accepted
      contradiction
  · obtain ⟨fuel, remaining⟩ := Nat.exists_eq_succ_of_ne_zero nonempty
    rw [remaining, MixedFlat.Stream.readBatches]
    simp [wire.1, read, bind, Except.bind, Except.mapError]

theorem prefix_mismatch_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run := by
  obtain ⟨opened, final, chunk, opening, records, incoming, failed⟩ := run.ran
  obtain ⟨openedHeld, openedLimits, phase, readSchema⟩ := open_agrees opening
  change MixedFlat.Stream.readSchemaFrame limits.mixed.observation.ipc (reference wire) =
    .ok (run.fields, opened.messageOffset) at readSchema
  rw [← openedLimits] at openedHeld
  obtain ⟨running, finalHeld, finalLimits, finalPhase, _, eagerSuffix⟩ :=
    steps_agree records openedHeld phase
  obtain ⟨replayed, replayPhase, replay⟩ := steps_replay records openedHeld phase
  have runningExact := (Phase.records.inj (finalPhase.symm.trans replayPhase)).2
  subst replayed
  rw [← finalLimits] at finalHeld
  obtain ⟨ordinal, offset, range, rangeOffset, admitted⟩ := feed_field_wire finalHeld incoming finalPhase failed
  rw [finalLimits, openedLimits] at admitted
  obtain ⟨native, terminal⟩ := field_terminal admitted
  rw [rangeOffset, ← ordinal] at native terminal
  refine ⟨opened.messageOffset, running, range, readSchema, ?_, ordinal.symm, rangeOffset, admitted,
    ?_, ?_⟩
  · simpa only [openedLimits, ← offset, reference] using replay
  · simpa only [Position.readNext, Position.ofRunning, ordinal, reference] using native
  · simp only [openedLimits, ← offset, ← ordinal] at eagerSuffix
    change MixedFlat.Stream.readBatches limits.mixed (reference wire) run.fields
      limits.mixed.observation.ipc.batches 0 0 opened.messageOffset = _ at eagerSuffix
    rw [terminal] at eagerSuffix
    have valid : (reference wire).wf = true := rfl
    simp [MixedFlat.Stream.read, valid, readSchema, eagerSuffix, bind, Except.bind, Except.map]

theorem schedules_mismatch_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := prefix_mismatch_exact a
  have checkedB := prefix_mismatch_exact b
  rcases a with ⟨fieldsA, batchesA, ordinalA, offsetA, fieldA, slotA, runA⟩
  rcases b with ⟨fieldsB, batchesB, ordinalB, offsetB, fieldB, slotB, runB⟩
  obtain ⟨startA, runningA, rangeA, schemaA, replayA, _, _, _, failedA, _⟩ := checkedA
  obtain ⟨startB, runningB, rangeB, schemaB, replayB, _, _, _, failedB, _⟩ := checkedB
  rw [sameRef] at schemaA replayA failedA
  obtain ⟨fieldsEq, startEq⟩ := Prod.mk.inj (Except.ok.inj (schemaA.symm.trans schemaB))
  dsimp only at fieldsEq startEq
  subst fieldsB
  subst startB
  obtain ⟨publishedEq, _, coordinates⟩ := replay_unique_at_error replayA replayB failedA failedB
  have rangesEq := congrArg (List.map fun (item : Published fieldsA) => item.1.range) publishedEq
  have eventsEq := congrArg (List.map fun (item : Published fieldsA) => item.2) publishedEq
  have exact : ordinalA = ordinalB ∧ offsetA = offsetB ∧ fieldA = fieldB ∧ slotA = slotB := by
    simpa [columnCause] using coordinates
  obtain ⟨ordinalEq, offsetEq, fieldEq, slotEq⟩ := exact
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [Run.ranges, Run.trace, Run.cause, mismatchError, rangesEq, eventsEq,
    ordinalEq, offsetEq, fieldEq, slotEq]

theorem mismatch_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, immutableError⟩ := prefix_mismatch_exact failed
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch
