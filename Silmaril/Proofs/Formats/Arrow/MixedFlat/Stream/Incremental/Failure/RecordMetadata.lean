module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.RecordMetadata
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)
open MixedFlat.Stream (BatchRange)
open Arrow.Framing.Incremental (Frame Window metadataBytes)

private theorem decode_metadata_error {limits : MixedFlat.Stream.Incremental.Limits}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame} {cause : MixedFlat.MetadataError}
    (failed : decode limits fields running frame = .error (.record (.metadata cause))) :
    running.ordinal < limits.mixed.observation.ipc.batches ∧
    MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers limits.mixed.totalDataBuffers
      fields (metadataBytes frame.metadata) = .error cause := by
  unfold decode at failed
  dsimp only at failed
  split at failed
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at failed
  rename_i batches
  refine ⟨by omega, ?_⟩
  cases metadataCheck : MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
      limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) with
  | error rejected =>
    simp [metadataCheck, bind, Except.bind, Except.mapError] at failed
    exact congrArg Except.error failed
  | ok metadata =>
    simp only [metadataCheck, bind, Except.bind, Except.mapError] at failed
    split at failed
    · simp [throw, throwThe, MonadExceptOf.throw] at failed
    · cases budget : Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) with
      | error => simp [budget] at failed
      | ok accepted =>
        cases accepted
        simp only [budget] at failed
        split at failed <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at failed

theorem decode_metadata_error_iff {limits : MixedFlat.Stream.Incremental.Limits}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame} {cause : MixedFlat.MetadataError} :
    decode limits fields running frame = .error (.record (.metadata cause)) ↔
      running.ordinal < limits.mixed.observation.ipc.batches ∧
      MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers limits.mixed.totalDataBuffers
        fields (metadataBytes frame.metadata) = .error cause := by
  refine ⟨decode_metadata_error, ?_⟩
  rintro ⟨available, rejected⟩
  simp [decode, Nat.not_le.mpr available, rejected, bind, Except.bind, Except.mapError]

theorem feed_metadata_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset : Nat}
    {cause : MixedFlat.MetadataError}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (feedError ordinal offset cause)) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        Wire cursor.limits.mixed (.leaf size packed) fields running range cause := by
  obtain ⟨_, clash, _⟩ | ⟨frame, _, _, typed, tag, raw, decoded⟩ := feed_late_failure phase failed
  · contradiction
  · obtain ⟨ordinalExact, offsetExact, typedExact⟩ := MixedFlat.Stream.Incremental.Error.batch.inj tag
    rw [← typedExact] at decoded
    obtain ⟨frameOffset, wire, bodyWf⟩ := completed_frame_at held incoming raw
    obtain ⟨available, rejected⟩ := decode_metadata_error_iff.mp decoded
    obtain ⟨metadataMatch, bodyRead⟩ := packed_frame wire bodyWf
    rw [metadataMatch] at rejected
    exact ⟨ordinalExact, offsetExact, frameRange frame, frameOffset.trans offsetExact.symm, wire.1,
      wire.2.2.1, ⟨_, bodyRead⟩, available, rejected⟩

private theorem metadata_terminal {limits : MixedFlat.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange}
    {cause : MixedFlat.MetadataError}
    (wire : Wire limits input fields running range cause) :
    let remaining := limits.observation.ipc.batches - running.ordinal
    MixedFlat.Stream.Events.readNext limits input fields remaining running.ordinal running.rows range.offset =
      .error (.message running.ordinal range.offset (.metadata cause)) ∧
    MixedFlat.Stream.readBatches limits input fields remaining running.ordinal running.rows range.offset =
      .error (.batch running.ordinal (.metadata cause)) := by
  have nonempty : limits.observation.ipc.batches - running.ordinal ≠ 0 := by
    have available := wire.available
    omega
  have read : MixedFlat.Stream.readRecord limits input fields running.rows range.offset range.metadataSize =
      .error (.metadata cause) := by
    have rejected := wire.rejected
    simp only [BatchRange.metadataSlice] at rejected
    simp [MixedFlat.Stream.readRecord, rejected, bind, Except.bind, Except.mapError]
  refine ⟨?_, ?_⟩
  · simp only [MixedFlat.Stream.Events.readNext, wire.envelope, Except.mapError, bind, Except.bind, nonempty, ite_false]
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
    simp [wire.envelope, read, bind, Except.bind, Except.mapError]

theorem metadata_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
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
  obtain ⟨ordinal, offset, range, rangeOffset, admitted⟩ := feed_metadata_wire finalHeld incoming finalPhase failed
  rw [finalLimits, openedLimits] at admitted
  obtain ⟨native, terminal⟩ := metadata_terminal admitted
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

theorem metadata_pull_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ := by
  obtain ⟨_, _, _, schemaRead, replay, _, _, _, failed, _⟩ := metadata_exact run
  simpa only [List.map_map, Function.comp_def, Delivered.published, Run.nativeCause] using
    replay_read_all_error rfl schemaRead replay failed

theorem schedules_metadata_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := metadata_exact a
  have checkedB := metadata_exact b
  rcases a with ⟨fieldsA, batchesA, ordinalA, offsetA, causeA, runA⟩
  rcases b with ⟨fieldsB, batchesB, ordinalB, offsetB, causeB, runB⟩
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
  have exact : ordinalA = ordinalB ∧ offsetA = offsetB ∧ causeA = causeB := by
    simpa using coordinates
  obtain ⟨ordinalEq, offsetEq, causeEq⟩ := exact
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [Run.ranges, Run.trace, Run.cause, feedError, rangesEq, eventsEq,
    ordinalEq, offsetEq, causeEq]

theorem metadata_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, immutableError⟩ := metadata_exact failed
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata
