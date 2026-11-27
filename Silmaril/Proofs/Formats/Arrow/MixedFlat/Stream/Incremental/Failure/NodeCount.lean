module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.NodeCount
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)
open MixedFlat.Stream (BatchRange)
open Arrow.Framing.Incremental (Frame Window metadataBytes)

private theorem decode_node_count {limits : MixedFlat.Stream.Incremental.Limits}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame} {expected actual : Nat}
    (failed : decode limits fields running frame = .error (.record (batchError expected actual))) :
    running.ordinal < limits.mixed.observation.ipc.batches ∧
    MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers limits.mixed.totalDataBuffers
      fields (metadataBytes frame.metadata) = .error (.nodeCount expected actual) := by
  unfold decode at failed
  dsimp only at failed
  split at failed
  · simp [batchError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at failed
  rename_i batches
  refine ⟨by omega, ?_⟩
  cases metadataCheck : MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
      limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) with
  | error cause =>
    simp [metadataCheck, batchError, bind, Except.bind, Except.mapError] at failed
    exact congrArg Except.error failed
  | ok metadata =>
    simp only [metadataCheck, bind, Except.bind, Except.mapError] at failed
    split at failed
    · simp [batchError, throw, throwThe, MonadExceptOf.throw] at failed
    · cases budget : Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) with
      | error => simp [budget, batchError] at failed
      | ok accepted =>
        cases accepted
        simp only [budget] at failed
        split at failed <;> simp [batchError, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at failed

theorem feed_node_count_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset expected actual : Nat}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (feedError ordinal offset expected actual)) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        Wire cursor.limits.mixed (.leaf size packed) fields running range expected actual := by
  obtain ⟨_, clash, _⟩ | ⟨frame, _, _, typed, tag, raw, decoded⟩ := feed_late_failure phase failed
  · contradiction
  · obtain ⟨ordinalExact, offsetExact, typedExact⟩ := MixedFlat.Stream.Incremental.Error.batch.inj tag
    rw [← typedExact] at decoded
    obtain ⟨frameOffset, wire, bodyWf⟩ := completed_frame_at held incoming raw
    obtain ⟨available, rejected⟩ := decode_node_count decoded
    obtain ⟨metadataMatch, bodyRead⟩ := packed_frame wire bodyWf
    rw [metadataMatch] at rejected
    exact ⟨ordinalExact, offsetExact, frameRange frame, frameOffset.trans offsetExact.symm, wire.1,
      wire.2.2.1, ⟨_, bodyRead⟩, available, rejected⟩

private theorem node_count_terminal {limits : MixedFlat.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange} {expected actual : Nat}
    (wire : Wire limits input fields running range expected actual) :
    let remaining := limits.observation.ipc.batches - running.ordinal
    MixedFlat.Stream.Events.readNext limits input fields remaining running.ordinal running.rows range.offset =
      .error (.message running.ordinal range.offset (batchError expected actual)) ∧
    MixedFlat.Stream.readBatches limits input fields remaining running.ordinal running.rows range.offset =
      .error (.batch running.ordinal (batchError expected actual)) := by
  have nonempty : limits.observation.ipc.batches - running.ordinal ≠ 0 := by
    have available := wire.available
    omega
  have read : MixedFlat.Stream.readRecord limits input fields running.rows range.offset range.metadataSize =
      .error (batchError expected actual) := by
    have rejected := wire.rejected
    simp only [BatchRange.metadataSlice] at rejected
    simp [MixedFlat.Stream.readRecord, batchError, rejected, bind, Except.bind, Except.mapError]
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

theorem node_count_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
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
  obtain ⟨ordinal, offset, range, rangeOffset, admitted⟩ := feed_node_count_wire finalHeld incoming finalPhase failed
  rw [finalLimits, openedLimits] at admitted
  obtain ⟨native, terminal⟩ := node_count_terminal admitted
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

theorem node_count_pull_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ := by
  obtain ⟨_, _, _, schemaRead, replay, _, _, _, failed, _⟩ := node_count_exact run
  simpa only [List.map_map, Function.comp_def, Delivered.published, Run.nativeCause] using
    replay_read_all_error rfl schemaRead replay failed

theorem schedules_node_count_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := node_count_exact a
  have checkedB := node_count_exact b
  rcases a with ⟨fieldsA, batchesA, ordinalA, offsetA, expectedA, actualA, runA⟩
  rcases b with ⟨fieldsB, batchesB, ordinalB, offsetB, expectedB, actualB, runB⟩
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
  have exact : ordinalA = ordinalB ∧ offsetA = offsetB ∧ expectedA = expectedB ∧ actualA = actualB := by
    simpa [batchError] using coordinates
  obtain ⟨ordinalEq, offsetEq, expectedEq, actualEq⟩ := exact
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [Run.ranges, Run.trace, Run.cause, feedError, batchError, rangesEq, eventsEq,
    ordinalEq, offsetEq, expectedEq, actualEq]

theorem node_count_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, immutableError⟩ := node_count_exact failed
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount
