module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.BodyLayout
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)
open MixedFlat.Stream (BatchRange)
open Arrow.Framing.Incremental (Frame Window metadataBytes)

private theorem groups_error_field {limits : BinaryView.Column.Limits} {body : KBytes}
    {rows index : Nat} {groups : List (MixedFlat.Group rows)} {cause : MixedFlat.Error}
    (failed : MixedFlat.readGroups limits body index groups = .error cause) :
    ∃ field error, cause = .field field error := by
  induction groups generalizing index cause with
  | nil => simp [MixedFlat.readGroups] at failed
  | cons group rest ih =>
    cases column : MixedFlat.readGroup limits body group with
    | error fault =>
      simp [MixedFlat.readGroups, column, bind, Except.bind, Except.mapError] at failed
      exact ⟨index, fault, failed.symm⟩
    | ok values =>
      cases next : MixedFlat.readGroups limits body (index + 1) rest with
      | error fault =>
        simp [MixedFlat.readGroups, column, next, bind, Except.bind, Except.mapError] at failed
        subst cause
        exact ih next
      | ok columns =>
        simp [MixedFlat.readGroups, column, next, bind, Except.bind, Except.mapError, pure, Except.pure] at failed

private theorem binder_error {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {cause : Cause}
    (failed : MixedFlat.readParsed limits fields metadata body = .error cause.decodeError) :
    MixedFlat.bindBatch limits fields metadata body = .error cause.decodeError := by
  cases bound : MixedFlat.bindBatch limits fields metadata body with
  | error fault => simpa [MixedFlat.readParsed, bound, bind, Except.bind] using failed
  | ok plan =>
    cases read : MixedFlat.readGroups limits.view body 0 plan.assignment.groups with
    | error fault =>
      obtain ⟨field, column, rfl⟩ := groups_error_field read
      cases cause <;> simp [MixedFlat.readParsed, Cause.decodeError, bound, read, bind, Except.bind] at failed
    | ok columns =>
      simp [MixedFlat.readParsed, bound, read, bind, Except.bind, pure, Except.pure] at failed

private theorem layout_extent {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {cause : Cause}
    (failed : MixedFlat.bindBatch limits fields metadata body = .error cause.decodeError) :
    metadata.bodyLength = body.len := by
  by_contra different
  by_cases source : body.wf = true <;> cases cause <;>
    simp [MixedFlat.bindBatch, Cause.decodeError, source, different,
      throw, throwThe, MonadExceptOf.throw] at failed

theorem feed_layout_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset : Nat}
    {cause : Cause}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (feedError ordinal offset cause)) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        Wire cursor.limits (.leaf size packed) fields running range cause := by
  obtain ⟨_, clash, _⟩ | ⟨frame, _, _, typed, tag, raw, decoded⟩ := feed_late_failure phase failed
  · contradiction
  · obtain ⟨ordinalExact, offsetExact, typedExact⟩ := MixedFlat.Stream.Incremental.Error.batch.inj tag
    rw [← typedExact] at decoded
    obtain ⟨frameOffset, wire, bodyWf⟩ := completed_frame_at held incoming raw
    obtain ⟨metadata, accepted, available, dataBudget, rowsBudget, parsed⟩ := decode_rejected decoded
    have rejected := binder_error parsed
    have extent : metadata.bodyLength = frame.body.len := layout_extent (body := metadataBytes frame.body) rejected
    obtain ⟨metadataMatch, bodyRead⟩ := packed_frame wire bodyWf
    rw [metadataMatch] at accepted
    exact ⟨ordinalExact, offsetExact, frameRange frame, frameOffset.trans offsetExact.symm, wire.1,
      wire.2.2.1, available, metadata, metadataBytes frame.body, accepted, extent, bodyRead, dataBudget,
      rowsBudget, rejected⟩

private theorem layout_terminal {limits : MixedFlat.Stream.Incremental.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange} {cause : Cause}
    (wire : Wire limits input fields running range cause) :
    let remaining := limits.mixed.observation.ipc.batches - running.ordinal
    MixedFlat.Stream.Events.readNext limits.mixed input fields remaining running.ordinal running.rows range.offset =
      .error (.message running.ordinal range.offset (.decode cause.decodeError)) ∧
    MixedFlat.Stream.readBatches limits.mixed input fields remaining running.ordinal running.rows range.offset =
      .error (.batch running.ordinal (.decode cause.decodeError)) := by
  have nonempty : limits.mixed.observation.ipc.batches - running.ordinal ≠ 0 := by
    have available := wire.available
    omega
  have read : MixedFlat.Stream.readRecord limits.mixed input fields running.rows range.offset range.metadataSize =
      .error (.decode cause.decodeError) := by
    obtain ⟨metadata, body, metadataRead, extent, bodyRead, _, budget, bound⟩ := wire.rejected
    simp only [BatchRange.metadataSlice] at metadataRead
    simp only [BatchRange.bodyStart] at bodyRead
    simp [MixedFlat.Stream.readRecord, metadataRead, extent, BatchRange.bodyStart, bodyRead,
      budget, MixedFlat.readParsed, bound, bind, Except.bind, Except.mapError]
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

theorem layout_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
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
  obtain ⟨ordinal, offset, range, rangeOffset, admitted⟩ := feed_layout_wire finalHeld incoming finalPhase failed
  rw [finalLimits, openedLimits] at admitted
  obtain ⟨native, terminal⟩ := layout_terminal admitted
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

theorem layout_pull_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ := by
  obtain ⟨_, _, _, schemaRead, replay, _, _, _, failed, _⟩ := layout_exact run
  simpa only [List.map_map, Function.comp_def, Delivered.published, Run.nativeCause] using
    replay_read_all_error rfl schemaRead replay failed

theorem schedules_layout_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := layout_exact a
  have checkedB := layout_exact b
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
  obtain ⟨ordinalEq, offsetEq, causeEq⟩ :
      ordinalA = ordinalB ∧ offsetA = offsetB ∧ causeA.decodeError = causeB.decodeError := by
    simpa using coordinates
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [Run.ranges, Run.trace, Run.cause, feedError, rangesEq, eventsEq,
    ordinalEq, offsetEq, causeEq]

theorem layout_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, immutableError⟩ := layout_exact failed
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout
