module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.Defs
import Silmaril.Formats.Arrow.Framing.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.BodyCutoff
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)
open MixedFlat.Stream (BatchRange)

theorem wait_body {cursor : Cursor} {header chunk : KBytes} {offset size : Nat}
    {pending : Arrow.Framing.Incremental.Buffer size}
    (atBody : cursor.input = .body offset header size pending)
    (valid : chunk.wf = true) (short : pending.bytes.len + chunk.len < size) :
    feed cursor chunk = .ok (.wait
      { cursor with input := .body offset header size (pending.feed chunk valid).buffered }) := by
  simp [feed, atBody, Arrow.Framing.Incremental.feed_body_wait (limits := cursor.limits.mixed.observation.ipc)
    valid short, bind, Except.bind, Except.mapError, pure, Except.pure]

theorem body_cutoff_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run := by
  obtain ⟨opened, header, pending, opening, records, atBody, headerSize, exhausted, short,
    indexed, available, metadata, checkedMetadata, declared⟩ := run.ran
  obtain ⟨openedHeld, openedLimits, phase, readSchema⟩ := open_agrees opening
  change MixedFlat.Stream.readSchemaFrame limits.mixed.observation.ipc (reference wire) =
    .ok (run.fields, opened.messageOffset) at readSchema
  rw [← openedLimits] at openedHeld
  obtain ⟨running, finalHeld, _, finalPhase, _, eagerSuffix⟩ :=
    steps_agree records openedHeld phase
  obtain ⟨replayed, replayPhase, replay⟩ := steps_replay records openedHeld phase
  have runningExact := (Phase.records.inj (finalPhase.symm.trans replayPhase)).2
  subst replayed
  have ordinal : running.ordinal = run.ordinal := by
    simpa [finalPhase, Phase.ordinal] using indexed
  have bodyState : (Arrow.Framing.Incremental.State.body run.attempted.offset header
      run.attempted.bodyLength pending).InCarrier limits.mixed.observation.ipc (reference wire) := by
    simpa only [atBody, openedLimits, reference] using finalHeld
  have atEnd : (Arrow.Framing.Incremental.State.body run.attempted.offset header
      run.attempted.bodyLength pending).position = (reference wire).len := by
    change _ = wire.len
    simpa only [Cursor.position, atBody] using exhausted
  obtain ⟨envelope, truncated, stopped⟩ :=
    Arrow.Framing.Incremental.finish_body_exact rfl bodyState atEnd short
  rw [headerSize] at envelope truncated stopped
  have offset : run.final.messageOffset = run.attempted.offset := by
    simp [Cursor.messageOffset, atBody]
  have finished : finish run.final = .error run.cause := by
    simp [finish, atBody, stopped, indexed, Run.cause, cutoffError, BatchRange.bodyStart,
      bind, Except.bind, Except.mapError]
  let mark := Position.ofRunning limits.mixed running run.attempted.offset
  have remaining : mark.remaining ≠ 0 := by
    change limits.mixed.observation.ipc.batches - running.ordinal ≠ 0
    omega
  have readRecord : MixedFlat.Stream.readRecord limits.mixed (reference wire) run.fields
      mark.rows mark.offset run.attempted.metadataSize = .error (.body (.malformed .truncated)) := by
    simp only [BatchRange.metadataSlice] at checkedMetadata
    simp [mark, Position.ofRunning, MixedFlat.Stream.readRecord, checkedMetadata, declared,
      BatchRange.bodyStart, truncated, bind, Except.bind, Except.mapError]
  change MixedFlat.Stream.readRecord limits.mixed (reference wire) run.fields running.rows
    run.attempted.offset run.attempted.metadataSize = _ at readRecord
  have native : mark.readNext limits.mixed (reference wire) run.fields =
      .error (.message run.ordinal mark.offset (.body (.malformed .truncated))) := by
    change MixedFlat.Stream.Events.readNext limits.mixed (reference wire) run.fields
      mark.remaining running.ordinal running.rows run.attempted.offset = _
    simp only [MixedFlat.Stream.Events.readNext, envelope, Except.mapError, bind, Except.bind,
      remaining, ite_false]
    split
    · rename_i cause rejected
      rw [readRecord] at rejected
      have same := Except.error.inj rejected
      subst cause
      rw [ordinal]
      rfl
    · rename_i _ accepted
      rw [readRecord] at accepted
      contradiction
  have eagerError : MixedFlat.Stream.readBatches limits.mixed (reference wire) run.fields
      mark.remaining mark.ordinal mark.rows mark.offset =
        .error (.batch run.ordinal (.body (.malformed .truncated))) := by
    change MixedFlat.Stream.readBatches limits.mixed (reference wire) run.fields
      mark.remaining running.ordinal running.rows run.attempted.offset = _
    obtain ⟨fuel, exactFuel⟩ := Nat.exists_eq_succ_of_ne_zero remaining
    rw [exactFuel, MixedFlat.Stream.readBatches]
    simp [envelope, readRecord, ordinal, bind, Except.bind, Except.mapError]
  refine ⟨opened.messageOffset, mark, readSchema, ?_, ordinal, rfl, envelope, truncated,
    finished, native, ?_⟩
  · simpa only [openedLimits, offset, mark, reference] using replay
  · simp only [openedLimits, offset] at eagerSuffix
    change MixedFlat.Stream.readBatches limits.mixed (reference wire) run.fields
      limits.mixed.observation.ipc.batches 0 0 opened.messageOffset =
        (MixedFlat.Stream.readBatches limits.mixed (reference wire) run.fields
          mark.remaining mark.ordinal mark.rows mark.offset).map _ at eagerSuffix
    rw [eagerError] at eagerSuffix
    have valid : (reference wire).wf = true := rfl
    simp [MixedFlat.Stream.read, valid, readSchema, eagerSuffix, bind, Except.bind, Except.map]

theorem schedules_body_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := body_cutoff_exact a
  have checkedB := body_cutoff_exact b
  rcases a with ⟨fieldsA, batchesA, cursorA, attemptA, ordinalA, runA⟩
  rcases b with ⟨fieldsB, batchesB, cursorB, attemptB, ordinalB, runB⟩
  obtain ⟨startA, stopA, schemaA, replayA, ordA, atA, envA, _, _, failedA, _⟩ := checkedA
  obtain ⟨startB, stopB, schemaB, replayB, ordB, atB, envB, _, _, failedB, _⟩ := checkedB
  rw [sameRef] at schemaA replayA failedA envA
  obtain ⟨fieldsEq, startEq⟩ := Prod.mk.inj (Except.ok.inj (schemaA.symm.trans schemaB))
  dsimp only at fieldsEq startEq
  subst fieldsB
  subst startB
  obtain ⟨publishedEq, stopEq, _⟩ := replay_unique_at_error replayA replayB failedA failedB
  have rangesEq := congrArg (List.map fun (item : Published fieldsA) => item.1.range) publishedEq
  have eventsEq := congrArg (List.map fun (item : Published fieldsA) => item.2) publishedEq
  have ordinalEq : ordinalA = ordinalB := ordA.symm.trans ((congrArg Position.ordinal stopEq).trans ordB)
  have offsetEq : attemptA.offset = attemptB.offset :=
    atA.symm.trans ((congrArg Position.offset stopEq).trans atB)
  rw [stopEq] at envA
  have sizeEq : attemptA.metadataSize = attemptB.metadataSize :=
    Envelope.metadata.inj (Except.ok.inj (envA.symm.trans envB))
  have bodyOffsetEq : attemptA.bodyStart = attemptB.bodyStart := by
    simp [BatchRange.bodyStart, offsetEq, sizeEq]
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [Run.ranges, Run.trace, Run.cause, rangesEq, eventsEq, ordinalEq, bodyOffsetEq]

theorem body_cutoff_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (cutoff : Run limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, immutableError⟩ := body_cutoff_exact cutoff
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff
