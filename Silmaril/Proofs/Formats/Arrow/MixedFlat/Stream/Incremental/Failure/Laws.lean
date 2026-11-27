module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs
import Silmaril.Formats.Arrow.Framing.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)

theorem replaySteps {size packed : Nat} {fields : List MixedFlat.Field}
    {before last : Cursor} {batches : List (Delivered fields)} {running : Running}
    (steps : RecordSteps size packed fields before batches last)
    (held : before.input.InCarrier before.limits.mixed.observation.ipc (.leaf size packed))
    (phase : before.phase = .records fields running) :
    ∃ final,
      last.phase = .records fields final ∧
      Replay before.limits.mixed (.leaf size packed) fields
        (.ofRunning before.limits.mixed running before.messageOffset)
        (batches.map Delivered.published) (.ofRunning before.limits.mixed final last.messageOffset) := by
  induction steps generalizing running with
  | stop => exact ⟨running, phase, .stop _⟩
  | wait incoming step _ ih =>
    obtain ⟨nextHeld, sameLimits, samePhase, sameOffset, _⟩ := feed_refines held incoming step
    rw [← sameLimits] at nextHeld
    simpa only [sameLimits, sameOffset] using ih nextHeld (samePhase.trans phase)
  | advance incoming step _ ih =>
    obtain ⟨⟨nextHeld, sameLimits, _, _⟩, samePhase, sameOffset⟩ := feed_refines held incoming step
    rw [← sameLimits] at nextHeld
    simpa only [sameLimits, sameOffset] using ih nextHeld (samePhase.trans phase)
  | @batch before next last chunk rest value batches incoming step _ ih =>
    obtain ⟨⟨nextHeld, sameLimits, _, _⟩, active, samePhase, nextPhase, _, nextOffset,
      pulled, read, sameRecord, sameEvent⟩ := feed_refines held incoming step
    have same := (Phase.records.inj (samePhase.symm.trans phase)).2
    subst active
    rw [← sameLimits] at nextHeld
    obtain ⟨final, finalPhase, replay⟩ := ih nextHeld nextPhase
    let mark := Position.ofRunning before.limits.mixed running before.messageOffset
    have readMark : mark.readNext before.limits.mixed (.leaf size packed) fields = .ok (some pulled) := read
    have advance : mark.after pulled.record =
        Position.ofRunning before.limits.mixed
          ⟨running.ordinal + 1, running.rows + value.event.rowCount, running.dataBuffers + value.dataBuffers⟩
          next.messageOffset := by
      simp [mark, Position.after, Position.ofRunning, sameRecord, nextOffset, value.aligned.1, Nat.sub_sub]
    rw [sameLimits] at replay
    rw [← advance] at replay
    refine ⟨final, finalPhase, ?_⟩
    simpa only [List.map_cons, Delivered.published, sameRecord, sameEvent] using Replay.next readMark replay

theorem replayUnique {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {initial a b : Position} {left right : List (Published fields)}
    {causeA causeB : MixedFlat.Stream.Events.Error}
    (replayA : Replay limits input fields initial left a)
    (replayB : Replay limits input fields initial right b)
    (failedA : a.readNext limits input fields = .error causeA)
    (failedB : b.readNext limits input fields = .error causeB) :
    left = right ∧ a = b ∧ causeA = causeB := by
  induction replayA generalizing b right with
  | stop =>
    cases replayB with
    | stop =>
      exact ⟨rfl, rfl, Except.error.inj (failedA.symm.trans failedB)⟩
    | next read _ =>
      rw [failedA] at read
      contradiction
  | next read _ ih =>
    cases replayB with
    | stop =>
      rw [failedB] at read
      contradiction
    | next other rest =>
      have same := Option.some.inj (Except.ok.inj (read.symm.trans other))
      subst same
      obtain ⟨prefixEq, finalEq, causeEq⟩ := ih rest failedA failedB
      exact ⟨congrArg (List.cons _) prefixEq, finalEq, causeEq⟩

theorem tail_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (result : TailFailure limits wire) : TailAgreement limits wire result := by
  obtain ⟨opened, final, chunk, opening, records, incoming, failure⟩ := result.ran
  obtain ⟨openedHeld, openedLimits, phase, readSchema⟩ := open_agrees opening
  change MixedFlat.Stream.readSchemaFrame limits.mixed.observation.ipc (reference wire) =
    .ok (result.fields, opened.messageOffset) at readSchema
  rw [← openedLimits] at openedHeld
  obtain ⟨running, finalHeld, finalLimits, runningPhase, _, eagerSuffix⟩ :=
    steps_agree records openedHeld phase
  obtain ⟨replayed, replayPhase, replay⟩ := replaySteps records openedHeld phase
  have runningExact := (Phase.records.inj (runningPhase.symm.trans replayPhase)).2
  subst replayed
  rw [← finalLimits] at finalHeld
  have failureCause := feed_late_failure runningPhase failure
  obtain ⟨framing, tag, raw⟩ | ⟨_, _, _, _, impossible, _⟩ := failureCause
  · have exactTag : some result.ordinal = some running.ordinal ∧
        (⟨.tail, result.firstTail, .malformed .trailingBytes⟩ : Arrow.Framing.Incremental.Failure) = framing :=
      MixedFlat.Stream.Incremental.Error.framing.inj tag
    have ordinal := Option.some.inj exactTag.1
    rw [← exactTag.2] at raw
    obtain ⟨tail, bounded, envelope⟩ :=
      Arrow.Framing.Incremental.feed_tail_exact rfl finalHeld incoming raw
    change result.firstTail = final.messageOffset + 8 at tail
    change readEnvelope final.limits.mixed.observation.ipc (Portable.reference wire) final.messageOffset =
      .ok .eos at envelope
    rw [finalLimits, openedLimits] at envelope
    change result.firstTail < wire.len at bounded
    have extra : final.messageOffset + 8 ≠ (Portable.reference wire).len := by
      change final.messageOffset + 8 ≠ wire.len
      omega
    let mark := Position.ofRunning limits.mixed running final.messageOffset
    have native : mark.readNext limits.mixed (Portable.reference wire) result.fields =
        .error (.message result.ordinal mark.offset .trailingBytes) := by
      simp [mark, Position.readNext, Position.ofRunning, MixedFlat.Stream.Events.readNext,
        envelope, extra, ordinal, bind, Except.bind, Except.mapError]
      rfl
    have eagerError : MixedFlat.Stream.readBatches limits.mixed (Portable.reference wire) result.fields
        mark.remaining mark.ordinal mark.rows mark.offset = .error (.batch result.ordinal .trailingBytes) := by
      simp [mark, Position.ofRunning, MixedFlat.Stream.readBatches, envelope, extra, ordinal,
        bind, Except.bind, Except.mapError]
      rfl
    refine ⟨opened.messageOffset, mark, readSchema, ?_, ordinal.symm, tail.symm, bounded, native, ?_⟩
    · simpa only [openedLimits, mark, reference] using replay
    · simp only [openedLimits] at eagerSuffix
      change MixedFlat.Stream.readBatches limits.mixed (Portable.reference wire) result.fields
        limits.mixed.observation.ipc.batches 0 0 opened.messageOffset =
          (MixedFlat.Stream.readBatches limits.mixed (Portable.reference wire) result.fields
            mark.remaining mark.ordinal mark.rows mark.offset).map _ at eagerSuffix
      rw [eagerError] at eagerSuffix
      have valid : (Portable.reference wire).wf = true := rfl
      simp [MixedFlat.Stream.read, valid, readSchema, eagerSuffix,
        bind, Except.bind, Except.map]
  · contradiction

theorem schedules_tail_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : TailFailure limits left) (b : TailFailure limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := tail_exact a
  have checkedB := tail_exact b
  rcases a with ⟨fieldsA, batchesA, ordinalA, tailA, runA⟩
  rcases b with ⟨fieldsB, batchesB, ordinalB, tailB, runB⟩
  obtain ⟨startA, finalA, schemaA, replayA, ordA, atA, _, failedA, _⟩ := checkedA
  obtain ⟨startB, finalB, schemaB, replayB, ordB, atB, _, failedB, _⟩ := checkedB
  rw [sameRef] at schemaA replayA failedA
  obtain ⟨fieldsEq, startEq⟩ := Prod.mk.inj (Except.ok.inj (schemaA.symm.trans schemaB))
  dsimp only at fieldsEq startEq
  subst fieldsB
  subst startB
  obtain ⟨publishedEq, finalEq, _⟩ := replayUnique replayA replayB failedA failedB
  have rangesEq := congrArg (List.map fun (item : Published fieldsA) => item.1.range) publishedEq
  have eventsEq := congrArg (List.map fun (item : Published fieldsA) => item.2) publishedEq
  have ordinalEq : ordinalA = ordinalB := ordA.symm.trans ((congrArg Position.ordinal finalEq).trans ordB)
  have tailEq : tailA = tailB := atA.symm.trans
    ((congrArg (fun position : Position => position.offset + 8) finalEq).trans atB)
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [TailFailure.ranges, TailFailure.trace, TailFailure.cause, tailError, rangesEq, eventsEq, ordinalEq, tailEq]

theorem tail_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : TailFailure limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, immutableError⟩ := tail_exact failed
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
