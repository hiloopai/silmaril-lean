module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Laws

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

/-- Successful feed calls retain each exact immutable record and event
up to the pending original position. -/
theorem steps_replay {size packed : Nat} {fields : List MixedFlat.Field}
    {before last : Cursor} {batches : List (Delivered fields)} {running : Running}
    (steps : RecordSteps size packed fields before batches last)
    (held : before.input.InCarrier before.limits.mixed.observation.ipc (.leaf size packed))
    (phase : before.phase = .records fields running) :
    ∃ final,
      last.phase = .records fields final ∧
      Replay before.limits.mixed (.leaf size packed) fields
        (.ofRunning before.limits.mixed running before.messageOffset)
        (batches.map Delivered.published) (.ofRunning before.limits.mixed final last.messageOffset) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.replaySteps steps held phase

/-- An immutable terminal error determines the exact preceding record and
event sequence and the final position. -/
theorem replay_unique_at_error {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {initial a b : Position} {left right : List (Published fields)}
    {causeA causeB : MixedFlat.Stream.Events.Error}
    (replayA : Replay limits input fields initial left a)
    (replayB : Replay limits input fields initial right b)
    (failedA : a.readNext limits input fields = .error causeA)
    (failedB : b.readNext limits input fields = .error causeB) :
    left = right ∧ a = b ∧ causeA = causeB :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.replayUnique replayA replayB failedA failedB

/-- The exact emitted prefix replays against immutable pulls. The native
error identifies the original EOS marker and the feed error identifies the
first tail byte eight bytes later, at the same next batch ordinal. -/
theorem tail_exact {limits : Incremental.Limits} {wire : KBytes}
    (result : TailFailure limits wire) : TailAgreement limits wire result :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.tail_exact result

/-- Two admitted schedules that encounter the tail have the same checked
schema, ordered events, absolute ranges and original typed feed error. -/
theorem schedules_tail_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : TailFailure limits left) (b : TailFailure limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.schedules_tail_equivalent
    leftWf rightWf octets a b

/-- A tail failure rules out successful finalization of the same complete
octets under the same incremental limits. -/
theorem tail_no_success {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : TailFailure limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.tail_no_success
    leftWf rightWf octets failed succeeded

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
