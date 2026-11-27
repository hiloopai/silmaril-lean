module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout

open Arrow.Framing.Incremental (Window)

/-- Recover the original complete frame and its exact typed layout rejection. -/
theorem feed_layout_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset : Nat}
    {cause : Cause}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (feedError ordinal offset cause)) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        Wire cursor.limits (.leaf size packed) fields running range cause :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.feed_layout_wire
    held incoming phase failed

/-- Replay every published batch and recover the terminal cause in the immutable readers. -/
theorem layout_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.layout_exact
    run

/-- The immutable pull reader returns the same complete prefix and terminal cause. -/
theorem layout_pull_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    Stream.Events.readAll limits.mixed (Portable.reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.layout_pull_exact
    run

/-- Two admitted schedules give the same original ranges, batches and typed cause. -/
theorem schedules_layout_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.schedules_layout_equivalent
    leftWf rightWf octets a b

/-- The same octets under the same limits cannot yield a successful finish. -/
theorem layout_no_success {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.layout_no_success
    leftWf rightWf octets failed succeeded

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout
