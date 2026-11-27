module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.NodeCount
open MixedFlat.Stream.Incremental.Portable (reference)
open MixedFlat.Stream (BatchRange)
open Arrow.Framing.Incremental (Window)

theorem feed_node_count_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset expected actual : Nat}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (feedError ordinal offset expected actual)) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        Wire cursor.limits.mixed (.leaf size packed) fields running range expected actual := by
  obtain ⟨ordinalEq, offsetEq, range, rangeEq, wire⟩ :=
    RecordMetadata.feed_metadata_wire held incoming phase failed
  exact ⟨ordinalEq, offsetEq, range, rangeEq, wire.envelope, wire.planned, wire.body,
    wire.available, wire.rejected⟩

theorem node_count_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run := by
  obtain ⟨startOffset, running, range, schemaRead, replay, ordinalEq, rangeEq, wire, native, eager⟩ :=
    RecordMetadata.metadata_exact run.toMetadata
  exact ⟨startOffset, running, range, schemaRead, replay, ordinalEq, rangeEq,
    ⟨wire.envelope, wire.planned, wire.body, wire.available, wire.rejected⟩, native, eager⟩

theorem node_count_pull_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ :=
  RecordMetadata.metadata_pull_exact run.toMetadata

theorem schedules_node_count_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  RecordMetadata.schedules_metadata_equivalent leftWf rightWf octets a.toMetadata b.toMetadata

theorem node_count_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False :=
  RecordMetadata.metadata_no_success leftWf rightWf octets failed.toMetadata succeeded

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount
