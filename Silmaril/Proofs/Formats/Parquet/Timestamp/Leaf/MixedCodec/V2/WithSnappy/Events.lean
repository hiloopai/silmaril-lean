module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Wire
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2 (rowsAt rowsAtUsing traceUsing emitUsing)
open Silmaril.Numeric.Timestamp (Ticks)

theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Leaf.MixedCodec.V2.traceUsing_first_error split earlier failed

theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) := by
  simp [convert, opened, trace_first_error split earlier failed, emitUsing, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits output input ordinal = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      List.Forall₂ (GroupWire limits inputLimits.leaf bound) (List.range bound.snapshot.groupCount) groups ∧
      trace limits inputLimits.leaf bound =
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) := by
  cases opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    have emitted : emitUsing output bound (trace limits inputLimits.leaf bound)
        Error.source Error.closed Error.writer = .ok wire := by
      simpa [convert, opened, Except.mapError, Bind.bind, Except.bind] using written
    cases ended : (trace limits inputLimits.leaf bound).termination with
    | closed | closeError _ | readError _ => simp [emitUsing, ended] at emitted
    | eos =>
      obtain ⟨groups, decoded, events⟩ := Leaf.MixedCodec.V2.traceUsing_eos (by
        simpa only [trace] using ended)
      have witnesses := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => readGroup_wire read
      exact ⟨bound, groups, rfl, witnesses, events, Leaf.MixedCodec.V2.emitUsing_readback events emitted⟩

private theorem denote_twoCodec {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {indices : List Nat}
    (other : ∀ index ∈ indices, Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.snappy.id) :
    Reader.denoteGroups (rowsAtUsing bound (readGroup limits leafLimits bound) SourceError.groupFailure) indices =
      let prev := Reader.denoteGroups (rowsAt limits.twoCodec leafLimits bound) indices
      (prev.1, terminationOfTwoCodec prev.2) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
    have same := readGroup_twoCodec_agrees (limits := limits) (leafLimits := leafLimits)
      (other index List.mem_cons_self)
    have rest := ih (fun j mem => other j (List.mem_cons_of_mem _ mem))
    cases decoded : Leaf.MixedCodec.V2.readGroup limits.twoCodec leafLimits bound index <;>
      simp [Reader.denoteGroups, rowsAt, rowsAtUsing, Except.map, Except.mapError,
        same, decoded, rest, terminationOfTwoCodec, SourceError.ofTwoCodec]

theorem trace_twoCodec_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    (other : ∀ index ∈ List.range bound.snapshot.groupCount,
      Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.snappy.id) :
    trace limits leafLimits bound =
      let prev := Leaf.MixedCodec.V2.trace limits.twoCodec leafLimits bound
      ⟨prev.batches, terminationOfTwoCodec prev.termination⟩ := by
  unfold trace Leaf.MixedCodec.V2.trace traceUsing
  rw [denote_twoCodec (limits := limits) (leafLimits := leafLimits) other]
  rfl

private theorem emit_twoCodec_agrees (output : Arrow.ObservationLimits) (bound : Bound)
    (events : Arrow.Events.Trace (Leaf.Events.schema bound) Leaf.Events.Cell Leaf.MixedCodec.V2.SourceError) :
    emitUsing output bound ⟨events.batches, terminationOfTwoCodec events.termination⟩
        Error.source Error.closed Error.writer =
      (emitUsing output bound events Leaf.MixedCodec.V2.Error.source Leaf.MixedCodec.V2.Error.closed
        Leaf.MixedCodec.V2.Error.writer).mapError Error.ofTwoCodec := by
  cases events with
  | mk batches finish =>
    cases finish with
    | eos =>
      simp only [emitUsing, terminationOfTwoCodec]
      cases Arrow.TimestampStream.Writer.emit output (Leaf.Events.ToIpc.selectedBinding bound)
        (batches.map fun batch => batch.values ⟨0, Nat.zero_lt_one⟩) <;> rfl
    | closed | readError _ | closeError _ => rfl

theorem convert_twoCodec_agrees {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat}
    (other : ∀ bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound →
      ∀ index ∈ List.range bound.snapshot.groupCount,
        Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.snappy.id) :
    convert limits inputLimits output input ordinal =
      (Leaf.MixedCodec.V2.convert limits.twoCodec inputLimits output input ordinal).mapError Error.ofTwoCodec := by
  cases opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal with
  | error cause =>
    simp [convert, Leaf.MixedCodec.V2.convert, opened, Except.mapError, Bind.bind, Except.bind, Error.ofTwoCodec]
  | ok bound =>
    simp only [convert, Leaf.MixedCodec.V2.convert, opened, Except.mapError, Bind.bind, Except.bind]
    rw [trace_twoCodec_agrees (other bound opened)]
    exact emit_twoCodec_agrees output bound (Leaf.MixedCodec.V2.trace limits.twoCodec inputLimits.leaf bound)

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy
