module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Wire
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2 (rowsAtUsing traceUsing emitUsing)
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

private theorem denote_threeCodec {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {indices : List Nat}
    (other : ∀ index ∈ indices, Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.uncompressed.id) :
    Reader.denoteGroups (rowsAtUsing bound (readGroup limits leafLimits bound) SourceError.groupFailure) indices =
      let prev := Reader.denoteGroups (rowsAtUsing bound (Leaf.MixedCodec.V2.WithSnappy.readGroup limits.threeCodec leafLimits bound)
        Leaf.MixedCodec.V2.WithSnappy.SourceError.groupFailure) indices
      (prev.1, terminationOfThreeCodec prev.2) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
    have same := readGroup_threeCodec_agrees (limits := limits) (leafLimits := leafLimits)
      (other index List.mem_cons_self)
    have rest := ih (fun j mem => other j (List.mem_cons_of_mem _ mem))
    cases decoded : Leaf.MixedCodec.V2.WithSnappy.readGroup limits.threeCodec leafLimits bound index <;>
      simp [Reader.denoteGroups, rowsAtUsing, Except.map, Except.mapError,
        same, decoded, rest, terminationOfThreeCodec, SourceError.ofThreeCodec]

theorem trace_threeCodec_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    (other : ∀ index ∈ List.range bound.snapshot.groupCount,
      Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.uncompressed.id) :
    trace limits leafLimits bound =
      let prev := Leaf.MixedCodec.V2.WithSnappy.trace limits.threeCodec leafLimits bound
      ⟨prev.batches, terminationOfThreeCodec prev.termination⟩ := by
  unfold trace Leaf.MixedCodec.V2.WithSnappy.trace traceUsing
  rw [denote_threeCodec (limits := limits) (leafLimits := leafLimits) other]

private theorem emit_threeCodec_agrees (output : Arrow.ObservationLimits) (bound : Bound)
    (events : Arrow.Events.Trace (Leaf.Events.schema bound) Leaf.Events.Cell Leaf.MixedCodec.V2.WithSnappy.SourceError) :
    emitUsing output bound ⟨events.batches, terminationOfThreeCodec events.termination⟩
        Error.source Error.closed Error.writer =
      (emitUsing output bound events Leaf.MixedCodec.V2.WithSnappy.Error.source Leaf.MixedCodec.V2.WithSnappy.Error.closed
        Leaf.MixedCodec.V2.WithSnappy.Error.writer).mapError Error.ofThreeCodec := by
  cases events with
  | mk batches finish =>
    cases finish with
    | eos =>
      simp only [emitUsing, terminationOfThreeCodec]
      cases Arrow.TimestampStream.Writer.emit output (Leaf.Events.ToIpc.selectedBinding bound)
        (batches.map fun batch => batch.values ⟨0, Nat.zero_lt_one⟩) <;> rfl
    | closed | readError _ | closeError _ => rfl

theorem convert_threeCodec_agrees {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat}
    (other : ∀ bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound →
      ∀ index ∈ List.range bound.snapshot.groupCount,
        Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.uncompressed.id) :
    convert limits inputLimits output input ordinal =
      (Leaf.MixedCodec.V2.WithSnappy.convert limits.threeCodec inputLimits output input ordinal).mapError Error.ofThreeCodec := by
  cases opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal with
  | error cause =>
    simp [convert, Leaf.MixedCodec.V2.WithSnappy.convert, opened, Except.mapError, Bind.bind, Except.bind, Error.ofThreeCodec]
  | ok bound =>
    simp only [convert, Leaf.MixedCodec.V2.WithSnappy.convert, opened, Except.mapError, Bind.bind, Except.bind]
    rw [trace_threeCodec_agrees (other bound opened)]
    exact emit_threeCodec_agrees output bound (Leaf.MixedCodec.V2.WithSnappy.trace limits.threeCodec inputLimits.leaf bound)

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed
