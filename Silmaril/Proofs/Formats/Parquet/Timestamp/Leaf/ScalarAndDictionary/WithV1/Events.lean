module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Wire
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary (Limits)
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
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

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
