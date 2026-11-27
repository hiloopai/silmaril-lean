module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Arrow.TimestampStream.Writer.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Wire
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2
open Silmaril.Numeric.Timestamp (Ticks)

private theorem denote_prefix {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before : List Nat} {groups : List (Slots bound)}
    (read : before.mapM (readGroup limits leafLimits bound) = .ok groups) (after : List Nat) :
    Reader.denoteGroups (rowsAt limits leafLimits bound) (before ++ after) =
      let tail := Reader.denoteGroups (rowsAt limits leafLimits bound) after
      (groups.map (Leaf.Events.rows bound) ++ tail.1, tail.2) := by
  have paired := List.mapM_eq_ok_iff_forall₂.mp read
  clear read
  induction paired with
  | nil => rfl
  | cons first _ ih =>
    simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError, ih]

theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ := by
  rw [trace, split, denote_prefix earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, Except.mapError, List.map_map]

theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) := by
  simp [convert, opened, trace_first_error split earlier failed, Except.mapError, Bind.bind, Except.bind]

private theorem denote_complete {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {indices : List Nat} (ended : (Reader.denoteGroups (rowsAt limits leafLimits bound) indices).2 = .eos) :
    ∃ groups, indices.mapM (readGroup limits leafLimits bound) = .ok groups ∧
      (Reader.denoteGroups (rowsAt limits leafLimits bound) indices).1 = groups.map (Leaf.Events.rows bound) := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index rest ih =>
    cases first : readGroup limits leafLimits bound index with
    | error => simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] at ended
    | ok slots =>
      obtain ⟨groups, tailRead, exactRows⟩ := ih (by
        simpa [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] using ended)
      refine ⟨slots :: groups, ?_, ?_⟩
      · simp [List.mapM_cons, first, tailRead, Bind.bind, Except.bind, pure, Except.pure]
      · simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError, exactRows]

private theorem batch_counts (bound : Bound) (groups : List (Slots bound))
    (column : Fin (Leaf.Events.schema bound).width) :
    (((groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound)).map (·.values column)) :
      List (Arrow.TimestampBatch.Column (Leaf.Events.ToIpc.bindingAt (Leaf.Events.schema bound) column))).map
        Arrow.TimestampBatch.Writer.tickCounts = groups.map (List.map (Option.map Ticks.ticks)) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    exact congrArg₂ List.cons (Leaf.Events.batch_slots bound group column).2 ih

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
    cases ended : (trace limits inputLimits.leaf bound).termination with
    | closed | closeError _ | readError _ =>
      simp [convert, opened, ended, Except.mapError, Bind.bind, Except.bind] at written
    | eos =>
      obtain ⟨groups, decoded, rows⟩ := denote_complete ended
      have events : trace limits inputLimits.leaf bound =
          ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩ := by
        change (Reader.denoteGroups (rowsAt limits inputLimits.leaf bound) _).2 = .eos at ended
        simp only [trace, ended, rows, List.map_map]
      let column : Fin (Leaf.Events.schema bound).width := ⟨0, Nat.zero_lt_one⟩
      let binding := Leaf.Events.ToIpc.selectedBinding bound
      let batches := (groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound)).map (·.values column)
      have conversion : convert limits inputLimits output input ordinal =
          (Arrow.TimestampStream.Writer.emit output binding batches).mapError Error.writer := by
        simp only [convert, opened, Except.mapError, Bind.bind, Except.bind, events]
        rfl
      have mapped := conversion.symm.trans written
      have emitted : Arrow.TimestampStream.Writer.emit output binding batches = .ok wire := by
        cases native : Arrow.TimestampStream.Writer.emit output binding batches with
        | error => simp [native, Except.mapError] at mapped
        | ok => simpa [native, Except.mapError] using mapped
      obtain ⟨result, read, descriptor, ticks⟩ := Arrow.TimestampStream.Writer.emit_readback emitted
      have witnesses := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => readGroup_wire read
      exact ⟨bound, groups, rfl, witnesses, events, result, read, descriptor,
        ticks.trans (batch_counts bound groups column)⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2
