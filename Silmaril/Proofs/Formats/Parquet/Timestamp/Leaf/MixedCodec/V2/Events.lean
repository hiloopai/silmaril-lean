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

private theorem denote_prefix {ε δ : Type} {bound : Bound}
    {read : Nat → Except ε (Slots bound)} {tag : Nat → ε → δ}
    {before : List Nat} {groups : List (Slots bound)} (finish : before.mapM read = .ok groups)
    (after : List Nat) :
    Reader.denoteGroups (rowsAtUsing bound read tag) (before ++ after) =
      let tail := Reader.denoteGroups (rowsAtUsing bound read tag) after
      (groups.map (Leaf.Events.rows bound) ++ tail.1, tail.2) := by
  have paired := List.mapM_eq_ok_iff_forall₂.mp finish
  clear finish
  induction paired with
  | nil => rfl
  | cons first _ ih =>
    simp [Reader.denoteGroups, rowsAtUsing, first, Except.map, Except.mapError, ih]

theorem traceUsing_first_error {ε δ : Type} {bound : Bound} {read : Nat → Except ε (Slots bound)}
    {tag : Nat → ε → δ} {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : ε}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM read = .ok groups) (failed : read index = .error cause) :
    traceUsing bound read tag =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (tag index cause)⟩ := by
  rw [traceUsing, split, denote_prefix earlier]
  simp [Reader.denoteGroups, rowsAtUsing, failed, Except.map, Except.mapError, List.map_map]

theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  traceUsing_first_error split earlier failed

theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) := by
  simp [convert, opened, trace_first_error split earlier failed, emitUsing, Except.mapError, Bind.bind, Except.bind]

private theorem denote_complete {ε δ : Type} {bound : Bound} {read : Nat → Except ε (Slots bound)}
    {tag : Nat → ε → δ} {indices : List Nat}
    (ended : (Reader.denoteGroups (rowsAtUsing bound read tag) indices).2 = .eos) :
    ∃ groups, indices.mapM read = .ok groups ∧
      (Reader.denoteGroups (rowsAtUsing bound read tag) indices).1 = groups.map (Leaf.Events.rows bound) := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index rest ih =>
    cases first : read index with
    | error => simp [Reader.denoteGroups, rowsAtUsing, first, Except.map, Except.mapError] at ended
    | ok slots =>
      obtain ⟨groups, tailRead, exactRows⟩ := ih (by
        simpa [Reader.denoteGroups, rowsAtUsing, first, Except.map, Except.mapError] using ended)
      refine ⟨slots :: groups, ?_, ?_⟩
      · simp [List.mapM_cons, first, tailRead, Bind.bind, Except.bind, pure, Except.pure]
      · simp [Reader.denoteGroups, rowsAtUsing, first, Except.map, Except.mapError, exactRows]

theorem traceUsing_eos {ε δ : Type} {bound : Bound} {read : Nat → Except ε (Slots bound)} {tag : Nat → ε → δ}
    (ended : (traceUsing bound read tag).termination = .eos) :
    ∃ groups, (List.range bound.snapshot.groupCount).mapM read = .ok groups ∧
      traceUsing bound read tag = ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩ := by
  change (Reader.denoteGroups (rowsAtUsing bound read tag) _).2 = .eos at ended
  obtain ⟨groups, decoded, rows⟩ := denote_complete ended
  exact ⟨groups, decoded, by simp only [traceUsing, ended, rows, List.map_map]⟩

private theorem batch_counts (bound : Bound) (groups : List (Slots bound))
    (column : Fin (Leaf.Events.schema bound).width) :
    (((groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound)).map (·.values column)) :
      List (Arrow.TimestampBatch.Column (Leaf.Events.ToIpc.bindingAt (Leaf.Events.schema bound) column))).map
        Arrow.TimestampBatch.Writer.tickCounts = groups.map (List.map (Option.map Ticks.ticks)) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    exact congrArg₂ List.cons (Leaf.Events.batch_slots bound group column).2 ih

theorem emitUsing_readback {ε δ : Type} {bound : Bound} {output : Arrow.ObservationLimits}
    {events : Arrow.Events.Trace (Leaf.Events.schema bound) Leaf.Events.Cell ε}
    {sourceError : ε → δ} {closed : δ} {writerError : Arrow.TimestampStream.Writer.Error → δ}
    {groups : List (Slots bound)} {wire : KBytes}
    (complete : events = ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩)
    (written : emitUsing output bound events sourceError closed writerError = .ok wire) :
    ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
      result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        groups.map (List.map (Option.map Ticks.ticks)) := by
  subst events
  let column : Fin (Leaf.Events.schema bound).width := ⟨0, Nat.zero_lt_one⟩
  let binding := Leaf.Events.ToIpc.selectedBinding bound
  let batches := (groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound)).map (·.values column)
  change (Arrow.TimestampStream.Writer.emit output binding batches).mapError writerError = .ok wire at written
  have emitted : Arrow.TimestampStream.Writer.emit output binding batches = .ok wire := by
    cases native : Arrow.TimestampStream.Writer.emit output binding batches with
    | error => simp [native, Except.mapError] at written
    | ok => simpa [native, Except.mapError] using written
  obtain ⟨result, read, descriptor, ticks⟩ := Arrow.TimestampStream.Writer.emit_readback emitted
  exact ⟨result, read, descriptor, ticks.trans (batch_counts bound groups column)⟩

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
      obtain ⟨groups, decoded, events⟩ := traceUsing_eos (by
        simpa only [trace] using ended)
      have witnesses := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => readGroup_wire read
      exact ⟨bound, groups, rfl, witnesses, events, emitUsing_readback events emitted⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2
