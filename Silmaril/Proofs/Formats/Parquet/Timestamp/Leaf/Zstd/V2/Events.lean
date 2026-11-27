module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Arrow.TimestampStream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2

theorem readBound_reference (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Reader.denoteGroups (rowsAt limits leafLimits bound) (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ := by
  rw [readBound, Reader.readAll_opened]

private theorem denote_prefix {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before : List Nat} {groups : List (Slots bound)}
    (read : before.mapM (readGroup limits leafLimits bound) = .ok groups) (after : List Nat) :
    Reader.denoteGroups (rowsAt limits leafLimits bound) (before ++ after) =
      let tail := Reader.denoteGroups (rowsAt limits leafLimits bound) after
      (groups.map (Leaf.Events.rows bound) ++ tail.1, tail.2) := by
  induction before generalizing groups with
  | nil =>
    simp [pure, Except.pure] at read
    subst groups
    rfl
  | cons index rest ih =>
    cases first : readGroup limits leafLimits bound index with
    | error => simp [List.mapM_cons, first, Bind.bind, Except.bind] at read
    | ok slots =>
      cases more : rest.mapM (readGroup limits leafLimits bound) with
      | error => simp [List.mapM_cons, first, more, Bind.bind, Except.bind] at read
      | ok following =>
        have ordered : slots :: following = groups := by
          simpa [List.mapM_cons, first, more, Bind.bind, Except.bind, pure, Except.pure] using read
        subst groups
        simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError, ih more]

theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  rw [readBound_reference, split, denote_prefix earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, Except.mapError, List.map_map]

theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) := by
  have trace := readBound_first_error split earlier failed
  simp [convert, opened, trace, emit, Except.mapError, Bind.bind, Except.bind]

private theorem denote_complete {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {indices : List Nat}
    (ended : (Reader.denoteGroups (rowsAt limits leafLimits bound) indices).2 = .eos) :
    ∃ groups, indices.mapM (readGroup limits leafLimits bound) = .ok groups ∧
      (Reader.denoteGroups (rowsAt limits leafLimits bound) indices).1 = groups.map (Leaf.Events.rows bound) := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index rest ih =>
    cases first : readGroup limits leafLimits bound index with
    | error => simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] at ended
    | ok slots =>
      obtain ⟨groups, read, exactRows⟩ := ih (by
        simpa [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError] using ended)
      refine ⟨slots :: groups, ?_, ?_⟩
      · simp [List.mapM_cons, first, read, Bind.bind, Except.bind, pure, Except.pure]
      · simp [Reader.denoteGroups, rowsAt, first, Except.map, Except.mapError, exactRows]

private theorem emit_readback {output : Arrow.ObservationLimits} {schema : Scan.Schema String Leaf.Events.Kind}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell SourceError} {wire : KBytes}
    (one : schema.width = 1) (ended : trace.termination = .eos)
    (written : emit output (.ok ⟨schema, trace⟩) = .ok wire) :
    let column : Fin schema.width := ⟨0, by omega⟩
    let binding := Leaf.Events.ToIpc.bindingAt schema column
    let batches : List (Arrow.TimestampBatch.Column binding) := trace.batches.map (·.values column)
    ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
      result.binding = binding ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts = batches.map Arrow.TimestampBatch.Writer.tickCounts := by
  let column : Fin schema.width := ⟨0, by omega⟩
  let binding := Leaf.Events.ToIpc.bindingAt schema column
  let batches : List (Arrow.TimestampBatch.Column binding) := trace.batches.map (·.values column)
  have encoded : (Arrow.TimestampStream.Writer.emit output binding batches).mapError Error.writer = .ok wire := by
    simpa only [emit, ended, one, ↓reduceDIte, binding, batches, column] using written
  have native : Arrow.TimestampStream.Writer.emit output binding batches = .ok wire := by
    cases decoded : Arrow.TimestampStream.Writer.emit output binding batches with
    | error cause => simp [decoded, Except.mapError] at encoded
    | ok payload => simpa [decoded, Except.mapError] using encoded
  exact Arrow.TimestampStream.Writer.emit_readback native

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
      (List.range bound.snapshot.groupCount).mapM (readGroup limits inputLimits.leaf bound) = .ok groups ∧
      readBound limits inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) := by
  cases opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    let reference := Reader.denoteGroups (rowsAt limits inputLimits.leaf bound) (List.range bound.snapshot.groupCount)
    have events := readBound_reference limits inputLimits.leaf bound
    change readBound limits inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ at events
    have directly : emit output (.ok ⟨Leaf.Events.schema bound,
        ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩) = .ok wire := by
      simpa [convert, opened, events, Except.mapError, Bind.bind, Except.bind] using written
    cases ended : reference.2 with
    | readError _ | closeError _ | closed => simp [emit, ended] at directly
    | eos =>
      obtain ⟨groups, decoded, rows⟩ := denote_complete ended
      change reference.1 = groups.map (Leaf.Events.rows bound) at rows
      have trace : readBound limits inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound,
          ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ := by
        simpa [ended, rows, List.map_map] using events
      have width : (Leaf.Events.schema bound).width = 1 := rfl
      rw [ended, rows, List.map_map] at directly
      obtain ⟨result, read, binding, exactCounts⟩ := emit_readback width rfl directly
      refine ⟨bound, groups, rfl, decoded, trace, result, read, binding, exactCounts.trans ?_⟩
      exact batch_counts bound groups ⟨0, Nat.zero_lt_one⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2
