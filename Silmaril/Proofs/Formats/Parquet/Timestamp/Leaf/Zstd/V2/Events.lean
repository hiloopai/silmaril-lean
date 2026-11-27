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

theorem readBoundWith_reference (bound : Bound) (read : Nat → Except GroupError (Slots bound)) :
    let reference := Reader.denoteGroups (rowsAtWith bound read) (List.range bound.snapshot.groupCount)
    readBoundWith bound read = .ok ⟨Leaf.Events.schema bound,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ := by
  rw [readBoundWith, Reader.readAll_opened]

theorem readBound_reference (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Reader.denoteGroups (rowsAt limits leafLimits bound) (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ :=
  readBoundWith_reference bound (readGroup limits leafLimits bound)

private theorem denote_prefix {bound : Bound} {groupRead : Nat → Except GroupError (Slots bound)}
    {before : List Nat} {groups : List (Slots bound)}
    (read : before.mapM groupRead = .ok groups) (after : List Nat) :
    Reader.denoteGroups (rowsAtWith bound groupRead) (before ++ after) =
      let tail := Reader.denoteGroups (rowsAtWith bound groupRead) after
      (groups.map (Leaf.Events.rows bound) ++ tail.1, tail.2) := by
  induction before generalizing groups with
  | nil =>
    simp [pure, Except.pure] at read
    subst groups
    rfl
  | cons index rest ih =>
    cases first : groupRead index with
    | error => simp [List.mapM_cons, first, Bind.bind, Except.bind] at read
    | ok slots =>
      cases more : rest.mapM groupRead with
      | error => simp [List.mapM_cons, first, more, Bind.bind, Except.bind] at read
      | ok following =>
        have ordered : slots :: following = groups := by
          simpa [List.mapM_cons, first, more, Bind.bind, Except.bind, pure, Except.pure] using read
        subst groups
        simp [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError, ih more]

theorem readBoundWith_first_error {bound : Bound} {read : Nat → Except GroupError (Slots bound)}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM read = .ok groups)
    (failed : read index = .error cause) :
    readBoundWith bound read = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  rw [readBoundWith_reference, split, denote_prefix earlier]
  simp [Reader.denoteGroups, rowsAtWith, failed, Except.map, Except.mapError, List.map_map]

theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  readBoundWith_first_error (read := readGroup limits leafLimits bound) split earlier failed

theorem convertWith_first_error {inputLimits : Leaf.Events.ToIpc.Limits}
    {read : (bound : Bound) → Nat → Except GroupError (Slots bound)}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (read bound) = .ok groups)
    (failed : read bound index = .error cause) :
    convertWith inputLimits output input ordinal read = .error (.source (.groupFailure index cause)) := by
  have trace := readBoundWith_first_error split earlier failed
  simp [convertWith, opened, trace, emit, Except.mapError, Bind.bind, Except.bind]

theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  convertWith_first_error (read := readGroup limits inputLimits.leaf) opened split earlier failed

private theorem denote_complete {bound : Bound} {read : Nat → Except GroupError (Slots bound)}
    {indices : List Nat}
    (ended : (Reader.denoteGroups (rowsAtWith bound read) indices).2 = .eos) :
    ∃ groups, indices.mapM read = .ok groups ∧
      (Reader.denoteGroups (rowsAtWith bound read) indices).1 = groups.map (Leaf.Events.rows bound) := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index rest ih =>
    cases first : read index with
    | error => simp [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError] at ended
    | ok slots =>
      obtain ⟨groups, tailRead, exactRows⟩ := ih (by
        simpa [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError] using ended)
      refine ⟨slots :: groups, ?_, ?_⟩
      · simp [List.mapM_cons, first, tailRead, Bind.bind, Except.bind, pure, Except.pure]
      · simp [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError, exactRows]

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

theorem convertWith_readback {inputLimits : Leaf.Events.ToIpc.Limits}
    {read : (bound : Bound) → Nat → Except GroupError (Slots bound)}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convertWith inputLimits output input ordinal read = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (read bound) = .ok groups ∧
      readBoundWith bound (read bound) = .ok ⟨Leaf.Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) := by
  cases opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal with
  | error cause => simp [convertWith, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    let reference := Reader.denoteGroups (rowsAtWith bound (read bound)) (List.range bound.snapshot.groupCount)
    have events := readBoundWith_reference bound (read bound)
    change readBoundWith bound (read bound) = .ok ⟨Leaf.Events.schema bound,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ at events
    have directly : emit output (.ok ⟨Leaf.Events.schema bound,
        ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩) = .ok wire := by
      simpa [convertWith, opened, events, Except.mapError, Bind.bind, Except.bind] using written
    cases ended : reference.2 with
    | readError _ | closeError _ | closed => simp [emit, ended] at directly
    | eos =>
      obtain ⟨groups, decoded, rows⟩ := denote_complete ended
      change reference.1 = groups.map (Leaf.Events.rows bound) at rows
      have trace : readBoundWith bound (read bound) = .ok ⟨Leaf.Events.schema bound,
          ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ := by
        simpa [ended, rows, List.map_map] using events
      have width : (Leaf.Events.schema bound).width = 1 := rfl
      rw [ended, rows, List.map_map] at directly
      obtain ⟨result, read, binding, exactCounts⟩ := emit_readback width rfl directly
      refine ⟨bound, groups, rfl, decoded, trace, result, read, binding, exactCounts.trans ?_⟩
      exact batch_counts bound groups ⟨0, Nat.zero_lt_one⟩

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
          groups.map (List.map (Option.map Ticks.ticks)) :=
  convertWith_readback (read := readGroup limits inputLimits.leaf) written

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2
