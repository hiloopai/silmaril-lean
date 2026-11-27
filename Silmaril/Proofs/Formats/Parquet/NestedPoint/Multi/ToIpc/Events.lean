module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Thms
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.Wire

public section

namespace Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc
open Arrow.StructInt32 (Field)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readAll_reader {limits : SourceLimits} {bytes : Bytes} {checked : Checked}
    (opened : openFile limits bytes = .ok checked) :
    readAll limits bytes = Reader.readAll (.ok ⟨schema checked.field, groupSource limits.group checked⟩) := by
  rw [Reader.readAll_opened]
  simp [readAll, opened, Except.map, Except.mapError, trace]

theorem convert_trace (limits : Limits) (bytes : Bytes) :
    (convert limits bytes).trace = readAll limits.parquet bytes := by
  cases opened : openFile limits.parquet bytes <;> simp [convert, readAll, opened, Except.mapError, Except.map]

private theorem first_group_error {limits : NestedPoint.Multi.Limits} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List NestedPoint.Row)}
    {cause : NestedPoint.Multi.Error}
    (earlier : before.mapM (NestedPoint.Multi.read limits checked.snapshot) = .ok groups)
    (failed : NestedPoint.Multi.read limits checked.snapshot ordinal = .error cause) :
    Reader.denoteGroups (groupSource limits checked).readGroup (before ++ ordinal :: after) =
      (groups.map (rowsFor checked.field), .readError (.groupFailure ordinal cause)) := by
  induction before generalizing groups with
  | nil =>
    have empty : [] = groups := Except.ok.inj earlier
    subst groups
    simp [Reader.denoteGroups, groupSource, failed, Except.map, Except.mapError]
  | cons index rest ih =>
    rw [List.mapM_cons] at earlier
    cases original : NestedPoint.Multi.read limits checked.snapshot index with
    | error e => simp [original, Bind.bind, Except.bind] at earlier
    | ok rowGroup =>
      simp only [original, Bind.bind, Except.bind] at earlier
      cases tail : rest.mapM (NestedPoint.Multi.read limits checked.snapshot) with
      | error e => simp [tail] at earlier
      | ok restGroups =>
        rw [tail] at earlier
        obtain rfl := Except.ok.inj earlier
        simp only [List.cons_append, Reader.denoteGroups, groupSource, original, Except.mapError, Except.map]
        simpa only [groupSource, Except.map, Except.mapError, List.map_cons] using congrArg
          (fun pair => (rowsFor checked.field rowGroup :: pair.1, pair.2)) (ih tail)

theorem convert_first_error {limits : Limits} {bytes : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List NestedPoint.Row)}
    {cause : NestedPoint.Multi.Error}
    (opened : openFile limits.parquet bytes = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (NestedPoint.Multi.read limits.parquet.group checked.snapshot) = .ok groups)
    (failed : NestedPoint.Multi.read limits.parquet.group checked.snapshot ordinal = .error cause) :
    (convert limits bytes).trace = .ok ⟨schema checked.field,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor checked.field), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits bytes).wire = .error (.source (.groupFailure ordinal cause)) := by
  have retained : trace limits.parquet.group checked =
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor checked.field), .readError (.groupFailure ordinal cause)⟩ := by
    change (⟨(Reader.denoteGroups (groupSource limits.parquet.group checked).readGroup
      (List.range checked.snapshot.groupCount)).1.map AlignedColumns.ofRows,
      (Reader.denoteGroups (groupSource limits.parquet.group checked).readGroup
        (List.range checked.snapshot.groupCount)).2⟩ : Trace checked.field) = _
    rw [split, first_group_error earlier failed, List.map_map]
  simp [convert, opened, retained, writeTrace]

private theorem all_groups {limits : NestedPoint.Multi.Limits} {checked : Checked} {indices : List Nat}
    (ended : (Reader.denoteGroups (groupSource limits checked).readGroup indices).2 = .eos) :
    ∃ groups,
      indices.mapM (NestedPoint.Multi.read limits checked.snapshot) = .ok groups ∧
      List.Forall₂ (GroupWire limits checked.snapshot) indices groups ∧
      (Reader.denoteGroups (groupSource limits checked).readGroup indices).1 =
        groups.map (rowsFor checked.field) := by
  induction indices with
  | nil => exact ⟨[], rfl, .nil, rfl⟩
  | cons ordinal rest ih =>
    rw [Reader.denoteGroups] at ended
    cases group : NestedPoint.Multi.read limits checked.snapshot ordinal with
    | error e => simp [groupSource, group, Except.map, Except.mapError] at ended
    | ok slots =>
      have tail : (Reader.denoteGroups (groupSource limits checked).readGroup rest).2 = .eos := by
        simpa [groupSource, group, Except.map, Except.mapError] using ended
      obtain ⟨groups, reads, original, observed⟩ := ih tail
      refine ⟨slots :: groups, ?_, .cons (readGroup_wire group) original, ?_⟩
      · simp [List.mapM_cons, group, reads, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · rw [Reader.denoteGroups]
        simp [groupSource, group, Except.map, Except.mapError] at observed ⊢
        exact observed

theorem nativeBatches_of_groups (field : Field) (groups : List (List NestedPoint.Row))
    (outcome : Arrow.Events.Termination SourceError) :
    nativeBatches (field := field) ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor field), outcome⟩ =
      groups.map (List.map nativeRow) := by
  simp [nativeBatches, rowsFor, AlignedColumns.ofRows, List.map_map, Function.comp_def]

theorem convert_readback {limits : Limits} {bytes : Bytes} {wire : KBytes}
    (written : (convert limits bytes).wire = .ok wire) : Readback limits bytes wire := by
  cases opened : openFile limits.parquet bytes with
  | error e => simp [convert, opened] at written
  | ok checked =>
    have emitted : writeTrace limits.ipc checked.field (trace limits.parquet.group checked) = .ok wire := by
      simpa [convert, opened] using written
    have ended : (trace limits.parquet.group checked).termination = .eos := by
      cases status : (trace limits.parquet.group checked).termination <;>
        simp_all [writeTrace]
    have denoted :
        (Reader.denoteGroups (groupSource limits.parquet.group checked).readGroup
          (List.range checked.snapshot.groupCount)).2 = .eos := ended
    obtain ⟨groups, reads, original, observed⟩ := all_groups denoted
    have complete : trace limits.parquet.group checked =
        ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor checked.field), .eos⟩ := by
      unfold trace
      simp only [groupSource] at observed denoted ⊢
      rw [observed, denoted, List.map_map]
    rw [complete, writeTrace, nativeBatches_of_groups] at emitted
    obtain ⟨native, start, read, agrees, wf, envelope, fields, batches⟩ :=
      Arrow.StructInt32.Stream.Writer.emitFor_readback (width := .int64) (mapError_ok emitted)
    exact ⟨checked, groups, native, start, opened, openFile_wire opened, reads, original,
      by simp [convert, opened, complete], read, agrees, wf, envelope, fields, batches⟩

end Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc
