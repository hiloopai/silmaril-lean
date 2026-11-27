module

public import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile
open Silmaril.Formats.Parquet.ListFile.Multi
open Silmaril.Formats.Parquet.ListFile.Multi.ToIpc
open Silmaril.Relational
open Arrow.ListInt32.Stream.Writer (emit_readback)

public theorem convert_trace (limits : ToIpc.Limits) (source : Bytes) :
    (convert limits source).trace = Multi.readAll limits.parquet source := by
  cases opened : ListFile.openFile limits.parquet.file source <;>
    simp [convert, Multi.readAll, Multi.openSource, opened, Except.map, Except.mapError, Reader.readAll]

private theorem convert_wire_of_open {limits : ToIpc.Limits} {source : Bytes} {checked : ListFile.Checked}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked) :
    (convert limits source).wire =
      writeTrace limits.ipc (fieldOf checked).childName (Multi.readAll limits.parquet source) := by
  rw [← convert_trace]
  simp [convert, opened]

public theorem convert_open_error {limits : ToIpc.Limits} {source : Bytes} {cause : ListFile.OpenError}
    (failed : ListFile.openFile limits.parquet.file source = .error cause) :
    (convert limits source).trace = .error (.openFailure cause) ∧
    (convert limits source).wire = .error (.source (.openFailure cause)) := by
  simp [convert, failed]

public theorem convert_first_error {limits : ToIpc.Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal : Nat}
    {groups : List (Reader.RowGroup (ListFile.schema checked) ListFile.Cell)}
    {cause : Multi.GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (Multi.groupSource limits.parquet checked).readGroup = .ok groups)
    (failed : Multi.readGroup limits.parquet.maxGroupSlots checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map AlignedColumns.ofRows, .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) := by
  have original := Multi.readAll_first_error opened split earlier failed
  exact ⟨(convert_trace limits source).trans original, by
    rw [convert_wire_of_open opened, original]
    rfl⟩

private theorem all_groups {limits : Multi.Limits} {checked : ListFile.Checked} {indices : List Nat}
    (ended : (Reader.denoteGroups (Multi.groupSource limits checked).readGroup indices).2 = .eos) :
    ∃ groups,
      indices.mapM (Multi.readGroup limits.maxGroupSlots checked) = .ok groups ∧
      List.Forall₂ (Multi.GroupWire limits.maxGroupSlots checked) indices groups ∧
      (Reader.denoteGroups (Multi.groupSource limits checked).readGroup indices).1 =
        groups.map (ListFile.rows checked) := by
  induction indices with
  | nil => exact ⟨[], rfl, .nil, rfl⟩
  | cons ordinal rest ih =>
    rw [Reader.denoteGroups] at ended
    cases group : Multi.readGroup limits.maxGroupSlots checked ordinal with
    | error e => simp [Multi.groupSource, group, Except.map, Except.mapError] at ended
    | ok slots =>
      have tail : (Reader.denoteGroups (Multi.groupSource limits checked).readGroup rest).2 = .eos := by
        simpa [Multi.groupSource, group, Except.map, Except.mapError] using ended
      obtain ⟨groups, reads, original, trace⟩ := ih tail
      refine ⟨slots :: groups, ?_, .cons (Multi.readGroup_wire group) original, ?_⟩
      · simp [List.mapM_cons, group, reads, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · rw [Reader.denoteGroups]
        simp [Multi.groupSource, group, Except.map, Except.mapError] at trace ⊢
        exact trace

private theorem writeTrace_exact (limits : Arrow.ListInt32.Stream.Limits) (checked : ListFile.Checked)
    (groups : List (List ListPage.Row)) :
    writeTrace limits (fieldOf checked).childName
      (.ok ⟨ListFile.schema checked, ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .eos⟩⟩) =
      (Arrow.ListInt32.Stream.Writer.emit limits (fieldOf checked) groups).mapError .writer := by
  obtain ⟨width, name⟩ := ListFile.schema_exact checked
  let column := Fin.cast width.symm (0 : Fin 1)
  have projected :
      (groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked)).map (·.values column) = groups := by
    induction groups with
    | nil => rfl
    | cons slots rest ih =>
      simp [ListFile.batch_slots checked slots column, ih]
  unfold writeTrace
  simp only [Except.mapError, Bind.bind, Except.bind]
  rw [dite_eq_left width]
  change (Arrow.ListInt32.Stream.Writer.emit limits
    ⟨((ListFile.schema checked).kind column).1, (fieldOf checked).childName⟩
    ((groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked)).map (·.values column))).mapError _ = _
  rw [name column, projected]
  rfl

public theorem convert_readback {limits : ToIpc.Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire := by
  cases opened : ListFile.openFile limits.parquet.file source with
  | error e => rw [(convert_open_error opened).2] at h; contradiction
  | ok checked =>
    rw [convert_wire_of_open opened, Multi.readAll_reference opened] at h
    let reference := Reader.denoteGroups (Multi.groupSource limits.parquet checked).readGroup
      (List.range checked.snapshot.groupCount)
    change writeTrace limits.ipc (fieldOf checked).childName
      (.ok ⟨ListFile.schema checked, ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩) = .ok wire at h
    have ended : reference.2 = .eos := by
      cases outcome : reference.2 <;> simp_all [writeTrace, Except.mapError, Bind.bind, Except.bind]
    obtain ⟨groups, reads, original, ordered⟩ := all_groups ended
    have trace : (convert limits source).trace = .ok ⟨ListFile.schema checked,
        ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .eos⟩⟩ := by
      rw [convert_trace, Multi.readAll_reference opened]
      change (Except.ok ⟨ListFile.schema checked, ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ : SourceTrace) = _
      rw [ended, ordered, List.map_map]
    rw [ended, ordered, List.map_map, writeTrace_exact] at h
    have written : Arrow.ListInt32.Stream.Writer.emit limits.ipc (fieldOf checked) groups = .ok wire := by
      cases ipc : Arrow.ListInt32.Stream.Writer.emit limits.ipc (fieldOf checked) groups <;>
        simp_all [Except.mapError]
    obtain ⟨decoded, size, nativeRead, agrees, wf, envelope, schema, batches⟩ := emit_readback written
    exact ⟨checked, groups, decoded, size, opened, ListFile.openFile_wire opened,
      reads, original, trace, nativeRead, agrees, wf,
      envelope, schema, batches⟩

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.ToIpc
