module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.Defs
import Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.Correctness

public section

namespace Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups

variable {limits : Limits} {input : Input} {output : Encoded}

/-- The original group ordinals and one-page windows partition the data
area from the leading magic to the exact checked footer. -/
theorem emit_checked (written : emit limits input = .ok output) :
    input.groups.length ≤ limits.groupLimit ∧ input.totalRows ≤ limits.rowLimit ∧
      output.Checked limits input ∧ certify limits input output = .ok () :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.emit_checked written

theorem emit_bounds (written : emit limits input = .ok output) :
    input.groups.length ≤ limits.maxGroups ∧
    input.groups.length ≤ limits.file.snapshot.footer.compact.maxCollectionSize ∧
    input.totalRows ≤ limits.file.maxFileRows ∧ input.totalRows < 2^63 ∧
    output.bytes.length ≤ limits.file.maxFileBytes ∧ output.bytes.length < 2^63 :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.emit_bounds written

/-- The original nullable slots and native group witness survive at each
ordinal. The footer is the exact parsed metadata of the output file. -/
theorem emit_indexed (written : emit limits input = .ok output) :
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits.file output.bytes input.name input.layout = .ok checked ∧
      Footer.readFooter limits.file.snapshot.footer output.bytes = .ok (output.footer, metadata input output) ∧
      checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        checked.readGroup limits.file i.val = .ok (input.groups.get i) ∧
        ∃ group, (metadata input output).rowGroups[i.val]? = some group ∧
          Plain.ByteArray.File.GroupWire checked limits.file i.val group (input.groups.get i) :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.emit_indexed written

/-- A group carries its original framed page in the exact footer-declared
window, with an exclusive stop in the signed file-offset range. -/
theorem emit_group_extent (written : emit limits input = .ok output) {group : Group}
    (member : group ∈ output.groups) :
    group.Wire input limits output.bytes output.footer.start ∧
      (group.span.start : Int) = (group.chunk input).metadata.dataPageOffset ∧
      (group.span.stop : Int) = (group.chunk input).metadata.dataPageOffset +
        (group.chunk input).metadata.totalCompressedSize ∧
      4 ≤ group.span.start ∧ group.span.start < group.span.stop ∧
      group.span.stop ≤ output.footer.start ∧ group.span.stop < 2^63 :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.emit_group_extent written member

/-- Each original ordinal has the same row count and native group extent in
the exact parsed footer. -/
theorem emit_footer_groups (written : emit limits input = .ok output) :
    (metadata input output).numRows = input.totalRows ∧
    ∀ i : Fin input.groups.length, ∃ group,
      output.groups[i.val]? = some group ∧
      (metadata input output).rowGroups[i.val]? = some (group.rowGroup input) ∧
      group.rows = (input.groups.get i).length ∧
      group.Wire input limits output.bytes output.footer.start :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.emit_footer_groups written

/-- A schema-only file places its footer immediately after the leading
magic and carries zero footer groups. -/
theorem emit_schema_only (written : emit limits input = .ok output) (empty : input.groups = []) :
    output.groups = [] ∧ output.footer.start = 4 ∧ (metadata input output).rowGroups = [] := by
  have ⟨_, rows, layout, _⟩ := (emit_checked written).2.2.1
  rw [empty] at rows
  have noGroups := List.map_eq_nil_iff.mp rows
  have footer : 4 = output.footer.start := by simpa [noGroups, Contiguous] using layout
  exact ⟨noGroups, footer.symm, by simp [metadata, noGroups]⟩

/-- An explicit empty group remains at its original ordinal as a checked
zero-row group. -/
theorem emit_empty_at (written : emit limits input = .ok output) (i : Fin input.groups.length)
    (empty : input.groups.get i = []) :
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits.file output.bytes input.name input.layout = .ok checked ∧
      checked.snapshot.groupCount = input.groups.length ∧ checked.readGroup limits.file i.val = .ok [] := by
  obtain ⟨checked, opened, _, _, count, indexed⟩ := emit_indexed written
  refine ⟨checked, opened, count, (indexed i).1.trans ?_⟩
  exact congrArg Except.ok empty

end Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups
