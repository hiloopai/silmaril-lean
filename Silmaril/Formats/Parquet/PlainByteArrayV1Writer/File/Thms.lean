module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs
import Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Correctness

public section

namespace Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File

variable {limits : Limits} {input : Input} {output : Encoded}

theorem Input.ofSlots_exact {name : String} {layout : FlatColumn.Layout} {slots : List (Option Bytes)}
    (prepared : ofSlots name layout slots = some input) :
    input.name = name ∧ input.layout = layout ∧ input.page.slots = slots :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.ofSlots_exact prepared

/-- The file consists of the original bounded V1 page at byte four,
the serialized Compact footer, its exact length word, and both magic markers. -/
theorem emit_wire (written : emit limits input = .ok output) :
    ∃ footer : Bytes, PlainByteArrayV1Writer.emit (pageLimits limits) input.page = .ok output.page ∧
      serializeFooter input limits output.pageSpan = .ok footer ∧
      output.footer = ⟨output.pageSpan.stop, output.pageSpan.stop + footer.length⟩ ∧
      output.bytes = (((Footer.magic.append output.page.wire).append footer).append
        (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.emit_wire written

/-- The exact singleton footer binds the original name and nullability to
column zero. Indexed readback of group zero recovers all nullable octets,
with the existing selected reader's wire witness. -/
theorem emit_readback (written : emit limits input = .ok output) :
    output.bytes.length ≤ limits.maxFileBytes ∧
    Footer.readFooter limits.snapshot.footer output.bytes = .ok (output.footer, metadata input output) ∧
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits output.bytes input.name input.layout = .ok checked ∧
      checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = 1 ∧
      checked.readGroup limits 0 = .ok input.page.slots ∧
      Plain.ByteArray.File.GroupWire checked limits 0 (rowGroup input output) input.page.slots :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.emit_readback written

/-- Checked emission recovers the original arguments of the slot adapter. -/
theorem emit_ofSlots_readback {name : String} {layout : FlatColumn.Layout} {slots : List (Option Bytes)}
    (prepared : Input.ofSlots name layout slots = some input) (written : emit limits input = .ok output) :
    Footer.readFooter limits.snapshot.footer output.bytes = .ok (output.footer, metadata input output) ∧
    ∃ checked : Plain.ByteArray.File.Checked name layout,
      Plain.ByteArray.File.openFile limits output.bytes name layout = .ok checked ∧
      checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = 1 ∧
      checked.readGroup limits 0 = .ok slots :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.emit_ofSlots_readback prepared written

/-- Assembly failures retain their typed cause before readback. -/
theorem emit_assembly_error {cause : Error} (failed : assemble limits input = .error cause) :
    emit limits input = .error cause := by
  simp [emit, failed, Bind.bind, Except.bind]

/-- After the footer matches, an indexed rejection retains the reader's cause. -/
theorem emit_group_error {checked : Plain.ByteArray.File.Checked input.name input.layout}
    {cause : FlatColumn.Error Plain.ByteArray.File.PageError}
    (assembled : assemble limits input = .ok output)
    (opened : Plain.ByteArray.File.openFile limits output.bytes input.name input.layout = .ok checked)
    (footer : checked.snapshot.footer = output.footer)
    (shape : checked.snapshot.metadata = metadata input output)
    (failed : checked.readGroup limits 0 = .error cause) :
    emit limits input = .error (.groupReadback cause) := by
  simp [emit, assembled, opened, footer, shape, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File
