module

public import Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.FromCsv.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv

open Csv.Typed.Utf8

/-- Recover the declared leaf and its exact footer and the CSV's ordered
nullable octets from group zero of the one-group file. -/
theorem convert_readback {csv : OpaqueIpc.CsvLimits} {limits : PlainByteArrayV1Writer.File.Limits}
    {field : OpaqueIpc.Descriptor} {input : Csv.Bytes} {output : PlainByteArrayV1Writer.File.Encoded}
    (converted : convert csv limits field input = .ok output) :
    ∃ (values : OpaqueIpc.Slots) (prepared : PlainByteArrayV1Writer.File.Input), field.layout = .binaryView ∧
      OpaqueIpc.decode csv field input = .ok values ∧
      prepared.name = field.name ∧ prepared.layout = layout field.nullable ∧
      prepared.page.slots = values.map (Option.map Bytes.ofList) ∧
      Footer.readFooter limits.snapshot.footer output.bytes =
        .ok (output.footer, PlainByteArrayV1Writer.File.metadata prepared output) ∧
      ∃ checked : File.Checked field.name (layout field.nullable),
        File.openFile limits output.bytes field.name (layout field.nullable) = .ok checked ∧
        checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = 1 ∧
        checked.readGroup limits 0 = .ok (values.map (Option.map Bytes.ofList)) :=
  Proofs.Formats.Parquet.Plain.ByteArray.FromCsv.convert_readback converted

/-- On successful export and import under independent limits, the new file's
single group holds the exact nullable slots of the original selected groups
flattened in footer order. -/
theorem roundtrip {source sink : File.Limits} {ipc : OpaqueIpc.IpcLimits}
    {exportLimits importLimits : OpaqueIpc.CsvLimits} {input : Bytes} {name : String}
    {selection : FlatColumn.Layout} {csv : OpaqueIpc.Output} {output : PlainByteArrayV1Writer.File.Encoded}
    (exported : ToCsv.exportCsv source ipc exportLimits input name selection = .ok csv)
    (converted : convert importLimits sink csv.field csv.wire = .ok output) :
    ∃ (original returned : File.Checked name selection) (groups : List (List (Option Bytes))),
      File.openFile source input name selection = .ok original ∧
      (List.range original.snapshot.groupCount).mapM (original.readGroup source) = .ok groups ∧
      File.openFile sink output.bytes name selection = .ok returned ∧
      returned.binding.columnOrdinal = 0 ∧ returned.snapshot.groupCount = 1 ∧
      returned.readGroup sink 0 = .ok groups.flatten :=
  Proofs.Formats.Parquet.Plain.ByteArray.FromCsv.roundtrip exported converted

/-- The CSV failure precedes preparation and every writer check. -/
theorem convert_csv_error {csv : OpaqueIpc.CsvLimits} {limits : PlainByteArrayV1Writer.File.Limits}
    {field : OpaqueIpc.Descriptor} {input : Csv.Bytes} {cause : OpaqueIpc.CsvError}
    (profile : field.layout = .binaryView) (failed : OpaqueIpc.decode csv field input = .error cause) :
    convert csv limits field input = .error (.csv cause) := by
  simp [convert, profile, failed, Except.mapError, Bind.bind, Except.bind]

/-- After successful CSV admission and preparation, the original writer
error is returned at the writer stage. -/
theorem convert_writer_error {csv : OpaqueIpc.CsvLimits} {limits : PlainByteArrayV1Writer.File.Limits}
    {field : OpaqueIpc.Descriptor} {input : Csv.Bytes} {values : OpaqueIpc.Slots}
    {prepared : PlainByteArrayV1Writer.File.Input} {cause : PlainByteArrayV1Writer.File.Error}
    (profile : field.layout = .binaryView) (parsed : OpaqueIpc.decode csv field input = .ok values)
    (packed : prepare field values = some prepared)
    (failed : PlainByteArrayV1Writer.File.emit limits prepared = .error cause) :
    convert csv limits field input = .error (.writer cause) := by
  simp [convert, profile, parsed, packed, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv
