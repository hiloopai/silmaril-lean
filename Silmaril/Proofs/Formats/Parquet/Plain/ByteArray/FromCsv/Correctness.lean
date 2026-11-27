module

public import Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs
import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Thms
import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.FromCsv

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv
open Silmaril.Formats.Csv.Typed.Utf8

private theorem convert_steps {csv : OpaqueIpc.CsvLimits} {limits : PlainByteArrayV1Writer.File.Limits}
    {field : OpaqueIpc.Descriptor} {input : Csv.Bytes} {output : PlainByteArrayV1Writer.File.Encoded}
    (converted : convert csv limits field input = .ok output) :
    field.layout = .binaryView ∧ ∃ values prepared, OpaqueIpc.decode csv field input = .ok values ∧
      prepare field values = some prepared ∧ PlainByteArrayV1Writer.File.emit limits prepared = .ok output := by
  by_cases profile : field.layout = .binaryView
  · cases parsed : OpaqueIpc.decode csv field input with
    | error cause => simp [convert, profile, parsed, Except.mapError, Bind.bind, Except.bind] at converted
    | ok values =>
      cases prepared : prepare field values with
      | none =>
        simp [convert, profile, parsed, prepared, Except.mapError, Bind.bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at converted
      | some packed =>
        refine ⟨profile, values, packed, rfl, prepared, ?_⟩
        cases written : PlainByteArrayV1Writer.File.emit limits packed <;>
          simp_all [convert, Except.mapError, Bind.bind, Except.bind]
  · simp [convert, profile, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at converted

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
        checked.readGroup limits 0 = .ok (values.map (Option.map Bytes.ofList)) := by
  obtain ⟨profile, values, prepared, parsed, packed, written⟩ := convert_steps converted
  have admitted : PlainByteArrayV1Writer.File.Input.ofSlots field.name (layout field.nullable)
      (values.map (Option.map Bytes.ofList)) = some prepared := packed
  obtain ⟨name, shape, slots⟩ := PlainByteArrayV1Writer.File.Input.ofSlots_exact admitted
  exact ⟨values, prepared, profile, parsed, name, shape, slots,
    PlainByteArrayV1Writer.File.emit_ofSlots_readback admitted written⟩

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
      returned.readGroup sink 0 = .ok groups.flatten := by
  obtain ⟨original, groups, opened, readGroups, field, decoded⟩ := ToCsv.exportCsv_readback exported
  obtain ⟨values, _, _, parsed, _, _, _, _, readback⟩ := convert_readback converted
  have exactValues := OpaqueIpc.decode_agrees parsed decoded
  subst values
  rw [field] at readback
  obtain ⟨returned, reopened, ordinal, count, read⟩ :
      ∃ checked : File.Checked name selection,
        File.openFile sink output.bytes name selection = .ok checked ∧
        checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = 1 ∧
        checked.readGroup sink 0 = .ok groups.flatten := by
    cases selection <;>
      simpa [ToCsv.descriptor, layout, List.map_map, Option.map_map, Function.comp_def] using readback
  exact ⟨original, returned, groups, opened, readGroups, reopened, ordinal, count, read⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.FromCsv
