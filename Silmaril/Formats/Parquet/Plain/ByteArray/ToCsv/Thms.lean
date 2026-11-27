module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToCsv.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv

open Silmaril.Relational Csv.Typed.Utf8

variable {parquet : File.Limits} {source sink : OpaqueIpc.IpcLimits}
variable {exportLimits importLimits : OpaqueIpc.CsvLimits}
variable {input : Bytes} {name : String} {layout : FlatColumn.Layout}

/-- Successful CSV recovers exactly the selected field and ordered nullable
octets read from the original footer groups. -/
theorem exportCsv_readback {output : OpaqueIpc.Output}
    (exported : exportCsv parquet source exportLimits input name layout = .ok output) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      output.field = descriptor name layout ∧
      OpaqueIpc.decode exportLimits output.field output.wire = .ok (groups.flatten.map (Option.map Bytes.toList)) :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToCsv.exportCsv_readback exported

/-- The checked CSV import and final native read agree with the exact field
and nullable octets of the original checked Parquet groups. The final stream
has one batch through exact EOS, even if the original file has zero groups. -/
theorem convert_readback {output : Output}
    (converted : convert parquet source sink exportLimits importLimits input name layout = .ok output) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      output.csv.field = descriptor name layout ∧
      OpaqueIpc.decode importLimits output.csv.field output.csv.wire =
        .ok (groups.flatten.map (Option.map Bytes.toList)) ∧
      OpaqueIpc.readIpc sink .binaryView output.ipc =
        .ok ⟨descriptor name layout, [groups.flatten.map (Option.map Bytes.toList)]⟩ :=
  Proofs.Formats.Parquet.Plain.ByteArray.ToCsv.convert_readback converted

/-- Preserve a source or intermediate native writer error before either CSV stage. -/
theorem convert_parquet_error {cause : ToIpc.Error}
    (failed : ToIpc.convert parquet source.ipc source.view input name layout = .error cause) :
    convert parquet source sink exportLimits importLimits input name layout = .error (.parquetToIpc cause) := by
  simp [convert, exportCsv, failed, Except.mapError, Bind.bind, Except.bind]

theorem convert_open_error {cause : File.Error}
    (failed : File.openFile parquet input name layout = .error cause) :
    convert parquet source sink exportLimits importLimits input name layout =
      .error (.parquetToIpc (.source (.openError cause))) :=
  convert_parquet_error (ToIpc.convert_open_error failed)

/-- A first indexed source failure produces no conversion result. The
separate Parquet trace retains the preceding complete groups. -/
theorem convert_first_error {checked : File.Checked name layout} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error File.PageError}
    (opened : File.openFile parquet input name layout = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup parquet) = .ok groups)
    (failed : checked.readGroup parquet index = .error cause) :
    convert parquet source sink exportLimits importLimits input name layout =
      .error (.parquetToIpc (.source (.readError cause))) ∧
    File.readAll parquet input name layout = .ok
      ⟨File.schema name layout,
        ⟨groups.map (AlignedColumns.ofRows ∘ File.rows name layout), .readError (.column cause)⟩⟩ := by
  obtain ⟨error, trace⟩ := ToIpc.convert_first_error opened indices earlier failed
  exact ⟨convert_parquet_error error, trace⟩

theorem convert_toCsv_error {wire : KBytes} {cause : OpaqueIpc.ToCsvError}
    (emitted : ToIpc.convert parquet source.ipc source.view input name layout = .ok wire)
    (failed : OpaqueIpc.toCsv source exportLimits .binaryView wire = .error cause) :
    convert parquet source sink exportLimits importLimits input name layout = .error (.toCsv cause) := by
  simp [convert, exportCsv, emitted, failed, Except.mapError, Bind.bind, Except.bind]

theorem convert_fromCsv_error {csv : OpaqueIpc.Output} {cause : OpaqueIpc.FromCsvError}
    (exported : exportCsv parquet source exportLimits input name layout = .ok csv)
    (failed : OpaqueIpc.fromCsv importLimits sink csv.field csv.wire = .error cause) :
    convert parquet source sink exportLimits importLimits input name layout = .error (.fromCsv cause) := by
  simp [convert, exported, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv
