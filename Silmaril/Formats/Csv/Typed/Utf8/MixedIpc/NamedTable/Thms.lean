module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Thms
public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Thms
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.Correctness

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable

open Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

/-- Only a complete, exact-schema decode can insert at a vacant name. -/
theorem importCsv_ok_iff {Name : Type*} [DecidableEq Name] {db next : Database Name}
    {name : Name} {expected declared : Rows.Schema} {limits : Limits} {input : Csv.Bytes} :
    importCsv db name expected declared limits input = .ok next ↔
      db name = none ∧ declared = expected ∧ ∃ rows : Scan.Table expected (fun _ => Cell),
        decode limits declared input = .ok ⟨expected, rows⟩ ∧
        next = Function.update db name (some ⟨expected, rows⟩) :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.importCsv_ok_iff

/-- Success exports the original named table under its exact descriptor. -/
theorem exportCsv_ok_iff {Name : Type*} {db : Database Name} {name : Name}
    {expected : Rows.Schema} {limits : Limits} {output : Output} :
    exportCsv db name expected limits = .ok output ↔
      ∃ rows : Scan.Table expected (fun _ => Cell),
        Scan.observePacked db name = some ⟨expected, rows⟩ ∧
        output.schema = expected ∧ encode limits ⟨expected, rows⟩ = .ok output.wire :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.exportCsv_ok_iff

/-- Transfer the exact observed table to a vacant destination using the same
CSV limits for export and import. The update preserves every other name. -/
theorem import_exportCsv {Name : Type*} [DecidableEq Name] {source dest : Database Name}
    {sourceName destName : Name} {expected : Rows.Schema} {limits : Limits} {output : Output}
    (written : exportCsv source sourceName expected limits = .ok output)
    (vacant : dest destName = none) :
    ∃ rows : Scan.Table expected (fun _ => Cell),
      Scan.observePacked source sourceName = some ⟨expected, rows⟩ ∧
      importCsv dest destName expected output.schema limits output.wire =
        .ok (Function.update dest destName (some ⟨expected, rows⟩)) := by
  obtain ⟨rows, found, rfl, encoded⟩ := exportCsv_ok_iff.mp written
  exact ⟨rows, found, importCsv_ok_iff.mpr ⟨vacant, rfl, rows, decode_encode encoded, rfl⟩⟩

/-- Successful IPC conversion, named import, named export and IPC emission
observe the same ordered table under independent limits. The returned stream
has one batch through exact EOS. The table retains rows at zero width. -/
theorem ipc_roundtrip {Name : Type*} [DecidableEq Name] {db next : Database Name}
    {name : Name} {expected : Rows.Schema} {source sink : Arrow.MixedFlat.Limits}
    {sourceCsv importLimits exportLimits sinkCsv : Limits} {input output : KBytes} {csv exported : Output}
    (converted : convert source sourceCsv input = .ok csv)
    (inserted : importCsv db name expected csv.schema importLimits csv.wire = .ok next)
    (written : exportCsv next name expected exportLimits = .ok exported)
    (emitted : ToIpc.convert sinkCsv sink exported.schema exported.wire = .ok output) :
    ∃ table, Rows.readRows source input = some table ∧
      Scan.observePacked next name = some table ∧ csv.schema = table.schema ∧
      exported.schema = table.schema ∧ Rows.readRows sink output = some table ∧
      readEvents sink output = some
        ⟨ToIpc.fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.ipc_roundtrip converted inserted written emitted

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable
