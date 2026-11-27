module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Correctness

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
open Arrow.MixedFlat

/-- Prepared writer columns retain the exact nullable cells and explicit row count. -/
theorem prepare_observe {table : Rows.Table} {batch : OrderedWriter.BatchInput}
    (prepared : prepare table = .ok batch) :
    observeSourceBatch batch.observe = some (Rows.observeColumns (AlignedColumns.ofRows table.rows)) :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.prepare_observe prepared

/-- The opted-in writer reads back the single prepared batch through exact EOS. -/
theorem emitted_table {limits : Arrow.MixedFlat.Limits} {table : Rows.Table} {batch : OrderedWriter.BatchInput}
    {wire : KBytes} (prepared : prepare table = .ok batch)
    (written : OrderedWriter.emitWith limits (fields table.schema) [batch]
      (fun signature => signature.all MixedIpc.supported) = .ok wire) :
    readEvents limits wire = some ⟨fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ ∧
      Rows.readRows limits wire = some table :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.emitted_table prepared written

/-- Successful conversion recovers the exact imported dependent table
under its declared schema and the single-batch policy. -/
theorem convert_readback {csv : MixedIpc.Limits} {ipc : Arrow.MixedFlat.Limits}
    {schema : Rows.Schema} {input : Csv.Bytes} {wire : KBytes}
    (converted : convert csv ipc schema input = .ok wire) :
    ∃ table, MixedIpc.decode csv schema input = .ok table ∧ table.schema = schema ∧
      readEvents ipc wire = some ⟨fields schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ ∧
      Rows.readRows ipc wire = some table :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.convert_readback converted

/-- Successful CSV export and native conversion recover the exact initial Scan table. -/
theorem encoded_readback {csv : MixedIpc.Limits} {ipc : Arrow.MixedFlat.Limits}
    {table : Rows.Table} {input : Csv.Bytes} {wire : KBytes}
    (encoded : MixedIpc.encode csv table = .ok input)
    (converted : convert csv ipc table.schema input = .ok wire) :
    Rows.readRows ipc wire = some table :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.encoded_readback encoded converted

/-- The checked source refusal propagates before any writer call. -/
theorem convert_source_error {csv : MixedIpc.Limits} {ipc : Arrow.MixedFlat.Limits}
    {schema : Rows.Schema} {input : Csv.Bytes} {cause : MixedIpc.Error}
    (refused : MixedIpc.decode csv schema input = .error cause) :
    convert csv ipc schema input = .error (.source cause) := by
  simp [convert, refused, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc
