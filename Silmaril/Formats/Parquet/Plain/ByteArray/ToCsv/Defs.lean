module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Defs

/-! One selected uncompressed PLAIN BYTE_ARRAY leaf through native BinaryView
IPC and the checked opaque typed CSV profile. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv

open Csv.Typed.Utf8

def descriptor (name : String) (layout : FlatColumn.Layout) : OpaqueIpc.Descriptor :=
  ⟨name, decide (layout = .optional), .binaryView⟩

inductive Error where
  | parquetToIpc (cause : ToIpc.Error)
  | toCsv (cause : OpaqueIpc.ToCsvError)
  | fromCsv (cause : OpaqueIpc.FromCsvError)
  deriving DecidableEq, Repr

structure Output where
  csv : OpaqueIpc.Output
  ipc : KBytes

/-- Use the checked selected-column converter, then read its complete
BinaryView wire into the bounded hex CSV profile. -/
def exportCsv (parquet : File.Limits) (source : OpaqueIpc.IpcLimits) (limits : OpaqueIpc.CsvLimits)
    (input : Bytes) (name : String) (layout : FlatColumn.Layout) : Except Error OpaqueIpc.Output := do
  let wire ← (ToIpc.convert parquet source.ipc source.view input name layout).mapError .parquetToIpc
  (OpaqueIpc.toCsv source limits .binaryView wire).mapError .toCsv

/-- Return the CSV and final native IPC together after both CSV stages
succeed. The final carrier has one batch of the flattened footer groups. -/
def convert (parquet : File.Limits) (source sink : OpaqueIpc.IpcLimits)
    (exportLimits importLimits : OpaqueIpc.CsvLimits) (input : Bytes) (name : String)
    (layout : FlatColumn.Layout) : Except Error Output := do
  let csv ← exportCsv parquet source exportLimits input name layout
  let wire ← (OpaqueIpc.fromCsv importLimits sink csv.field csv.wire).mapError .fromCsv
  return ⟨csv, wire⟩

end Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv
