module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs

/-! Native recursive Arrow V5 IPC for checked non-repeated Parquet rows. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc

@[expose] public section

inductive Error where
  | source (original : Rows.Error)
  | writer (original : Arrow.RecursiveSchema.Stream.Writer.Error)
  deriving DecidableEq, Repr

/-- Complete every original row group before admitting native output. -/
def convert {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (ipc : Arrow.RecursiveSchema.Batch.Limits)
    (schema : Compiled schemaLimits snapshot) : Except Error KBytes := do
  let groups ← (Rows.readAll limits schema).mapError .source
  (Arrow.RecursiveSchema.Stream.Writer.emit ipc schema.arrow groups).mapError .writer

end

end Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc
