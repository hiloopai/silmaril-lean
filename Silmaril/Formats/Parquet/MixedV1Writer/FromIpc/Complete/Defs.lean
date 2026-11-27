module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Defs

/-! Ordered native mixed IPC to Parquet with any admitted batch count. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete

open Silmaril.Formats.Relational.NamedTable

/-- The dispatch consumes the same checked observation in either case.
An empty record list writes a footer only. Each actual record, even one
with zero rows, becomes a row group. -/
def emitPrepared (sink : Multi.Limits) (observed : MixedIpc.Prepared) :
    Except Error Multi.Encoded :=
  match observed.batches with
  | [] => (SchemaOnly.emit sink observed.descriptor).mapError .sink
  | _ :: _ => emitOrderedPrepared sink observed

/-- Read the source once through exact EOS before invoking either writer.
Only a complete checked Parquet file is returned. -/
def convert (source : MixedIpc.Limits) (sink : Multi.Limits) (input : KBytes) :
    Except Error Multi.Encoded := do
  let observed ← (MixedIpc.read source input).mapError .source
  emitPrepared sink observed

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete
