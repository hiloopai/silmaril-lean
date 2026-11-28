module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs

/-! Native V5 IPC for the checked two-LIST groups and their top-level
projections. Complete the original source reads before admitting output. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc

open Arrow.RecursiveSchema (Schema)
open Arrow.RecursiveSchema.Batch.Rows (Observation)

@[expose] public section

inductive Error where
  | source (original : Events.Error)
  | writer (original : Arrow.RecursiveSchema.Stream.Writer.Error)
  deriving DecidableEq, Repr

def selectSchema (selection : Events.Selection) (schema : Schema) : Schema :=
  match selection with
  | .field => schema
  | .empty => ⟨[]⟩

def selectBatch (selection : Events.Selection) (batch : Observation) : Observation :=
  match selection with
  | .field => batch
  | .empty => ⟨batch.rowCount, List.replicate batch.rowCount []⟩

/-- Read whole groups in order, attaching the same ordinal and cause as
direct Events. Any error prevents the entire output from being written. -/
def readGroups {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (ordinals : List Nat) :
    Except Events.Error (List Observation) :=
  ordinals.mapM fun ordinal => (Rows.readGroup limits schema ordinal).mapError (.group ordinal)

def convertSource {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (ipc : Arrow.RecursiveSchema.Batch.Limits)
    (schema : Compiled schemaLimits snapshot) (selection : Events.Selection := .field) :
    Except Error KBytes := do
  let groups ← (readGroups limits schema (List.range snapshot.groupCount)).mapError .source
  (Arrow.RecursiveSchema.Stream.Writer.emit ipc (selectSchema selection (Rows.arrowSchema schema.plan))
    (groups.map (selectBatch selection))).mapError .writer

def convert (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (input : Bytes)
    (selection : Events.Selection := .field) : Except Error KBytes := do
  let source ← (TwoList.openFile schemaLimits input).mapError (.source ∘ .openError)
  convertSource limits ipc source.schema selection

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
