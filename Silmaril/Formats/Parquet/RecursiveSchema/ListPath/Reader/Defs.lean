module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs

/-! Reconstruct complete native V1/V2 groups for a checked canonical LIST path. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader

open Arrow.RecursiveSchema.Batch.Rows (Observation)

@[expose] public section

inductive Error where
  | binding (cause : Chunk.BindError)
  | chunk (cause : Chunk.Error)
  | reconstruction (address : RecursiveSchema.Chunk.Address) (cause : Rows.Error)
  deriving DecidableEq, Repr

/-- Feed the exact ordered trace of the entire original group to the
checked inverse. A page boundary never closes an in-progress row. -/
def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error Observation := do
  let binding ← (Chunk.bind schema group).mapError .binding
  let original ← (Chunk.read limits binding).mapError .chunk
  (Rows.reconstruct limits.logical schema.plan binding.rowGroup.numRows.toNat original.atoms).mapError
    (.reconstruction (Chunk.address schema.plan group))

def readAll {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) : Except Error (List Observation) :=
  (List.range snapshot.groupCount).mapM (readGroup limits schema)

structure GroupWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) (out : Observation) :
    Prop where
  original : ∃ (binding : Chunk.Binding schema group) (original : Chunk.Observation),
    Chunk.bind schema group = .ok binding ∧ Chunk.read limits binding = .ok original ∧
    Chunk.Wire limits (Chunk.carrierOf binding) original ∧
    Rows.ObservationWire limits.logical schema.plan original.atoms binding.rowGroup.numRows.toNat out

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader
