module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Defs

/-! Materialize complete IPC observations as ordered nullable Scan rows. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows

open Silmaril.Relational
open Arrow.MixedFlat (Field)

abbrev Schema := Scan.Schema Field Unit
abbrev Columns (schema : Schema) := Scan.Columns schema (fun _ => Cell)
abbrev Table := Scan.Observation Field (fun _ : Unit => Cell)

abbrev schema := Arrow.MixedFlat.Events.schema

/-- The explicit row count is retained even when the batch has no columns. -/
def BatchAligned (width : Nat) (batch : BatchObservation) : Prop :=
  batch.2.length = width ∧ ∀ column ∈ batch.2, column.length = batch.1

instance (width : Nat) (batch : BatchObservation) : Decidable (BatchAligned width batch) := by
  unfold BatchAligned
  infer_instance

def Aligned (observation : EventObservation) : Prop :=
  ∀ batch ∈ observation.batches, BatchAligned observation.fields.length batch

instance (observation : EventObservation) : Decidable (Aligned observation) := by
  unfold Aligned
  infer_instance

/-- Record aligned Scan columns without altering their explicit row count. -/
def observeColumns {signature : Schema} (columns : Columns signature) : BatchObservation :=
  (columns.rowCount, List.ofFn columns.values)

def batchColumns (signature : Schema) (batch : BatchObservation)
    (aligned : BatchAligned signature.width batch) : Columns signature where
  rowCount := batch.1
  values i := batch.2[i.val]'(by simp [aligned.1])
  length_eq i := aligned.2 _ (List.getElem_mem _)

def alignedBatches (signature : Schema) (batches : List BatchObservation)
    (aligned : ∀ batch ∈ batches, BatchAligned signature.width batch) : List (Columns signature) :=
  batches.pmap (batchColumns signature) aligned

/-- The ordered Scan schema keeps full field descriptors independently of
field name uniqueness. Batch boundaries are erased by concatenating rows. -/
def materialize (observed : EventObservation) (aligned : Aligned observed) : Table :=
  ⟨schema observed.fields,
    (alignedBatches (schema observed.fields) observed.batches aligned).flatMap AlignedColumns.toRows⟩

def toTable (observed : EventObservation) : Option Table :=
  if aligned : Aligned observed then some (materialize observed aligned) else none

/-- A partial native event trace supplies no relational table. -/
def readRows (limits : Arrow.MixedFlat.Limits) (wire : KBytes) : Option Table :=
  (readEvents limits wire).bind toTable

/-- The raw positions corresponding to a typed Scan projection. -/
def positions {signature : Schema} (projection : Scan.Projection signature) : List Nat :=
  List.ofFn fun i => (projection.index i).val

/-- Compare complete reads by ordered schema and flattened nullable rows. -/
def Equivalent (leftLimits : Arrow.MixedFlat.Limits) (left : KBytes)
    (rightLimits : Arrow.MixedFlat.Limits) (right : KBytes) : Prop :=
  ∃ table, readRows leftLimits left = some table ∧ readRows rightLimits right = some table

end Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows
