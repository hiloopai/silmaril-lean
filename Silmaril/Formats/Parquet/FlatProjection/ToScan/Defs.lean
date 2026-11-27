module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Defs

/-! Observe projected Parquet groups directly in the common Scan cell carrier. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.ToScan

open FlatProjection.Composition.Ipc
open Arrow.MixedFlat

/-- A group contributes its explicit row count and one nullable slot list
per selected leaf, including when the projection has width zero. -/
def observeGroup (batch : OrderedWriter.BatchInput) : BatchObservation :=
  (batch.rowCount, batch.columns.map (observeSlots ∘ OrderedWriter.Column.observe))

/-- Normalize already checked group results without opening or reading the source. -/
def observeGroups (checked : Checked) (batches : List OrderedWriter.BatchInput) : EventObservation :=
  ⟨checked.fields, batches.map observeGroup⟩

end Silmaril.Formats.Parquet.FlatProjection.ToScan
