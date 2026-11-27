module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Defs

/-! Positional algebra for complete, batch-sensitive IPC observations. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

/-- Every batch supplies one column for each field of the original schema. -/
def EventObservation.AlignedWidth (observation : EventObservation) : Prop :=
  ∀ batch ∈ observation.batches, batch.2.length = observation.fields.length

/-- Compose positions after checking the intermediate selection against its original width. -/
def composePositions (width : Nat) (first second : List Nat) : Option (List Nat) :=
  (select first (List.range width)).bind (select second)

/-- Equivalence requires both reads to reach EOS. It retains the complete
schema and each original batch, including the position of empty batches. -/
def Equivalent (leftLimits : Arrow.MixedFlat.Limits) (left : KBytes)
    (rightLimits : Arrow.MixedFlat.Limits) (right : KBytes) : Prop :=
  ∃ observation, readEvents leftLimits left = some observation ∧
    readEvents rightLimits right = some observation

end Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
