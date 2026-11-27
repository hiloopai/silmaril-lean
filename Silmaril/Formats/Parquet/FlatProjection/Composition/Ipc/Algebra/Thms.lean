module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

/-- A complete native trace aligns each batch with its checked schema. -/
theorem readEvents_aligned {limits : Arrow.MixedFlat.Limits} {wire : KBytes}
    {observed : EventObservation} (read : readEvents limits wire = some observed) :
    observed.AlignedWidth :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.readEvents_aligned read

/-- Selecting every position once in order recovers the exact observation. -/
theorem projectEvents_id {observed : EventObservation} (aligned : observed.AlignedWidth) :
    projectEvents (List.range observed.fields.length) observed = some observed :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.projectEvents_id aligned

/-- Projection fails exactly when some requested position is out of range. -/
theorem projectEvents_none_iff {positions : List Nat} {observed : EventObservation}
    (aligned : observed.AlignedWidth) :
    projectEvents positions observed = none ↔ ∃ i ∈ positions, observed.fields.length ≤ i :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.projectEvents_none_iff aligned

/-- Every successful projection again aligns each batch with its selected fields. -/
theorem projectEvents_aligned {positions : List Nat} {observed output : EventObservation}
    (projected : projectEvents positions observed = some output) : output.AlignedWidth :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.projectEvents_aligned projected

/-- Staged and composed selection agree as partial operations on complete
observations. An invalid intermediate position fails even when the second
selection would discard it. -/
theorem projectEvents_comp {first second : List Nat} {observed : EventObservation}
    (aligned : observed.AlignedWidth) :
    (projectEvents first observed).bind (projectEvents second) =
      (composePositions observed.fields.length first second).bind (projectEvents · observed) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.projectEvents_comp aligned

namespace Equivalent

variable {leftLimits middleLimits rightLimits : Arrow.MixedFlat.Limits} {left middle right : KBytes}

theorem refl {observation : EventObservation} (read : readEvents leftLimits left = some observation) :
    Equivalent leftLimits left leftLimits left := ⟨observation, read, read⟩

theorem symm (equal : Equivalent leftLimits left rightLimits right) :
    Equivalent rightLimits right leftLimits left := by
  obtain ⟨observation, leftRead, rightRead⟩ := equal
  exact ⟨observation, rightRead, leftRead⟩

theorem trans (first : Equivalent leftLimits left middleLimits middle)
    (second : Equivalent middleLimits middle rightLimits right) :
    Equivalent leftLimits left rightLimits right := by
  obtain ⟨observation, leftRead, middleRead⟩ := first
  obtain ⟨other, middleAgain, rightRead⟩ := second
  exact ⟨observation, leftRead, rightRead.trans (middleAgain.symm.trans middleRead)⟩

/-- Equivalent complete carriers agree on every positional projection,
including its refusal for invalid positions. -/
theorem project (equal : Equivalent leftLimits left rightLimits right) (positions : List Nat) :
    (readEvents leftLimits left).bind (projectEvents positions) =
      (readEvents rightLimits right).bind (projectEvents positions) := by
  obtain ⟨_, leftRead, rightRead⟩ := equal
  rw [leftRead, rightRead]

end Equivalent

end Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
