module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRawBranchBinding

/-! # Exact branch normalization and raw generation for computed products -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding

open Silmaril.Isotope.LambdaSSA
open Paper.SingletonReification.BinaryLet (returnPair returnPair_typed)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton (NormalizedSeed rawClass)
open Paper.WithProductDestructureReturns (GuardedFragmentWithProducts)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The literal raw producer equates the two endpoints at the exact product type. -/
theorem raw_producer {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (product A B)) :
    Extension.Eqv (RawJoinedStep pe) [X] (returnPair a) (.br 0 a) [product A B] :=
  .extra (returnPair_typed ha).hasType (.br rfl ha) (.inl (.inr (.producer ha)))

/-- In the contextual closure, either producer generator replays from the other
using branch binding at its exit. -/
theorem raw_eqv_iff_replayed {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ} :
    Extension.Eqv (RawJoinedStep pe) Γ r s L ↔
      Extension.Eqv (AddBinding (JoinedStep pe)) Γ r s L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRawBranchBinding.raw_eqv_iff_replayed pe

/-- Raw equivalence is exactly equivalence of the branch-normalized regions. -/
theorem raw_eqv_iff_normalized {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Extension.Eqv (RawJoinedStep pe) Γ r s L ↔
      Extension.Eqv (JoinedStep pe) Γ r.bindBranchArguments s.bindBranchArguments L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductRawBranchBinding.raw_eqv_iff_normalized pe hr hs

/-- Use the literal raw generators with the existing singleton operations. -/
@[expose] def singletonSeed : NormalizedSeed τ Φ where
  step := JoinedStep pe
  rawStep := RawJoinedStep pe
  eqv_iff_normalized := raw_eqv_iff_normalized pe

local notation "S" => singletonSeed (τ := τ) (Φ := Φ) pe

/-- The literal producer equation holds in the singleton raw hom. -/
theorem raw_class_producer_eq {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (product A B)) :
    rawClass S (returnPair_typed ha).hasType = rawClass S (.br (ℓ := 0) rfl ha) :=
  Quotient.sound (raw_producer pe ha)

/-- Transfer the computed-scrutinee grammar to the literal raw class. -/
theorem raw_generated_guardedFragment {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragmentWithProducts pe true hr) :
    Singleton.Generation.Generated S (rawClass S hr.hasType) :=
  (Singleton.Generation.generated_rawClass_iff S hr).mpr
    (generated_guardedFragment pe h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
