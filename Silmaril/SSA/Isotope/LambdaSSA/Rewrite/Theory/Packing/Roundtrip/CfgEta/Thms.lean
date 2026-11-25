module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackingCfgEta

/-! # The exit-packing factor of singleton region arrows -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Tagging the exits preserves constructor-valued branches. -/
theorem ValueBranches.packExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) : ValueBranches Γ r.packExits [packedExitType L] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packExits_valueBranches hr

namespace CfgEta.TypeCategory

/-- The literal tags postcompose the singleton-source continuation arrow.
This applies to any exactly typed producer after binding its branch arguments. -/
theorem ofRegion_packExits {Γ : VCtx τ} {A : τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches (A :: Γ) r L) :
    (ofRegion hr.packExits).hom =
      CfgEta.fromNative.map (ContinuationContext.singletonToHom (Y := ⟨L⟩) hr) ≫
        CfgEta.fromNative.map
          (ContinuationFamily.toHom (X := ⟨L⟩) (Y := ContinuationContext.single (packedExitType L))
            ⟨_, packExits_valueFamily Γ L⟩) := by
  rw [← Functor.map_comp, ← Proofs.SSA.Isotope.LambdaSSA.Rewrite.singleton_packExits_hom hr]
  rfl

/-- The packed singleton arrow is categorical composition with the tag family.
The producer may contain any local CFGs and computations before its value branches.
This form includes the additional branch binding after tagging. -/
theorem ofRegion_packExits_bindBranchArguments {Γ : VCtx τ} {A : τ}
    {L : LCtx τ} {r : Region Φ} (hr : ValueBranches (A :: Γ) r L) :
    (ofRegion hr.hasType.packExits.bindBranchArguments).hom =
      CfgEta.fromNative.map (ContinuationContext.singletonToHom (Y := ⟨L⟩) hr) ≫
        CfgEta.fromNative.map
          (ContinuationFamily.toHom (X := ⟨L⟩) (Y := ContinuationContext.single (packedExitType L))
            ⟨_, packExits_valueFamily Γ L⟩) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ofRegion_packExits_bindBranchArguments_proof hr

end CfgEta.TypeCategory

end Silmaril.Isotope.LambdaSSA.Region
