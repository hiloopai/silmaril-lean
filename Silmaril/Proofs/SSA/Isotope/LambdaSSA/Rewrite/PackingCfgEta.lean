module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackingRoundtrip
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationCategory

/-! # Exit packing in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem packExits_valueBranches {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) :
    ValueBranches Γ r.packExits [packedExitType L] :=
  valueBranches_lsubst hr (packExits_valueFamily Γ L)

theorem singleton_packExits_hom {Γ : VCtx τ} {A : τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches (A :: Γ) r L) :
    ContinuationContext.singletonToHom
        (Y := ContinuationContext.single (packedExitType L)) (packExits_valueBranches hr) =
      ContinuationContext.singletonToHom (Y := ⟨L⟩) hr ≫
        (ContinuationFamily.toHom (X := ⟨L⟩) (Y := ContinuationContext.single (packedExitType L))
          ⟨_, packExits_valueFamily Γ L⟩) := by
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i B hi
  have hB : B = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
  subst B
  change SubstitutionEquiv (A :: Γ) r.packExits
    (r.lsubst (liftLSubstVars (fun j => .br 0 (packedExitArg j (.var 0))))) [packedExitType L]
  rw [packFamily_liftVars]
  exact .base (.refl (packExits_valueBranches hr).hasType)

theorem ofRegion_packExits_bindBranchArguments_proof {Γ : VCtx τ} {A : τ}
    {L : LCtx τ} {r : Region Φ} (hr : ValueBranches (A :: Γ) r L) :
    (CfgEta.TypeCategory.ofRegion hr.hasType.packExits.bindBranchArguments).hom =
      CfgEta.fromNative.map (ContinuationContext.singletonToHom (Y := ⟨L⟩) hr) ≫
        CfgEta.fromNative.map
          (ContinuationFamily.toHom (X := ⟨L⟩) (Y := ContinuationContext.single (packedExitType L))
            ⟨_, packExits_valueFamily Γ L⟩) := by
  rw [← Functor.map_comp, ← singleton_packExits_hom hr]
  change CfgEta.fromNative.map (ContinuationContext.singletonToHom
    (Y := ContinuationContext.single (packedExitType L)) hr.hasType.packExits.bindBranchArguments) = _
  apply congrArg CfgEta.fromNative.map
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i B hi
  have hB : B = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
  subst B
  exact (bindBranchArguments_equiv (packExits_valueBranches hr)).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
