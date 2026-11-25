module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Pure-return representatives in the CFG η singleton category -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Values

open CategoryTheory
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (TypeCategory toHom_eq_iff)
open Region.CfgEta.TypeCategory

variable {τ : Type v} [TypeFormers τ] {Φ : Type u} [HasTy Φ τ]
  {Γ : VCtx τ} {A B C : τ} {a b : Tm Φ}

private theorem returnRegion_rename (a : Tm Φ) (ρ : Nat → Nat) :
    returnRegion (a.rename ρ) = (returnRegion a).renameVars ρ := by
  induction a generalizing ρ <;> try rfl
  case let₁ a b iha ihb =>
    simp only [Tm.rename, returnRegion, renameVars_lsubst, iha, ihb]

theorem returnRegion_typed (h : Tm.HasType Γ a B) :
    ValueBranches Γ (returnRegion a) [B] := by
  induction h with
  | @let₁ Γ a b A B ha hb iha ihb =>
      have second : LSubst.ValueFamily Γ [A] [B] (fun _ => returnRegion b) :=
        fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ ihb
      exact iha.lsubst second
  | _ => exact .let₁ (by constructor <;> assumption) (.br rfl (.var rfl))

theorem returnRegion_branchValue (h : Tm.BranchValue Γ a B) :
    RewriteEquiv Γ (returnRegion a) (.br 0 a) [B] := by
  have eq := RewriteEquiv.letBr h (.var (i := 0) rfl) (L := [B]) (ℓ := 0) rfl
  cases h <;> exact eq

private theorem returnRegion_identity (h : ValueBranches ([A] : VCtx τ)
    (returnRegion (.var 0 : Tm Φ)) [A]) :
    ofRegion h = 𝟙 (ofType (Φ := Φ) (Γ := []) A) := by
  apply InducedCategory.hom_ext
  apply toHom_eq_iff.mpr
  intro i D hi
  change At [A] i D at hi
  cases i with
  | zero =>
      cases Option.some.inj hi
      exact .native (.base (returnRegion_branchValue (.var (i := 0) rfl)))
  | succ i => simp [At] at hi

variable {ε : Type w} [HasEff Φ ε] {pe : ε}
local notation "Comp" => TypeCategory Φ ([] : VCtx τ)

theorem pureReturn_id (A : Comp) : PureReturn pe (𝟙 A) := by
  let T : τ := A
  have h : Tm.HasType [T] (.var 0 : Tm Φ) T := .var rfl
  exact ⟨.var 0, h, .var, returnRegion_typed h, (returnRegion_identity (A := T) _).symm⟩

theorem pureReturn_comp {X Y Z : Comp} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : PureReturn pe f) (hg : PureReturn pe g) : PureReturn pe (f ≫ g) := by
  obtain ⟨a, ha, pa, ra, rfl⟩ := hf
  obtain ⟨b, hb, pb, rb, rfl⟩ := hg
  have capture : Ren ([] : VCtx τ) [X] Nat.succ := by
    intro i A h
    simp [At] at h
  have h := Tm.HasType.let₁ ha (hb.rename (capture.lift Y))
  refine ⟨_, h, .let₁ pa (pb.rename (lift Nat.succ)), returnRegion_typed h, ?_⟩
  apply InducedCategory.hom_ext
  apply toHom_eq_iff.mpr
  intro i D hi
  change At [X] i D at hi
  have eq : D = X := List.mem_singleton.mp (List.mem_of_getElem? hi)
  subst D
  have he : returnRegion (.let₁ a (b.rename (lift Nat.succ))) =
      (returnRegion a).lsubst (fun _ => (returnRegion b).renameVars (lift Nat.succ)) := by
    simp only [returnRegion, returnRegion_rename]
  change Region.CfgEta.Eqv ([X] : VCtx τ) ((returnRegion a).lsubst
    (fun _ => (returnRegion b).renameVars (lift Nat.succ))) (returnRegion _) [Z]
  rw [← he]
  exact .native (.base (.refl (returnRegion_typed h).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Values
