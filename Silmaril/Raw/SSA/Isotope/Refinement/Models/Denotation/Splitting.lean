module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Pure
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

@[expose] public section

-- Toolchain fix (port): Mathlib's `β_` and the premonoidal `β_` of
-- `Premonoidal.Symmetric` are both in scope; select Mathlib's braiding, as in the source.
local notation (priority := high) "β_" => CategoryTheory.BraidedCategory.braiding

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory
universe u v w r

namespace Structural
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
open MonoidalCategory BraidedCategory

/-- Exchange the two results of the tensor comparison. -/
theorem tensorμ_braid (W X Y Z : C) :
    tensorμ W X Y Z ≫ (β_ (W ⊗ Y) (X ⊗ Z)).hom =
      ((β_ W X).hom ⊗ₘ (β_ Y Z).hom) ≫ tensorμ X W Z Y := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X, tensorHom_def]

/-- Move a new final slot to the first output, then exchange the outputs. -/
theorem moveLeft_braid (L R A : C) :
    (α_ L R A).hom ≫ L ◁ (β_ R A).hom ≫ (α_ L A R).inv ≫ (β_ (L ⊗ A) R).hom =
      (β_ L R).hom ▷ A ≫ (α_ R L A).hom := by
  apply (cancel_epi ((β_ R L).hom ▷ A)).1
  simp only [← BraidedCategory.hexagon_forward_assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  simp
/-- The corresponding coherence equation when the new slot belongs to the second output. -/
theorem moveRight_braid (L R A : C) :
    (α_ L R A).hom ≫ (β_ L (R ⊗ A)).hom =
      (β_ L R).hom ▷ A ≫ (α_ R L A).hom ≫ R ◁ (β_ L A).hom ≫ (α_ R A L).inv := by
  apply (cancel_mono (β_ (R ⊗ A) L).hom).1
  simp only [Category.assoc, SymmetricCategory.symmetry, Category.comp_id]
  rw [moveLeft_braid]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  simp
/-- Coherence for an unused second output when a retained slot is appended. -/
theorem rightUnitorInv_moveLeft (L A : C) :
    (ρ_ L).inv ▷ A ≫ (α_ L (𝟙_ C) A).hom ≫ L ◁ (β_ (𝟙_ C) A).hom ≫
      (α_ L A (𝟙_ C)).inv = (ρ_ (L ⊗ A)).inv := by
  rw [braiding_tensorUnit_left]
  monoidal

end Structural

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

@[simp] theorem copy_braiding (A : τ) (h : Quantity.relevant ≤ quantity A) :
    M.compose (M.copy A h) (M.braiding A A) = M.copy A h := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, copy, braiding, Category.assoc]
  rw [← Category.assoc, M.copyDiscard.copy_comm]

end SeqData
namespace Denotation
open MonoidalCategory BraidedCategory
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem splitSlot_symm {L B D A : τ} (f : PureHom M L (product B D))
    {q ql qr : Usage} (h : QCtx.SlotSplit A q ql qr) :
    pureCompose M (splitSlot M f h)
      ⟨M.braiding (retain B A ql) (retain D A qr), M.braiding_pure _ _⟩ =
    splitSlot M (pureCompose M f ⟨M.braiding B D, M.braiding_pure _ _⟩) h.symm := by
  let L' : M.PureObject := ⟨L⟩
  let B' : M.PureObject := ⟨B⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ff : L' ⟶ B' ⊗ D' := f
  cases q <;> cases ql <;> cases qr
  · rfl
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · change (ff ▷ A' ≫ (α_ B' D' A').hom) ≫ (β_ B' (D' ⊗ A')).hom =
      (ff ≫ (β_ B' D').hom) ▷ A' ≫
        (α_ D' B' A').hom ≫ D' ◁ (β_ B' A').hom ≫ (α_ D' A' B').inv
    simp only [comp_whiskerRight, Category.assoc, Structural.moveRight_braid]
  · change (ff ▷ A' ≫ (α_ B' D' A').hom ≫ B' ◁ (β_ D' A').hom ≫ (α_ B' A' D').inv) ≫
      (β_ (B' ⊗ A') D').hom = (ff ≫ (β_ B' D').hom) ▷ A' ≫ (α_ D' B' A').hom
    simp only [comp_whiskerRight, Category.assoc, Structural.moveLeft_braid]
  · have hc : Quantity.relevant ≤ quantity A := by
      cases h with
      | both h => exact ((Usage.relevant_le_effective_iff _ _).mp h).1.trans inf_le_left
    let c : A' ⟶ A' ⊗ A' := ⟨M.copy A hc, M.copy_pure _ _⟩
    have hcomm : c ≫ (β_ A' A').hom = c := Subtype.ext (M.copy_braiding A hc)
    change ((ff ⊗ₘ c) ≫ tensorμ B' D' A' A') ≫ (β_ (B' ⊗ A') (D' ⊗ A')).hom =
      ((ff ≫ (β_ B' D').hom) ⊗ₘ c) ≫ tensorμ D' B' A' A'
    rw [Category.assoc, Structural.tensorμ_braid, ← Category.assoc, tensorHom_comp_tensorHom, hcomm]

/-- Native context splitting is symmetric, using the model's actual braiding. -/
theorem splitPure_symm {n : Nat} {Γ Γl Γr : QCtx τ n} (h : QCtx.Split Γ Γl Γr) :
    pureCompose M (splitPure M h)
      ⟨M.braiding (packed Γl) (packed Γr), M.braiding_pure _ _⟩ = splitPure M h.symm := by
  induction n with
  | zero =>
    change (λ_ (𝟙_ M.PureObject)).inv ≫ (β_ (𝟙_ M.PureObject) (𝟙_ M.PureObject)).hom =
      (λ_ (𝟙_ M.PureObject)).inv
    rw [leftUnitor_inv_braiding]
    monoidal
  | succ n ih =>
    let Γt : QCtx τ n := fun i => Γ i.succ
    let Γlt : QCtx τ n := fun i => Γl i.succ
    let Γrt : QCtx τ n := fun i => Γr i.succ
    have ht : QCtx.Split Γt Γlt Γrt := fun i => h i.succ
    have hl : Γlt.snoc (Γ 0).1 (Γl 0).2 = Γl := by
      rw [← (h 0).1]
      exact QCtx.snoc_tail Γl
    have hr : Γrt.snoc (Γ 0).1 (Γr 0).2 = Γr := by
      rw [← (h 0).2.1]
      exact QCtx.snoc_tail Γr
    have he := splitSlot_symm M (splitPure M ht) (h 0).2.2
    rw [ih ht] at he
    let P (p : QCtx τ (n + 1) × QCtx τ (n + 1) × QCtx τ (n + 1)) :=
      ∀ k : QCtx.Split p.1 p.2.1 p.2.2, pureCompose M (splitPure M k)
        ⟨M.braiding (packed p.2.1) (packed p.2.2), M.braiding_pure _ _⟩ = splitPure M k.symm
    have hall : P (Γt.snoc (Γ 0).1 (Γ 0).2,
        Γlt.snoc (Γ 0).1 (Γl 0).2, Γrt.snoc (Γ 0).1 (Γr 0).2) := fun _ => he
    have hΓ : Γt.snoc (Γ 0).1 (Γ 0).2 = Γ := QCtx.snoc_tail Γ
    exact ((congrArg P (congrArg₂ Prod.mk hΓ (congrArg₂ Prod.mk hl hr))).mp hall) h

theorem split_symm {n : Nat} {Γ Γl Γr : QCtx τ n} (h : QCtx.Split Γ Γl Γr) :
    M.compose (split M h) (M.braiding (packed Γl) (packed Γr)) = split M h.symm :=
  congrArg Subtype.val (splitPure_symm M h)

omit [TypeQuantity τ] in
/-- A zero-only context contributes just the tensor unit. -/
@[simp] theorem packed_zero {n : Nat} (Γ : QCtx τ n) : packed Γ.zero = Silmaril.unit := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun i => Γ i.succ)

/-- Record the type equality together with the context arrow, avoiding arbitrary
casts in the unit coherence statement. -/
theorem split_zero_right_pair {n : Nat} (Γ : QCtx τ n) :
    (⟨packed Γ.zero, splitPure M (QCtx.Split.zero_right Γ)⟩ :
      Σ B : τ, PureHom M (packed Γ) (product (packed Γ) B)) =
    ⟨Silmaril.unit, ⟨M.rightUnitorInv (packed Γ), M.rightUnitorInv_pure _⟩⟩ := by
  induction n with
  | zero =>
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    change (λ_ (𝟙_ M.PureObject)).inv = (ρ_ (𝟙_ M.PureObject)).inv
    monoidal
  | succ n ih =>
    have hs (Γt : QCtx τ n) (A : τ) (q : Usage) :
        (⟨packed (Γt.snoc A q).zero, splitPure M (QCtx.Split.zero_right (Γt.snoc A q))⟩ :
          Σ B : τ, PureHom M (packed (Γt.snoc A q)) (product (packed (Γt.snoc A q)) B)) =
        ⟨Silmaril.unit, ⟨M.rightUnitorInv (packed (Γt.snoc A q)), M.rightUnitorInv_pure _⟩⟩ := by
      cases q with
      | zero => exact ih Γt
      | used q =>
        let T (p : Σ B : τ, PureHom M (packed Γt) (product (packed Γt) B)) :
            Σ B : τ, PureHom M (product (packed Γt) A) (product (product (packed Γt) A) B) :=
          ⟨p.1, splitSlot M p.2 (QCtx.SlotSplit.left (.used q))⟩
        have he := congrArg T (ih Γt)
        refine he.trans ?_
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        change (ρ_ (⟨packed Γt⟩ : M.PureObject)).inv ▷ (⟨A⟩ : M.PureObject) ≫
          (α_ (⟨packed Γt⟩ : M.PureObject) (𝟙_ M.PureObject) (⟨A⟩ : M.PureObject)).hom ≫
          (⟨packed Γt⟩ : M.PureObject) ◁ (β_ (𝟙_ M.PureObject) (⟨A⟩ : M.PureObject)).hom ≫
          (α_ (⟨packed Γt⟩ : M.PureObject) (⟨A⟩ : M.PureObject) (𝟙_ M.PureObject)).inv =
          (ρ_ ((⟨packed Γt⟩ : M.PureObject) ⊗ (⟨A⟩ : M.PureObject))).inv
        exact Structural.rightUnitorInv_moveLeft _ _
    let P (G : QCtx τ (n + 1)) :=
      (⟨packed G.zero, splitPure M (QCtx.Split.zero_right G)⟩ :
        Σ B : τ, PureHom M (packed G) (product (packed G) B)) =
      ⟨Silmaril.unit, ⟨M.rightUnitorInv (packed G), M.rightUnitorInv_pure _⟩⟩
    exact (congrArg P (QCtx.snoc_tail Γ)).mp (hs _ _ _)

/-- Splitting off unused slots is the right unitor inverse. -/
theorem split_zero_right {n : Nat} (Γ : QCtx τ n) :
    HEq (split M (QCtx.Split.zero_right Γ)) (M.rightUnitorInv (packed Γ)) := by
  let erase (p : Σ B : τ, PureHom M (packed Γ) (product (packed Γ) B)) :
      Σ B : τ, M.Hom (packed Γ) (product (packed Γ) B) := ⟨p.1, p.2.1⟩
  exact (Sigma.mk.inj_iff.mp (congrArg erase (split_zero_right_pair M Γ))).2

theorem split_zero_left_pair {n : Nat} (Γ : QCtx τ n) :
    (⟨packed Γ.zero, splitPure M (QCtx.Split.zero_left Γ)⟩ :
      Σ B : τ, PureHom M (packed Γ) (product B (packed Γ))) =
    ⟨Silmaril.unit, ⟨M.leftUnitorInv (packed Γ), M.leftUnitorInv_pure _⟩⟩ := by
  let T (p : Σ B : τ, PureHom M (packed Γ) (product (packed Γ) B)) :
      Σ B : τ, PureHom M (packed Γ) (product B (packed Γ)) :=
    ⟨p.1, pureCompose M p.2 ⟨M.braiding (packed Γ) p.1, M.braiding_pure _ _⟩⟩
  have he := congrArg T (split_zero_right_pair M Γ)
  have hs := splitPure_symm M (QCtx.Split.zero_right Γ)
  have start : (⟨packed Γ.zero, splitPure M (QCtx.Split.zero_left Γ)⟩ :
      Σ B : τ, PureHom M (packed Γ) (product B (packed Γ))) =
      T ⟨packed Γ.zero, splitPure M (QCtx.Split.zero_right Γ)⟩ :=
    congrArg (fun f => (⟨packed Γ.zero, f⟩ : Σ B : τ, PureHom M (packed Γ) (product B (packed Γ)))) hs.symm
  refine start.trans (he.trans ?_)
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact rightUnitor_inv_braiding (⟨packed Γ⟩ : M.PureObject)

/-- Splitting off unused slots is the left unitor inverse. -/
theorem split_zero_left {n : Nat} (Γ : QCtx τ n) :
    HEq (split M (QCtx.Split.zero_left Γ)) (M.leftUnitorInv (packed Γ)) := by
  let erase (p : Σ B : τ, PureHom M (packed Γ) (product B (packed Γ))) :
      Σ B : τ, M.Hom (packed Γ) (product B (packed Γ)) := ⟨p.1, p.2.1⟩
  exact (Sigma.mk.inj_iff.mp (congrArg erase (split_zero_left_pair M Γ))).2

end Denotation
end Silmaril.Isotope.Refinement.Models
