module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.StructuralNaturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Variables
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Associativity

/-! # Categorical interpretation of ordinary binding -/

@[expose] public section
noncomputable section

namespace CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

@[reassoc] theorem transport_whiskerLeft {A A' B D : C} (h : A = A') (f : B ⟶ D) :
    eqToHom (congrArg (fun X => X ⊗ B) h) ≫ A' ◁ f =
      A ◁ f ≫ eqToHom (congrArg (fun X => X ⊗ D) h) := by
  subst A'
  simp

end CategoryTheory.PremonoidalCategory

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory Denotation
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Unit insertion and elimination cancel around an arbitrary computation. -/
theorem unit_bind {A B : τ} (f : M.Hom A B) :
    M.compose (M.leftUnitorInv A) (M.compose (M.left Silmaril.unit f) (M.leftUnitor B)) = f := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, leftUnitorInv, left, leftUnitor, Category.assoc,
    eqToHom_trans_assoc]
  rw [PremonoidalCategory.transport_whiskerLeft_assoc M.tensor_unit f]
  simp [PremonoidalCategory.leftUnitor_naturality]

/-- Associator naturality when the computation acts on the final component. -/
theorem associator_natural_right (D E : τ) {A B : τ} (f : M.Hom A B) :
    M.compose (M.associator D E A) (M.left D (M.left E f)) =
      M.compose (M.left (product D E) f) (M.associator D E B) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, left, associator, Category.assoc,
    PremonoidalCategory.whiskerLeft_comp, PremonoidalCategory.whiskerLeft_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← PremonoidalCategory.transport_whiskerLeft_assoc (M.tensor_obj D E).symm f]
  simp [PremonoidalCategory.associator_naturality_right_assoc]

/-- Braiding is natural in one arbitrary computation. -/
theorem braiding_natural_right (D : τ) {A B : τ} (f : M.Hom A B) :
    M.compose (M.left D f) (M.braiding D B) =
      M.compose (M.braiding D A) (M.right f D) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [SeqData.compose, SeqData.left, SeqData.right, SeqData.braiding,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [BraidedPremonoidalCategory.naturality_right_assoc]

/-- Inverse associator naturality in its final, possibly effectful component. -/
theorem associatorInv_natural_right (D E : τ) {A B : τ} (f : M.Hom A B) :
    M.compose (M.left D (M.left E f)) (M.associatorInv D E B) =
      M.compose (M.associatorInv D E A) (M.left (product D E) f) := by
  have h := congrArg (fun k => M.compose (M.associatorInv D E A)
      (M.compose k (M.associatorInv D E B)))
    (M.associator_natural_right D E f)
  simp only [← M.compose_assoc, M.associator_inv_hom,
    M.identity_compose] at h
  simpa only [M.compose_assoc, M.associator_hom_inv,
    M.compose_identity] using h

end SeqData

namespace Denotation
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Context splitting associates through two effectful computations. Only the
structural split is exchanged with a computation, so purity suffices. -/
theorem split_bind_assoc {n : Nat} {Γ Γ12 Γ1 Γ2 Γ3 Γ23 : QCtx τ n} {A B : τ}
    (s : Γ.Split Γ12 Γ3) (t : Γ12.Split Γ1 Γ2)
    (u : Γ.Split Γ1 Γ23) (v : Γ23.Split Γ2 Γ3)
    (a : M.Hom (packed Γ3) A) (b : M.Hom (product (packed Γ2) A) B) :
    M.compose (split M.toSeqData u)
      (M.left (packed Γ1) (M.compose (split M.toSeqData v)
        (M.compose (M.left (packed Γ2) a) b))) =
    M.compose (split M.toSeqData s) (M.compose (M.left (packed Γ12) a)
      (M.compose (M.right (split M.toSeqData t) A)
        (M.compose (M.associator (packed Γ1) (packed Γ2) A) (M.left (packed Γ1) b)))) := by
  simp only [M.toSeqData.left_compose]
  rw [← M.toSeqData.compose_assoc (split M.toSeqData u) (M.left (packed Γ1) (split M.toSeqData v)),
    ← split_assoc M.toSeqData s t u v]
  simp only [M.toSeqData.compose_assoc]
  rw [← M.toSeqData.compose_assoc (M.associator (packed Γ1) (packed Γ2) (packed Γ3)),
    M.toSeqData.associator_natural_right]
  simp only [M.toSeqData.compose_assoc]
  rw [← M.toSeqData.compose_assoc (M.right (split M.toSeqData t) (packed Γ3)),
    M.toSeqData.exchange_left_pure _ _ (split_pure M.toSeqData t)]
  simp only [M.toSeqData.compose_assoc]

/-- Sending the newest slot to the right output is the associator step. -/
theorem split_snoc_right {n : Nat} {Γ Γl Γr : QCtx τ n}
    (s : Γ.Split Γl Γr) (A : τ) (q : Quantity) :
    split M.toSeqData (s.snoc (.right (.used q)) (A := A)) =
      M.compose (M.right (split M.toSeqData s) A)
        (M.associator (packed Γl) (packed Γr) A) := rfl

/-- Inserting a unit immediately before the newest component cancels its
left unitor. This is pure tensor coherence. -/
theorem newest_unit_cancel (D A : τ) :
    M.compose (M.right (M.rightUnitorInv D) A)
      (M.compose (M.associator D Silmaril.unit A) (M.left D (M.leftUnitor A))) =
        M.identity (product D A) := by
  let D' : M.toSeqData.PureObject := ⟨D⟩
  let A' : M.toSeqData.PureObject := ⟨A⟩
  have h : (ρ_ D').inv ▷ A' ≫ (α_ D' (𝟙_ M.toSeqData.PureObject) A').hom ≫
      D' ◁ (λ_ A').hom = 𝟙 (D' ⊗ A') := by monoidal
  exact congrArg Subtype.val h

/-- An empty right split followed by selection of the newest slot leaves
the retained context unchanged. -/
theorem newest_split_bind_aux {X D A B : τ} (hX : X = Silmaril.unit)
    (g : M.Hom D (product D X)) (hg : HEq g (M.rightUnitorInv D))
    (hd : Quantity.affine ≤ quantity X) (f : M.Hom A B) :
    M.compose (M.right g A)
      (M.compose (M.associator D X A)
        (M.left D (M.compose (M.right (M.discard X hd) A)
          (M.compose (M.leftUnitor A) f)))) = M.left D f := by
  subst X
  cases eq_of_heq hg
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.identity_compose]
  rw [M.toSeqData.left_compose]
  rw [← M.toSeqData.compose_assoc, ← M.toSeqData.compose_assoc]
  rw [M.toSeqData.compose_assoc (M.right (M.rightUnitorInv D) A)
    (M.associator D Silmaril.unit A) (M.left D (M.leftUnitor A))]
  rw [newest_unit_cancel M, M.toSeqData.identity_compose]

/-- Interpreting an instruction on the newest variable after splitting off
its unused outer slots is just left whiskering that instruction. -/
theorem newest_split_bind {n : Nat} (Γ : QCtx τ n) {A B : τ}
    (hd : Γ.zero.Discardable) (f : M.Hom A B) :
    M.compose (split M.toSeqData ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)) (A := A)))
      (M.left (packed Γ) (M.compose (M.right (discard M.toSeqData hd) A)
        (M.compose (M.leftUnitor A) f))) = M.left (packed Γ) f := by
  change M.compose
      (M.compose (M.right (split M.toSeqData (QCtx.Split.zero_right Γ)) A)
        (M.associator (packed Γ) (packed Γ.zero) A))
      (M.left (packed Γ) (M.compose (M.right (discard M.toSeqData hd) A)
        (M.compose (M.leftUnitor A) f))) = M.left (packed Γ) f
  rw [M.toSeqData.compose_assoc]
  exact newest_split_bind_aux M (packed_zero Γ) _ (split_zero_right M.toSeqData Γ) _ f

/-- Selecting the newest variable after its canonical split is an identity. -/
theorem newest_split_variable {n : Nat} (Γ : QCtx τ n) (A : τ)
    (hd : Γ.zero.Discardable) :
    M.compose (split M.toSeqData ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)) (A := A)))
      (M.left (packed Γ) (M.compose (M.right (discard M.toSeqData hd) A)
        (M.leftUnitor A))) = M.identity (product (packed Γ) A) := by
  have h := newest_split_bind M Γ hd (M.identity A)
  rw [M.toSeqData.compose_identity, M.toSeqData.left_identity] at h
  exact h

/-- Eliminate an empty retained environment, accounting for its packed type. -/
theorem zero_context_bind_aux {X C A : τ} (hX : X = Silmaril.unit)
    (g : M.Hom C (product X C)) (hg : HEq g (M.leftUnitorInv C))
    (hd : Quantity.affine ≤ quantity X) (a : M.Hom C A) :
    M.compose g (M.compose (M.left X a)
      (M.compose (M.right (M.discard X hd) A) (M.leftUnitor A))) = a := by
  subst X
  cases eq_of_heq hg
  rw [M.discard_unit, M.toSeqData.right_identity, M.identity_compose]
  exact M.toSeqData.unit_bind a

/-- Binding with an unused outer continuation context passes the resulting
value directly to the newest-variable projection. -/
theorem zero_context_bind {n : Nat} (Γ : QCtx τ n) {A : τ} (a : M.Hom (packed Γ) A)
    (hd : Γ.zero.Discardable) :
    M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
      (M.compose (M.left (packed Γ.zero) a)
        (M.compose (M.right (discard M.toSeqData hd) A) (M.leftUnitor A))) = a :=
  zero_context_bind_aux M (packed_zero Γ) _ (split_zero_left M.toSeqData Γ) _ a

/-- Return the bound value after evaluating an arbitrary expression. -/
theorem denote_let_return {F : Fragment} (K : ControlData M.toSeqData F)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {a : Term Φ n} {A : τ}
    (ha : HasType F Γ e a A) :
    denote M.toSeqData K (HasType.let₁ (QCtx.Split.zero_left Γ) ha
      (.var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A))) = denote M.toSeqData K ha := by
  change M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
    (M.compose (M.left (packed Γ.zero) (denote M.toSeqData K ha))
      (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) A) (M.leftUnitor A))) = _
  exact zero_context_bind M Γ _ _

end Denotation
end Silmaril.Isotope.Refinement.Models
