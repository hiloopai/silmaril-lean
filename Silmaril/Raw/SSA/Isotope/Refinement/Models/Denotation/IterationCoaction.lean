module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationStrength

/-! # Iteration along a pure retained-context coaction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r

namespace Structural
open MonoidalCategory
variable {K : Type u} [Category.{v} K] [MonoidalCategory K]

/-- A coaction can extract two copies of its persistent component. -/
theorem coaction_duplicate {C D : K} (j : C ⟶ C ⊗ D) (c : D ⟶ D ⊗ D)
    (hj : j ≫ j ▷ D ≫ (α_ C D D).hom = j ≫ C ◁ c) (A : K) :
    j ▷ A ≫ (α_ C D A).hom ≫ C ◁ (c ▷ A ≫ (α_ D D A).hom) =
      j ▷ A ≫ (α_ C D A).hom ≫ j ▷ (D ⊗ A) ≫ (α_ C D (D ⊗ A)).hom := by
  simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc, ← hj]
  simp only [comp_whiskerRight, Category.assoc]
  rw [pentagon]
  rw [← associator_naturality_left_assoc]

/-- Discarding the extracted component is the coaction counit. -/
theorem coaction_counit {C D : K} (j : C ⟶ C ⊗ D) (d : D ⟶ 𝟙_ K)
    (hj : j ≫ C ◁ d ≫ (ρ_ C).hom = 𝟙 C) (A : K) :
    j ▷ A ≫ (α_ C D A).hom ≫ C ◁ (d ▷ A ≫ (λ_ A).hom) = 𝟙 (C ⊗ A) := by
  simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  have ht : (α_ C (𝟙_ K) A).hom ≫ C ◁ (λ_ A).hom = (ρ_ C).hom ▷ A := by monoidal
  rw [ht, ← comp_whiskerRight_assoc, ← comp_whiskerRight, Category.assoc, hj, id_whiskerRight]

end Structural

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A pure retained context that supplies a persistent component. The retained
context itself may be linear: only the supplied component has copy/discard. -/
structure RightCoaction (C D : τ) (cD : Quantity.relevant ≤ quantity D)
    (dD : Quantity.affine ≤ quantity D) where
  map : M.Hom C (product C D)
  pure : M.hasEffect ⊥ map
  coassoc : M.compose map (M.compose (M.right map D) (M.associator C D D)) =
    M.compose map (M.left C (M.copy D cD))
  counit : M.compose map (M.compose (M.left C (M.discard D dD)) (M.rightUnitor C)) = M.identity C

namespace RightCoaction
variable {M} {C D : τ} {cD : Quantity.relevant ≤ quantity D} {dD : Quantity.affine ≤ quantity D}
variable (j : M.RightCoaction C D cD dD)

/-- Extract the persistent component while retaining the state and context. -/
def action (A : τ) : M.Hom (product C A) (product C (product D A)) :=
  M.compose (M.right j.map A) (M.associator C D A)

theorem action_pure (A : τ) : M.hasEffect ⊥ (j.action A) :=
  M.compose_effect (M.right_effect A j.pure) (M.associator_pure C D A)

theorem action_natural {A B : τ} (f : M.Hom A B) :
    M.compose (j.action A) (M.left C (M.left D f)) =
      M.compose (M.left C f) (j.action B) := by
  dsimp [action]
  rw [M.compose_assoc, M.associator_natural_right, ← M.compose_assoc,
    M.exchange_left_pure j.map f j.pure, M.compose_assoc]

theorem action_duplicate (A : τ) :
    M.compose (j.action A)
      (M.left C (M.compose (M.right (M.copy D cD) A) (M.associator D D A))) =
    M.compose (j.action A) (j.action (product D A)) := by
  let C' : M.PureObject := ⟨C⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let jj : C' ⟶ C' ⊗ D' := ⟨j.map, j.pure⟩
  let cc : D' ⟶ D' ⊗ D' := ⟨M.copy D cD, M.copy_pure D cD⟩
  have hj : jj ≫ jj ▷ D' ≫ (α_ C' D' D').hom = jj ≫ C' ◁ cc := Subtype.ext j.coassoc
  have h := congrArg Subtype.val (Structural.coaction_duplicate jj cc hj A')
  change M.compose (M.right j.map A)
    (M.compose (M.associator C D A)
      (M.left C (M.compose (M.right (M.copy D cD) A) (M.associator D D A)))) =
    M.compose (M.right j.map A)
      (M.compose (M.associator C D A)
        (M.compose (M.right j.map (product D A)) (M.associator C D (product D A)))) at h
  simpa only [action, M.compose_assoc] using h

theorem action_counit (A : τ) :
    M.compose (j.action A)
      (M.left C (M.compose (M.right (M.discard D dD) A) (M.leftUnitor A))) =
      M.identity (product C A) := by
  let C' : M.PureObject := ⟨C⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let jj : C' ⟶ C' ⊗ D' := ⟨j.map, j.pure⟩
  let dd : D' ⟶ 𝟙_ M.PureObject := ⟨M.discard D dD, M.discard_pure D dD⟩
  have hj : jj ≫ C' ◁ dd ≫ (ρ_ C').hom = 𝟙 C' := Subtype.ext j.counit
  have h := congrArg Subtype.val (Structural.coaction_counit jj dd hj A')
  change M.compose (M.right j.map A)
    (M.compose (M.associator C D A)
      (M.left C (M.compose (M.right (M.discard D dD) A) (M.leftUnitor A)))) =
      M.identity (product C A) at h
  simpa only [action, M.compose_assoc] using h

end RightCoaction
end SeqData

namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε) {C D : τ}
variable {cD : Quantity.relevant ≤ quantity D} {dD : Quantity.affine ≤ quantity D}
variable (j : M.toSeqData.RightCoaction C D cD dD)

/-- Distributing a coaction through a loop exit removes only the supplied
persistent component and keeps the possibly linear retained context. -/
theorem coaction_exit {A B : τ} :
    M.compose (j.action (coprod B A))
      (M.compose (M.left C
        (M.compose (M.distribute D B A)
          (M.desc (M.compose (M.compose (M.right (M.discard D dD) B) (M.leftUnitor B))
              (M.inl B (product D A))) (M.inr B (product D A)))))
        (M.distribute C B (product D A))) =
      M.compose (M.distribute C B A)
        (M.desc (M.inl (product C B) (product C (product D A)))
          (M.compose (j.action A) (M.inr (product C B) (product C (product D A))))) := by
  let ex := M.compose (M.right (M.discard D dD) B) (M.leftUnitor B)
  let tl := M.compose (M.distribute D B A)
    (M.desc (M.compose ex (M.inl B (product D A))) (M.inr B (product D A)))
  have hl : M.compose (M.left D (M.inl B A)) tl = M.compose ex (M.inl B (product D A)) := by
    dsimp [tl]
    rw [← M.compose_assoc, M.toCaseData.left_inl_distribute, M.toCaseData.inl_desc]
  have hr : M.compose (M.left D (M.inr B A)) tl = M.inr B (product D A) := by
    dsimp [tl]
    rw [← M.compose_assoc, M.toCaseData.left_inr_distribute, M.toCaseData.inr_desc]
  change M.compose (j.action (coprod B A)) (M.compose (M.left C tl) (M.distribute C B (product D A))) = _
  apply M.toCaseData.distributed_hom_ext
  · rw [← M.compose_assoc, ← j.action_natural]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left C (M.left D (M.inl B A))), ← M.left_compose, hl,
      M.left_compose]
    simp only [M.compose_assoc]
    rw [M.toCaseData.left_inl_distribute, ← M.compose_assoc, j.action_counit, M.identity_compose,
      ← M.compose_assoc, M.toCaseData.left_inl_distribute, M.toCaseData.inl_desc]
  · rw [← M.compose_assoc, ← j.action_natural]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left C (M.left D (M.inr B A))), ← M.left_compose, hr,
      M.toCaseData.left_inr_distribute, ← M.compose_assoc, M.toCaseData.left_inr_distribute,
      M.toCaseData.inr_desc]

/-- A coaction supplies the same environment at every iteration step. -/
theorem coaction_contextStep {A B : τ} (f : M.Hom (product D A) (coprod B A)) :
    M.compose (j.action A)
      (M.compose (M.left C ((Denotation.ControlData.iter M).contextStep trivial D cD dD f))
        (M.distribute C B (product D A))) =
    M.compose
      (M.compose (j.action A) (M.compose (M.left C f) (M.distribute C B A)))
      (M.desc (M.inl (product C B) (product C (product D A)))
        (M.compose (j.action A) (M.inr (product C B) (product C (product D A))))) := by
  let cp := M.compose (M.right (M.copy D cD) A) (M.associator D D A)
  let tl := M.compose (M.distribute D B A)
    (M.desc (M.compose (M.compose (M.right (M.discard D dD) B) (M.leftUnitor B))
      (M.inl B (product D A))) (M.inr B (product D A)))
  have he : (Denotation.ControlData.iter M).contextStep trivial D cD dD f =
      M.compose cp (M.compose (M.left D f) tl) := by
    simp only [Denotation.ControlData.contextStep, Denotation.ControlData.iter,
      Denotation.ControlData.ofCase, cp, tl, M.compose_assoc]
  rw [he, M.left_compose C cp, M.left_compose C (M.left D f)]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (j.action A), j.action_duplicate]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (j.action (product D A)), j.action_natural]
  simp only [M.compose_assoc]
  rw [M.coaction_exit j]


/-- Iterating the supplied environment agrees with retaining the context
through the original contextual loop. -/
theorem coaction_iterate {A B : τ} (f : M.Hom (product D A) (coprod B A)) :
    M.compose (j.action A)
      (M.left C ((Denotation.ControlData.iter M).iterateWithContext trivial D cD dD f)) =
    M.iterate (M.compose (j.action A) (M.compose (M.left C f) (M.distribute C B A))) := by
  change M.compose (j.action A)
    (M.left C (M.iterate ((Denotation.ControlData.iter M).contextStep trivial D cD dD f))) = _
  rw [← M.strength]
  exact M.pure_uniformity (j.action_pure A) (M.coaction_contextStep j f)

end IterModel

end Silmaril.Isotope.Refinement.Models
