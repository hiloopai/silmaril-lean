module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationOutput
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationNaturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.CaseEquations

/-! # Simultaneous changes of loop environments, states, and outputs -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

/-- Distribution preserves maps in either summand, including effectful maps. -/
theorem distribute_map {D A B A' B' : τ} (a : M.Hom A A') (b : M.Hom B B') :
    M.compose (M.left D (M.desc (M.compose a (M.inl A' B')) (M.compose b (M.inr A' B'))))
      (M.distribute D A' B') =
    M.compose (M.distribute D A B)
      (M.desc (M.compose (M.left D a) (M.inl (product D A') (product D B')))
        (M.compose (M.left D b) (M.inr (product D A') (product D B')))) := by
  apply M.distributed_hom_ext
  · rw [← M.compose_assoc, ← M.left_compose, M.inl_desc, M.left_compose,
      M.compose_assoc, M.left_inl_distribute, ← M.compose_assoc,
      M.left_inl_distribute, M.inl_desc]
  · rw [← M.compose_assoc, ← M.left_compose, M.inr_desc, M.left_compose,
      M.compose_assoc, M.left_inr_distribute, ← M.compose_assoc,
      M.left_inr_distribute, M.inr_desc]

end CaseData

namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- Pure state simulation may change the result by an arbitrary continuation. -/
theorem pure_mixed_simulation {A A' B B' : τ}
    (h : M.Hom A A') (k : M.Hom B B')
    (f : M.Hom A (coprod B A)) (g : M.Hom A' (coprod B' A'))
    (hh : M.hasEffect ⊥ h)
    (hs : M.compose h g =
      M.compose f (M.desc (M.compose k (M.inl B' A')) (M.compose h (M.inr B' A')))) :
    M.compose h (M.iterate g) = M.compose (M.iterate f) k := by
  rw [M.output_naturality]
  apply M.pure_uniformity hh
  rw [M.compose_assoc, M.toCaseData.desc_compose]
  simpa only [M.compose_assoc, M.toCaseData.inl_desc, M.toCaseData.inr_desc] using hs

/-- Forgetting a persistent environment commutes with computation on the output. -/
theorem exit_natural {D B B' : τ} (dD : Quantity.affine ≤ quantity D) (b : M.Hom B B') :
    M.compose (M.left D b) (M.compose (M.right (M.discard D dD) B') (M.leftUnitor B')) =
    M.compose (M.compose (M.right (M.discard D dD) B) (M.leftUnitor B)) b := by
  rw [← M.compose_assoc, ← M.toSeqData.exchange_left_pure _ _ (M.toSeqData.discard_pure D dD)]
  rw [M.compose_assoc, M.toSeqData.leftUnitor_natural, ← M.compose_assoc]

/-- Copying the persistent environment is natural in the state argument. -/
theorem copy_state_natural {D A A' : τ} (cD : Quantity.relevant ≤ quantity D) (a : M.Hom A A') :
    M.compose (M.left D a)
      (M.compose (M.right (M.copy D cD) A') (M.associator D D A')) =
    M.compose (M.compose (M.right (M.copy D cD) A) (M.associator D D A))
      (M.left D (M.left D a)) := by
  rw [← M.compose_assoc, ← M.toSeqData.exchange_left_pure _ _ (M.toSeqData.copy_pure D cD)]
  rw [M.compose_assoc, ← M.toSeqData.associator_natural_right, ← M.compose_assoc]

/-- A state/output comparison of bodies induces a comparison of their explicit
machines with persistent environments. -/
theorem contextStep_state_output {D A A' B B' : τ}
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (a : M.Hom A A') (b : M.Hom B B')
    (f : M.Hom (product D A) (coprod B A))
    (g : M.Hom (product D A') (coprod B' A'))
    (hs : M.compose (M.left D a) g =
      M.compose f (M.desc (M.compose b (M.inl B' A')) (M.compose a (M.inr B' A')))) :
    M.compose (M.left D a) ((ControlData.iter M).contextStep trivial D cD dD g) =
    M.compose ((ControlData.iter M).contextStep trivial D cD dD f)
      (M.desc (M.compose b (M.inl B' (product D A')))
        (M.compose (M.left D a) (M.inr B' (product D A')))) := by
  let exitB := M.compose (M.right (M.discard D dD) B) (M.leftUnitor B)
  let exitB' := M.compose (M.right (M.discard D dD) B') (M.leftUnitor B')
  let transfer := M.desc (M.compose b (M.inl B' (product D A')))
    (M.compose (M.left D a) (M.inr B' (product D A')))
  have he : M.compose
      (M.desc (M.compose (M.left D b) (M.inl (product D B') (product D A')))
        (M.compose (M.left D a) (M.inr (product D B') (product D A'))))
      (M.desc (M.compose exitB' (M.inl B' (product D A'))) (M.inr B' (product D A'))) =
      M.compose (M.desc (M.compose exitB (M.inl B (product D A))) (M.inr B (product D A))) transfer := by
    rw [M.toCaseData.desc_compose, M.toCaseData.desc_compose]
    simp only [M.compose_assoc, transfer, M.toCaseData.inl_desc, M.toCaseData.inr_desc]
    rw [← M.compose_assoc (M.left D b) exitB', M.exit_natural dD b]
    rw [M.compose_assoc]
  simp only [ControlData.contextStep, ControlData.iter, ControlData.ofCase]
  rw [← M.compose_assoc (M.right (M.discard D dD) B) (M.leftUnitor B),
    ← M.compose_assoc (M.right (M.discard D dD) B') (M.leftUnitor B')]
  change M.compose (M.left D a)
    (M.compose (M.right (M.copy D cD) A')
      (M.compose (M.associator D D A')
        (M.compose (M.left D g)
          (M.compose (M.distribute D B' A')
            (M.desc (M.compose exitB' (M.inl B' (product D A'))) (M.inr B' (product D A'))))))) =
    M.compose (M.compose (M.right (M.copy D cD) A)
      (M.compose (M.associator D D A)
        (M.compose (M.left D f)
          (M.compose (M.distribute D B A)
            (M.desc (M.compose exitB (M.inl B (product D A))) (M.inr B (product D A))))))) transfer
  rw [← M.compose_assoc (M.right (M.copy D cD) A') (M.associator D D A'),
    ← M.compose_assoc (M.left D a), M.copy_state_natural cD a]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.left D (M.left D a)) (M.left D g), ← M.left_compose, hs, M.left_compose]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.left D (M.desc _ _)) (M.distribute D B' A'), M.toCaseData.distribute_map]
  simp only [M.compose_assoc]
  rw [he]

/-- Contextual iteration respects a pure state comparison and any output map. -/
theorem iterateWithContext_state_output {D A A' B B' : τ}
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (a : M.Hom A A') (b : M.Hom B B') (ha : M.hasEffect ⊥ a)
    (f : M.Hom (product D A) (coprod B A))
    (g : M.Hom (product D A') (coprod B' A'))
    (hs : M.compose (M.left D a) g =
      M.compose f (M.desc (M.compose b (M.inl B' A')) (M.compose a (M.inr B' A')))) :
    M.compose (M.left D a) ((ControlData.iter M).iterateWithContext trivial D cD dD g) =
      M.compose ((ControlData.iter M).iterateWithContext trivial D cD dD f) b :=
  M.pure_mixed_simulation (M.left D a) b
    ((ControlData.iter M).contextStep trivial D cD dD f)
    ((ControlData.iter M).contextStep trivial D cD dD g)
    (M.toSeqData.left_effect D ha) (M.contextStep_state_output cD dD a b f g hs)

/-- Simultaneous environment and state comparison preserves iteration, with
an arbitrary result continuation. All copy/discard compatibility follows from purity. -/
theorem iterateWithContext_simulation {D E A A' B B' : τ}
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (cE : Quantity.relevant ≤ quantity E) (dE : Quantity.affine ≤ quantity E)
    (u : M.Hom D E) (a : M.Hom A A') (b : M.Hom B B')
    (hu : M.hasEffect ⊥ u) (ha : M.hasEffect ⊥ a)
    (f : M.Hom (product D A) (coprod B A))
    (g : M.Hom (product E A') (coprod B' A'))
    (hs : M.compose (M.tensor u a) g =
      M.compose f (M.desc (M.compose b (M.inl B' A')) (M.compose a (M.inr B' A')))) :
    M.compose (M.tensor u a) ((ControlData.iter M).iterateWithContext trivial E cE dE g) =
      M.compose ((ControlData.iter M).iterateWithContext trivial D cD dD f) b := by
  have ht : M.tensor u a = M.compose (M.left D a) (M.right u A') :=
    M.toSeqData.exchange_left_pure u a hu
  rw [ht, M.compose_assoc, M.iterateWithContext_natural u hu cD dD cE dE g]
  apply M.iterateWithContext_state_output cD dD a b ha f
  simpa only [← M.compose_assoc, ← ht] using hs

end IterModel
end Silmaril.Isotope.Refinement.Models
