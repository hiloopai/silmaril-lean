module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationSimulation

/-! # The explicit body of iteration naturality

The persistent context contains the continuation's environment and the loop's
environment. Only the continuation environment is discarded on a recursive
step; on an exit it is consumed by the arbitrary continuation.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.IterModel
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- The body obtained by pushing an effectful continuation into a loop. -/
def naturalityBody {E D A B C : τ} (dE : Quantity.affine ≤ quantity E)
    (f : M.Hom (product D A) (coprod B A)) (g : M.Hom (product E B) C) :
    M.Hom (product (product E D) A) (coprod C A) :=
  M.compose (M.associator E D A)
    (M.compose (M.left E f)
      (M.compose (M.distribute E B A)
        (M.desc (M.compose g (M.inl C A))
          (M.compose (M.compose (M.right (M.discard E dE) A) (M.leftUnitor A)) (M.inr C A)))))

end Silmaril.Isotope.Refinement.Models.IterModel
