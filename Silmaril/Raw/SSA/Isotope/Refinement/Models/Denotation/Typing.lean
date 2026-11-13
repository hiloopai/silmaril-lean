module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Operations
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Contexts
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Algebra

/-! # Categorical interpretation of quantitative typing

Context packing and the optional control interface give a single constructor
algebra for all three fragments. Interpretation reuses the proved free-algebra
fold, so preservation of constructor operations and uniqueness are shared with
the general model development.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ]
variable {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε) {F : Fragment}

/-- The actual categorical constructor operations, with quantity-valid context
splitting and copying/discarding of the persistent loop environment. -/
def algebra (K : ControlData M F) : Algebra (signature (τ := τ) Φ F) where
  Carrier i := M.Hom (packed i.context) i.result
  op o args := by
    cases o with
    | var i h => exact «variable» M i h
    | op f => exact M.compose (args 0) (M.instruction f)
    | let₁ A B s => exact M.compose (split M s) (M.compose (M.left _ (args 0)) (args 1))
    | unit h => exact discard M h
    | pair A B s => exact M.compose (split M s) (M.tensor (args 0) (args 1))
    | let₂ A B C s =>
      exact M.compose (split M s)
        (M.compose (M.left _ (args 0)) (M.compose (M.associatorInv _ A B) (args 1)))
    | inl A B h => exact M.compose (args 0) (K.inl h A B)
    | inr A B h => exact M.compose (args 0) (K.inr h A B)
    | case A B C h s =>
      exact M.compose (split M s)
        (M.compose (M.left _ (args 0))
          (M.compose (K.distribute h _ A B) (K.desc h (args 1) (args 2))))
    | abort A h => exact M.compose (args 0) (K.abort h A)
    | iter A B h s hu =>
      have ht := hu ▸ packed_quantity _
      exact M.compose (split M s)
        (M.compose (M.left _ (args 0))
          (K.iterateWithContext h _ (le_trans le_top ht) (le_trans le_top ht) (args 1)))

/-- Interpret any effect-specific native typing derivation in the categorical
constructor algebra; effect proofs do not change its operations. -/
def denote (K : ControlData M F) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType F Γ e t A) : M.Hom (packed Γ) A :=
  Models.denote (algebra M K) h

/-- The unique constructor-preserving interpretation of top-effect derivations. -/
def fold (K : ControlData M F) : Algebra.Hom (syntaxAlgebra (τ := τ) Φ ε F) (algebra M K) :=
  Models.fold (algebra M K)

theorem fold_unique (K : ControlData M F) (f : Algebra.Hom (syntaxAlgebra (τ := τ) Φ ε F) (algebra M K)) :
    f = fold M K := Models.fold_unique (algebra M K) f

/-- Native sequential interpretation needs only the sequential model structure. -/
def denoteSeq (M : SeqModel.{u,v,w,r} τ Φ ε) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .seq Γ e t A) : M.toSeqData.Hom (packed Γ) A :=
  denote M.toSeqData (ControlData.seq M) h

def denoteCase (M : CaseModel.{u,v,w,r} τ Φ ε) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .case Γ e t A) : M.toSeqData.Hom (packed Γ) A :=
  denote M.toSeqData (ControlData.case M) h

def denoteIter (M : IterModel.{u,v,w,r} τ Φ ε) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .iter Γ e t A) : M.toSeqData.Hom (packed Γ) A :=
  denote M.toSeqData (ControlData.iter M) h

end Silmaril.Isotope.Refinement.Models.Denotation
