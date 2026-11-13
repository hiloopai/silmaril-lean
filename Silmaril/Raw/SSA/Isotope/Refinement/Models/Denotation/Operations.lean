module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Control
public import Silmaril.Raw.SSA.Isotope.Refinement.Typing

/-! # Shared interpretation operations for the three grammatical fragments

These data factor the constructor interpretation. They are obtained from the
actual categorical models; no semantic equations or initiality assumptions are
introduced by this auxiliary interface.
-/

@[expose] public section
noncomputable section

universe u v w r

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ]
variable {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Distribute a retained context into either branch, using the model's chosen
pure distributivity isomorphism and the signature's type constructors. -/
def CaseData.distribute (M : CaseData.{u,v,w,r} τ Φ ε) (D A B : τ) :
    M.toSeqData.Hom (product D (coprod A B)) (coprod (product D A) (product D B)) := by
  letI := M.toSeqData.category
  letI := M.toSeqData.homOrder
  letI := M.toSeqData.premonoidal
  letI := M.toSeqData.symmetric
  letI := M.caseLaws.distributor_isIso D A B
  exact eqToHom (by rw [M.tensor_obj, M.sum_obj]) ≫
    inv (M.coproducts.distributor D A B) ≫
    eqToHom (by rw [M.sum_obj, M.tensor_obj, M.tensor_obj])

namespace Denotation

/-- Optional control operations are available precisely when the grammar allows
using them. Sequential interpretation requires neither sums nor iteration. -/
structure ControlData (M : SeqData.{u,v,w,r} τ Φ ε) (F : Fragment) where
  inl : F.HasCase → ∀ A B : τ, M.Hom A (coprod A B)
  inr : F.HasCase → ∀ A B : τ, M.Hom B (coprod A B)
  desc : F.HasCase → ∀ {A B D : τ}, M.Hom A D → M.Hom B D → M.Hom (coprod A B) D
  abort : F.HasCase → ∀ A : τ, M.Hom Silmaril.empty A
  distribute : F.HasCase → ∀ D A B : τ,
    M.Hom (product D (coprod A B)) (coprod (product D A) (product D B))
  iterate : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B

namespace ControlData

variable {M : SeqData.{u,v,w,r} τ Φ ε} {F : Fragment}

/-- One step carrying an unrestricted environment. A copy feeds the body;
the retained environment is discarded only on the exit branch. -/
def contextStep (K : ControlData M F) (h : F.HasCase) (D : τ)
    (copyable : Quantity.relevant ≤ quantity D) (discardable : Quantity.affine ≤ quantity D)
    {A B : τ} (body : M.Hom (product D A) (coprod B A)) :
    M.Hom (product D A) (coprod B (product D A)) :=
    M.compose (M.right (M.copy D copyable) A)
      (M.compose (M.associator D D A)
        (M.compose (M.left D body)
          (M.compose (K.distribute h D B A)
            (K.desc h
              (M.compose (M.right (M.discard D discardable) B)
                (M.compose (M.leftUnitor B) (K.inl h B (product D A))))
              (K.inr h B (product D A))))))

/-- Iterate the contextual step, retaining the environment until the loop exits. -/
def iterateWithContext (K : ControlData M F) (h : F.HasIter) (D : τ)
    (copyable : Quantity.relevant ≤ quantity D) (discardable : Quantity.affine ≤ quantity D)
    {A B : τ} (body : M.Hom (product D A) (coprod B A)) :
    M.Hom (product D A) B := by
  have hc : F.HasCase := by cases F <;> first | exact h | trivial
  exact K.iterate h (K.contextStep hc D copyable discardable body)

/-- The empty control interface of a sequential model. -/
def seq (M : SeqModel.{u,v,w,r} τ Φ ε) : ControlData M.toSeqData .seq where
  inl h := False.elim h
  inr h := False.elim h
  desc h := False.elim h
  abort h := False.elim h
  distribute h := False.elim h
  iterate h := False.elim h

/-- Common case operations; the caller supplies only the grammatical iteration capability. -/
def ofCase (M : CaseData.{u,v,w,r} τ Φ ε) (F : Fragment)
    (iterate : F.HasIter → ∀ {A B : τ},
      M.toSeqData.Hom A (coprod B A) → M.toSeqData.Hom A B) :
    ControlData M.toSeqData F where
  inl _ := M.inl
  inr _ := M.inr
  desc _ := M.desc
  abort _ := M.abort
  distribute _ := M.distribute
  iterate := iterate

/-- The native branching model supplies no loop operator. -/
def case (M : CaseModel.{u,v,w,r} τ Φ ε) : ControlData M.toSeqData .case :=
  ofCase M.toCaseData .case (fun h => False.elim h)

/-- All control constructors are interpreted by the iterative model. -/
def iter (M : IterModel.{u,v,w,r} τ Φ ε) : ControlData M.toSeqData .iter :=
  ofCase M.toCaseData .iter (fun _ => M.iterate)

end ControlData
end Denotation
end Silmaril.Isotope.Refinement.Models
