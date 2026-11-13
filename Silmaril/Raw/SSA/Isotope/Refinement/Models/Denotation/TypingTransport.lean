module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Typing
public import Silmaril.Raw.SSA.Isotope.Refinement.TypingRestriction

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)
/-- Reindex an arrow by an equality of its source type. -/
def castInput {A B C : τ} (he : A = B) (f : M.Hom A C) : M.Hom B C := he ▸ f
@[simp] theorem castInput_refl {A C : τ} (he : A = A) (f : M.Hom A C) : M.castInput he f = f := rfl
end SeqData

namespace Denotation
variable (M : SeqData.{u,v,w,r} τ Φ ε) {F : Fragment} (K : ControlData M F)

/-- The categorical fold transports only the packed source when a native
derivation is reindexed along equality of quantitative contexts. -/
@[simp] theorem denote_castContext {n : Nat} {Γ Δ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (he : Γ = Δ) :
    denote M K (h.castContext he) = M.castInput (congrArg packed he) (denote M K h) := by
  cases he
  rfl

/-- Reindexing contexts does not change the interpreted arrow, accounting for
its dependent source object. -/
theorem denote_castContext_heq {n : Nat} {Γ Δ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType F Γ e t A) (he : Γ = Δ) :
    HEq (denote M K (h.castContext he)) (denote M K h) := by
  cases he
  rfl

/-- The binder-context transport has definitionally equal packed objects. -/
@[simp] theorem denote_restrict_snoc_cast {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ (n+1)} {A B : τ} {q : Usage} {p : Fin n → Bool}
    (h : HasType F (QCtx.restrict (Γ.snoc A q) (Fin.cases true p)) e t B) :
    denote M K (h.castContext (Δ := (QCtx.restrict Γ p).snoc A q)
      (QCtx.restrict_snoc_true Γ A q p)) =
      denote M K (Γ := QCtx.restrict (Γ.snoc A q) (Fin.cases true p)) h := by
  rw [denote_castContext]
  rfl

end Denotation
end Silmaril.Isotope.Refinement.Models
