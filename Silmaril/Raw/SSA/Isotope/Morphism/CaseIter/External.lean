module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Operational
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External

/-! The finite-syntax external-divergence judgment agrees with the existing
coinductive LetIter model. Loop-free syntax cannot introduce internal divergence. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.CaseIter

open LetCase.LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {prim : Φ → Value α → σ → Prop} {free : ν → Value α}

theorem embed_diverges {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s : σ}
    (h : LetCase.Semantics.External.Diverges instr prim free bound t s) :
    LetIter.Semantics.External.Diverges instr free prim (.term bound (embed t) s) := by
  induction h with
  | op_arg _ ih => exact .fold (.core (.op ih))
  | primitive arg div => exact .primitive (embed_eval arg) div
  | let₁_arg _ ih => exact .fold (.core (.let₁_arg ih))
  | let₁_body arg _ ih => exact .fold (.core (.let₁_body (embed_eval arg) ih))
  | pair_left _ ih => exact .fold (.core (.pair_left ih))
  | pair_right arg _ ih => exact .fold (.core (.pair_right (embed_eval arg) ih))
  | let₂_arg _ ih => exact .fold (.core (.let₂_arg ih))
  | let₂_body arg _ ih => exact .fold (.core (.let₂_body (embed_eval arg) ih))
  | inl _ ih => exact .fold (.core (.inl ih))
  | inr _ ih => exact .fold (.core (.inr ih))
  | case_arg _ ih => exact .fold (.core (.case_scrutinee ih))
  | case_inl arg _ ih => exact .fold (.core (.case_inl (embed_eval arg) ih))
  | case_inr arg _ ih => exact .fold (.core (.case_inr (embed_eval arg) ih))
  | abort_arg _ ih => exact .fold (.core (.abort ih))

theorem of_embed_diverges {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s : σ}
    (h : LetIter.Semantics.External.Diverges instr free prim (.term bound (embed t) s)) :
    LetCase.Semantics.External.Diverges instr prim free bound t s := by
  induction t generalizing s with
  | fv x => cases h.unfold with | core h => cases h
  | bv i => cases h.unfold with | core h => cases h
  | unit => cases h.unfold with | core h => cases h
  | op f a ih =>
      cases h.unfold with
      | primitive arg div => exact .primitive (of_embed_eval arg) div
      | core h => cases h with | op arg => exact .op_arg (ih arg)
  | let₁ a b ihArg ihBody =>
      cases h.unfold with
      | core h => cases h with
        | let₁_arg arg => exact .let₁_arg (ihArg arg)
        | let₁_body arg body => exact .let₁_body (of_embed_eval arg) (ihBody body)
  | pair a b ihLeft ihRight =>
      cases h.unfold with
      | core h => cases h with
        | pair_left arg => exact .pair_left (ihLeft arg)
        | pair_right left right => exact .pair_right (of_embed_eval left) (ihRight right)
  | let₂ a b ihArg ihBody =>
      cases h.unfold with
      | core h => cases h with
        | let₂_arg arg => exact .let₂_arg (ihArg arg)
        | let₂_body arg body => exact .let₂_body (of_embed_eval arg) (ihBody body)
  | inl a ih => cases h.unfold with
      | core h => cases h with | inl arg => exact .inl (ih arg)
  | inr a ih => cases h.unfold with
      | core h => cases h with | inr arg => exact .inr (ih arg)
  | case e l r ihArg ihLeft ihRight =>
      cases h.unfold with
      | core h => cases h with
        | case_scrutinee arg => exact .case_arg (ihArg arg)
        | case_inl arg branch => exact .case_inl (of_embed_eval arg) (ihLeft branch)
        | case_inr arg branch => exact .case_inr (of_embed_eval arg) (ihRight branch)
  | abort a ih => cases h.unfold with
      | core h => cases h with | abort arg => exact .abort_arg (ih arg)

@[simp] theorem embed_diverges_iff {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s : σ} :
    LetIter.Semantics.External.Diverges instr free prim (.term bound (embed t) s) ↔
      LetCase.Semantics.External.Diverges instr prim free bound t s :=
  ⟨of_embed_diverges, embed_diverges⟩

/-- Even partial or nondeterministic instructions cannot make loop-free syntax
internally divergent: primitive divergence must be supplied explicitly. -/
theorem embed_not_internal_diverges {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s : σ} :
    ¬ LetIter.Semantics.Diverges instr free (.term bound (embed t) s) := by
  intro h
  exact LetCase.Semantics.External.Diverges.false
    (of_embed_diverges (LetIter.Semantics.External.Diverges.of_internal
      (prim := fun _ _ _ => False) h))

end Silmaril.Isotope.Morphism.CaseIter

