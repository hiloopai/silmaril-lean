module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Operational
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault

/-! Exact fault agreement for the calculus inclusion. Successful prefixes and
final fault states are preserved, with arbitrary primitive relations. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.CaseIter

open LetCase.LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : ν → Value α}

theorem embed_fault {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s s' : σ}
    (h : LetCase.Semantics.Fault instr faults free bound t s s') :
    LetIter.Semantics.Fault instr faults free bound (embed t) s s' := by
  induction h with
  | op_arg _ ih => exact .op_arg ih
  | op_fault arg fault => exact .op_fault (embed_eval arg) fault
  | let₁_arg _ ih => exact .let₁_arg ih
  | let₁_body arg _ ih => exact .let₁_body (embed_eval arg) ih
  | pair_left _ ih => exact .pair_left ih
  | pair_right arg _ ih => exact .pair_right (embed_eval arg) ih
  | let₂_arg _ ih => exact .let₂_arg ih
  | let₂_body arg _ ih => exact .let₂_body (embed_eval arg) ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case_arg _ ih => exact .case_arg ih
  | case_inl arg _ ih => exact .case_inl (embed_eval arg) ih
  | case_inr arg _ ih => exact .case_inr (embed_eval arg) ih
  | abort_arg _ ih => exact .abort_arg ih

theorem of_embed_fault {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s s' : σ}
    (h : LetIter.Semantics.Fault instr faults free bound (embed t) s s') :
    LetCase.Semantics.Fault instr faults free bound t s s' := by
  induction t generalizing s s' with
  | fv x => cases h
  | bv i => cases h
  | unit => cases h
  | op f a ih =>
      cases h with
      | op_arg arg => exact .op_arg (ih arg)
      | op_fault arg fault => exact .op_fault (of_embed_eval arg) fault
  | let₁ a b ihArg ihBody =>
      cases h with
      | let₁_arg arg => exact .let₁_arg (ihArg arg)
      | let₁_body arg body => exact .let₁_body (of_embed_eval arg) (ihBody body)
  | pair a b ihLeft ihRight =>
      cases h with
      | pair_left arg => exact .pair_left (ihLeft arg)
      | pair_right left right => exact .pair_right (of_embed_eval left) (ihRight right)
  | let₂ a b ihArg ihBody =>
      cases h with
      | let₂_arg arg => exact .let₂_arg (ihArg arg)
      | let₂_body arg body => exact .let₂_body (of_embed_eval arg) (ihBody body)
  | inl a ih => cases h with | inl arg => exact .inl (ih arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih arg)
  | case e l r ihArg ihLeft ihRight =>
      cases h with
      | case_arg arg => exact .case_arg (ihArg arg)
      | case_inl arg branch => exact .case_inl (of_embed_eval arg) (ihLeft branch)
      | case_inr arg branch => exact .case_inr (of_embed_eval arg) (ihRight branch)
  | abort a ih => cases h with | abort_arg arg => exact .abort_arg (ih arg)

@[simp] theorem embed_fault_iff {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n} {s s' : σ} :
    LetIter.Semantics.Fault instr faults free bound (embed t) s s' ↔
      LetCase.Semantics.Fault instr faults free bound t s s' :=
  ⟨of_embed_fault, embed_fault⟩

end Silmaril.Isotope.Morphism.CaseIter

