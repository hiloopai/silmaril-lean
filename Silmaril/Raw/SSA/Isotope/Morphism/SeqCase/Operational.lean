module

public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase
public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Operational
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Operational

/-! Operational agreement for the constructor-preserving LetSeq to LetCase inclusion.
Both judgments are independently defined. The primitive relation and all input
environments are arbitrary; no determinism, totality, typing or purity is assumed. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.SeqCase

open LetSeq.LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : ν → Value α}

/-- Inclusion preserves the result and complete threaded state. -/
theorem embed_eval {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α}
    (h : LetSeq.Semantics.Eval instr free bound t s value s') :
    LetCase.Semantics.Eval instr free bound (embed t) s value s' := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op _ step ih => exact .op ih step
  | let₁ _ _ ihArg ihBody => exact .let₁ ihArg ihBody
  | unit => exact .unit
  | pair _ _ ihLeft ihRight => exact .pair ihLeft ihRight
  | let₂ _ _ ihArg ihBody => exact .let₂ ihArg ihBody

/-- The larger calculus adds no new finite outcomes to an included term. -/
theorem of_embed_eval {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α}
    (h : LetCase.Semantics.Eval instr free bound (embed t) s value s') :
    LetSeq.Semantics.Eval instr free bound t s value s' := by
  induction t generalizing s s' value with
  | fv x => cases h; exact .fv
  | bv i => cases h; exact .bv
  | op f a ih => cases h with | op arg step => exact .op (ih arg) step
  | let₁ a b ihArg ihBody =>
      cases h with | let₁ arg body => exact .let₁ (ihArg arg) (ihBody body)
  | unit => cases h; exact .unit
  | pair a b ihLeft ihRight =>
      cases h with | pair left right => exact .pair (ihLeft left) (ihRight right)
  | let₂ a b ihArg ihBody =>
      cases h with | let₂ arg body => exact .let₂ (ihArg arg) (ihBody body)

@[simp] theorem embed_eval_iff {n : Nat} {bound : Fin n → Value α} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α} :
    LetCase.Semantics.Eval instr free bound (embed t) s value s' ↔
      LetSeq.Semantics.Eval instr free bound t s value s' :=
  ⟨of_embed_eval, embed_eval⟩

@[simp] theorem embed_terminates_iff {n : Nat} {bound : Fin n → Value α}
    {t : Tm ν Φ n} {s : σ} :
    LetCase.Semantics.Terminates instr free bound (embed t) s ↔
      LetSeq.Semantics.Terminates instr free bound t s := by
  simp only [LetCase.Semantics.Terminates, LetSeq.Semantics.Terminates, embed_eval_iff]

@[simp] theorem embed_noResult_iff {n : Nat} {bound : Fin n → Value α}
    {t : Tm ν Φ n} {s : σ} :
    LetCase.Semantics.NoResult instr free bound (embed t) s ↔
      LetSeq.Semantics.NoResult instr free bound t s := by
  simp only [LetCase.Semantics.NoResult, LetSeq.Semantics.NoResult, embed_terminates_iff]

end Silmaril.Isotope.Morphism.SeqCase

