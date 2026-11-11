module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-!
# Determinism of lambda-SSA evaluation (proofs)

Restated in `Silmaril.SSA.Isotope.LambdaSSA.Thms`.
-/

@[expose] public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- Term evaluation is deterministic, by simultaneous recursion on the two derivations:
both follow the same constructor of the term, and the instruction relation and the
induction hypotheses identify the intermediate values and states. -/
theorem Tm.Eval.deterministic (hd : InstrDeterministic instr)
    {env : Env α} {t : LambdaSSA.Tm Φ} {s s₁ s₂ : σ} {v₁ v₂ : Value α}
    (h : Tm.Eval instr env t s v₁ s₁) (h' : Tm.Eval instr env t s v₂ s₂) :
    v₁ = v₂ ∧ s₁ = s₂ :=
  match h, h' with
  | .var, .var => ⟨rfl, rfl⟩
  | .unit, .unit => ⟨rfl, rfl⟩
  | .op a step, .op a' step' => by
      obtain ⟨rfl, rfl⟩ := deterministic hd a a'
      exact hd _ _ _ _ _ _ _ step step'
  | .let₁ a b, .let₁ a' b' => by
      obtain ⟨rfl, rfl⟩ := deterministic hd a a'
      exact deterministic hd b b'
  | .pair a b, .pair a' b' => by
      obtain ⟨rfl, rfl⟩ := deterministic hd a a'
      obtain ⟨rfl, rfl⟩ := deterministic hd b b'
      exact ⟨rfl, rfl⟩
  | .let₂ a b, .let₂ a' b' => by
      obtain ⟨hv, rfl⟩ := deterministic hd a a'
      obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
      exact deterministic hd b b'
  | .inl a, .inl a' => by
      obtain ⟨rfl, rfl⟩ := deterministic hd a a'
      exact ⟨rfl, rfl⟩
  | .inr a, .inr a' => by
      obtain ⟨rfl, rfl⟩ := deterministic hd a a'
      exact ⟨rfl, rfl⟩
  | .case_inl a l, .case_inl a' l' => by
      obtain ⟨hv, rfl⟩ := deterministic hd a a'
      cases Value.inl.inj hv
      exact deterministic hd l l'
  | .case_inr a r, .case_inr a' r' => by
      obtain ⟨hv, rfl⟩ := deterministic hd a a'
      cases Value.inr.inj hv
      exact deterministic hd r r'
  | .case_inl a _, .case_inr a' _ =>
      nomatch (deterministic hd a a').1
  | .case_inr a _, .case_inl a' _ =>
      nomatch (deterministic hd a a').1

mutual

/-- Region evaluation is deterministic: the exit label, its argument and the final state
are unique. Mutually recursive with `Region.Follow.deterministic`. -/
theorem Region.Eval.deterministic (hd : InstrDeterministic instr)
    {env : Env α} {r : LambdaSSA.Region Φ} {s s₁ s₂ : σ} {l₁ l₂ : Nat} {v₁ v₂ : Value α}
    (h : Region.Eval instr env r s l₁ v₁ s₁) (h' : Region.Eval instr env r s l₂ v₂ s₂) :
    l₁ = l₂ ∧ v₁ = v₂ ∧ s₁ = s₂ :=
  match h, h' with
  | .br a, .br a' => ⟨rfl, Tm.Eval.deterministic hd a a'⟩
  | .let₁ a b, .let₁ a' b' => by
      obtain ⟨rfl, rfl⟩ := Tm.Eval.deterministic hd a a'
      exact Region.Eval.deterministic hd b b'
  | .let₂ a b, .let₂ a' b' => by
      obtain ⟨hv, rfl⟩ := Tm.Eval.deterministic hd a a'
      obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
      exact Region.Eval.deterministic hd b b'
  | .case_inl a l, .case_inl a' l' => by
      obtain ⟨hv, rfl⟩ := Tm.Eval.deterministic hd a a'
      cases Value.inl.inj hv
      exact Region.Eval.deterministic hd l l'
  | .case_inr a r, .case_inr a' r' => by
      obtain ⟨hv, rfl⟩ := Tm.Eval.deterministic hd a a'
      cases Value.inr.inj hv
      exact Region.Eval.deterministic hd r r'
  | .case_inl a _, .case_inr a' _ =>
      nomatch (Tm.Eval.deterministic hd a a').1
  | .case_inr a _, .case_inl a' _ =>
      nomatch (Tm.Eval.deterministic hd a a').1
  | .cfg entry follow, .cfg entry' follow' => by
      obtain ⟨rfl, rfl, rfl⟩ := Region.Eval.deterministic hd entry entry'
      exact Region.Follow.deterministic hd follow follow'

/-- Following the internal transfers of a CFG is deterministic. -/
theorem Region.Follow.deterministic (hd : InstrDeterministic instr)
    {env : Env α} {n first l₁ l₂ : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
    {initial v₁ v₂ : Value α} {s s₁ s₂ : σ}
    (h : Region.Follow instr env blocks first initial s l₁ v₁ s₁)
    (h' : Region.Follow instr env blocks first initial s l₂ v₂ s₂) :
    l₁ = l₂ ∧ v₁ = v₂ ∧ s₁ = s₂ :=
  match h, h' with
  | .exit _, .exit _ => ⟨rfl, rfl, rfl⟩
  | .exit outside, .step inside _ _ =>
      absurd inside (Nat.not_lt_of_ge outside)
  | .step inside _ _, .exit outside =>
      absurd inside (Nat.not_lt_of_ge outside)
  | .step _ head tail, .step _ head' tail' => by
      obtain ⟨rfl, rfl, rfl⟩ := Region.Eval.deterministic hd head head'
      exact Region.Follow.deterministic hd tail tail'

end

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics

end
