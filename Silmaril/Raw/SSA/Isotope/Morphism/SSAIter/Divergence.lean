module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Correctness
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Divergence

/-!
# Divergence preservation for finite CFG encoding

Flat regions cannot themselves make infinitely many control transfers. An
infinite graph execution therefore gives infinitely many internal block steps,
which the encoding reproduces as iteration steps with the same machine states.
No instruction determinism or totality assumption is used.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w} {n labels : Nat}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv Empty α}

/-- A flat region has finitely many control constructs; primitive instructions
are atomic transitions, so failure to execute one is stuckness rather than divergence. -/
theorem flat_not_diverges (r : LambdaSSA.Flat Φ labels n)
    (env : LambdaSSA.Semantics.Env α) (s : σ) :
    ¬ LambdaSSA.Semantics.Diverges instr (.region env r.erase s) := by
  induction r generalizing env s with
  | br => intro h; cases h.unfold
  | let₁ a b ih =>
      intro h
      cases h.unfold with | let₁ _ rest => exact ih _ _ rest
  | let₂ a b ih =>
      intro h
      cases h.unfold with | let₂ _ rest => exact ih _ _ rest
  | case e l r ihl ihr =>
      intro h
      cases h.unfold with
      | case_inl _ rest => exact ihl _ _ rest
      | case_inr _ rest => exact ihr _ _ rest

/-- Infinite following must start at an internal label, since external labels return. -/
theorem follow_diverges_inside {blocks first : Nat} {env : LambdaSSA.Semantics.Env α}
    {bs : Fin blocks → LambdaSSA.Region Φ} {current : Value α} {s : σ}
    (h : LambdaSSA.Semantics.Diverges instr (.follow env bs first current s)) : first < blocks := by
  cases h.unfold with
  | follow_body inside _ | follow_next inside _ _ => exact inside

/-- Infinite internal transfers become an infinite loop. The extra captured
value is the initial state retained by the surrounding entry-case branch. -/
theorem follow_diverges_loop {blocks exits captured : Nat}
    {g : LambdaSSA.FiniteCFG Φ blocks exits captured} {i : Fin blocks}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α captured}
    {current : Value α} {s : σ} (agree : CaseSSA.EnvAgrees env bound) (extra : Value α)
    (h : LambdaSSA.Semantics.Diverges instr
      (.follow env (fun j => (g.block j).erase) i.val current s)) :
    Diverges instr free (.loop (extend bound extra) (loopBody g).underBinder
      (tagValue i current) s) := by
  let R : Config α Empty Φ σ → Prop := fun c =>
    ∃ (j : Fin blocks) (value : Value α) (state : σ),
      c = .loop (extend bound extra) (loopBody g).underBinder (tagValue j value) state ∧
      LambdaSSA.Semantics.Diverges instr
        (.follow env (fun k => (g.block k).erase) j.val value state)
  refine Diverges.coinduct R ?_ ⟨i, current, s, rfl, h⟩
  intro c hc
  obtain ⟨j, value, state, rfl, hdiv⟩ := hc
  cases hdiv.unfold with
  | follow_body inside hbody => exact False.elim (flat_not_diverges _ _ _ hbody)
  | follow_next inside head tail =>
      obtain ⟨k, hk, hbody⟩ := loopBody_eval (g := g) (i := j) agree head
      have insideNext : k.val < blocks := by
        rw [hk]
        exact follow_diverges_inside tail
      let next : Fin blocks := ⟨k.val, insideNext⟩
      have heq : k = next.castAdd exits := Fin.ext rfl
      rw [heq] at hbody
      refine .loop_step (by simpa [emitValueCFG] using
        (eval_underBinder (intermediate := extra) hbody)) ?_
      refine ⟨next, _, _, rfl, ?_⟩
      simpa only [show next.val = k.val from rfl, hk] using tail

/-- Every infinite execution of a finite flat CFG remains infinite after encoding. -/
theorem encodeCFG_diverges {blocks exits captured : Nat}
    {g : LambdaSSA.FiniteCFG Φ blocks exits captured}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α captured} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Diverges instr (.region env g.erase s)) :
    Diverges instr free (.term bound (encodeCFG g) s) := by
  cases h.unfold with
  | cfg_entry rest => exact False.elim (flat_not_diverges _ _ _ rest)
  | cfg_follow entry follow =>
      obtain ⟨i, hi, he⟩ := encodeFlatWith_eval
        (fun {_n _bound i _a _s _s' _value} ha => emitCFG_eval i ha) agree entry
      have inside : i.val < blocks := by
        rw [hi]
        exact follow_diverges_inside follow
      let j : Fin blocks := ⟨i.val, inside⟩
      have heq : i = j.castAdd exits := Fin.ext rfl
      refine Diverges.fold (.case_inr (by simpa [emitValueCFG, heq] using he) ?_)
      refine Diverges.fold (.iter_loop .bv ?_)
      apply follow_diverges_loop agree
      simpa only [show j.val = i.val from rfl, hi] using follow

end Silmaril.Isotope.Morphism.SSAIter
