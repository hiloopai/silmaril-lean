module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.FlatSemantics

/-!
# Finite correctness of the CFG-to-iteration encoding

Every finite SSA graph execution produces the same external label, payload,
and machine state in the encoded term. The result is a preservation theorem;
it requires neither instruction determinism nor a typing assumption.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv Empty α}

/-- Following an external label returns immediately and performs no state transition. -/
theorem follow_outside {blocks first out : Nat}
    {env : LambdaSSA.Semantics.Env α} {bs : Fin blocks → LambdaSSA.Region Φ}
    {current value : Value α} {s s' : σ}
    (h : LambdaSSA.Semantics.Region.Follow instr env bs first current s out value s')
    (outside : blocks ≤ first) : out = first - blocks ∧ value = current ∧ s' = s := by
  cases h with
  | exit => exact ⟨rfl, rfl, rfl⟩
  | step inside _ _ => exact False.elim (Nat.not_lt_of_ge outside inside)

/-- Finite internal control transfers become finite iterations. The quantified
graph witness keeps the induction independent of the unscoped region indices. -/
theorem follow_internal_eval {blocks first out : Nat}
    {env : LambdaSSA.Semantics.Env α} {bs : Fin blocks → LambdaSSA.Region Φ}
    {current value : Value α} {s s' : σ}
    (h : LambdaSSA.Semantics.Region.Follow instr env bs first current s out value s') :
    ∀ {exits captured : Nat} (g : LambdaSSA.FiniteCFG Φ blocks exits captured),
      bs = (fun i => (g.block i).erase) →
      ∀ (bound : BoundEnv α captured), CaseSSA.EnvAgrees env bound →
      ∀ i : Fin blocks, first = i.val →
      ∃ e : Fin exits, e.val = out ∧
        Loop instr free bound (loopBody g) (tagValue i current) s (tagValue e value) s' := by
  induction h using LambdaSSA.Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside =>
      intro _ _ _ _ _ _ i hi
      exact False.elim (Nat.not_lt_of_ge outside (hi.symm ▸ i.isLt))
  | @step env blocks first next out bs current middle value s s₁ s₂ inside head tail _ ih =>
      intro exits captured g hbs bound agree i hi
      subst bs
      subst first
      obtain ⟨j, hj, hstep⟩ := loopBody_eval (g := g) (i := i) agree head
      cases j using Fin.addCases with
      | left j =>
          obtain ⟨e, he, ht⟩ := ih g rfl bound agree j hj.symm
          exact ⟨e, he, .step (by simpa [emitValueCFG] using hstep) ht⟩
      | right e =>
          have outside : blocks ≤ next := by
            rw [← hj]
            exact Nat.le_add_right _ _
          obtain ⟨hout, rfl, rfl⟩ := follow_outside tail outside
          refine ⟨e, ?_, .done (by simpa [emitValueCFG] using hstep)⟩
          rw [← hj, Fin.val_natAdd, Nat.add_sub_cancel_left] at hout
          exact hout.symm
  | _ => trivial

/-- A finite graph execution returns the same external label and payload, with
exactly the same final machine state, after tagging the external result. -/
theorem encodeCFG_eval {blocks exits captured : Nat}
    {g : LambdaSSA.FiniteCFG Φ blocks exits captured}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α captured}
    {s s' : σ} {out : Nat} {value : Value α}
    (agree : CaseSSA.EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Region.Eval instr env g.erase s out value s') :
    ∃ e : Fin exits, e.val = out ∧
      Eval instr free bound (encodeCFG g) s (tagValue e value) s' := by
  cases h with
  | cfg entry follow =>
      obtain ⟨i, hi, he⟩ := encodeFlatWith_eval
        (fun {_n _bound i _a _s _s' _value} ha => emitCFG_eval i ha) agree entry
      cases i using Fin.addCases with
      | left i =>
          obtain ⟨e, hout, hl⟩ := follow_internal_eval follow g rfl bound agree i hi.symm
          refine ⟨e, hout, .case_inr (by simpa [emitValueCFG] using he) (.iter .bv ?_)⟩
          exact hl.rename Fin.succ _ (fun _ => rfl)
      | right e =>
          have outside : blocks ≤ (Fin.natAdd blocks e).val := Nat.le_add_right _ _
          rw [hi] at outside
          obtain ⟨hout, rfl, rfl⟩ := follow_outside follow outside
          refine ⟨e, ?_, .case_inl (by simpa [emitValueCFG] using he) .bv⟩
          rw [← hi, Fin.val_natAdd, Nat.add_sub_cancel_left] at hout
          exact hout.symm

/-- Finite termination of the original graph is preserved without a determinism
or total-instruction assumption. -/
theorem encodeCFG_terminates {blocks exits captured : Nat}
    {g : LambdaSSA.FiniteCFG Φ blocks exits captured}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α captured} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound)
    (h : ∃ out value s', LambdaSSA.Semantics.Region.Eval instr env g.erase s out value s') :
    Terminates instr free bound (encodeCFG g) s := by
  obtain ⟨out, value, s', h⟩ := h
  obtain ⟨e, _, he⟩ := encodeCFG_eval agree h
  exact ⟨tagValue e value, s', he⟩

end Silmaril.Isotope.Morphism.SSAIter
