module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Encode
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.ExpressionSemantics
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSASemantics

/-! Finite execution of scoped flat regions and their tagged expression encoding. -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w} {labels n blocks exits : Nat}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv Empty α}

/-- The runtime counterpart of `emitCFG`: exits are left, loop states right. -/
def emitValueCFG (i : Fin (blocks + exits)) (value : Value α) : Value α :=
  Fin.addCases (fun j => .inr (tagValue j value)) (fun j => .inl (tagValue j value)) i

theorem emitCFG_eval (i : Fin (blocks + exits)) {bound : BoundEnv α n} {a : Tm Empty Φ n}
    {s s' : σ} {value : Value α} (h : Eval instr free bound a s value s') :
    Eval instr free bound (emitCFG i a) s (emitValueCFG i value) s' := by
  cases i using Fin.addCases with
  | left i => simpa [emitCFG, emitValueCFG] using Eval.inr (inject_eval i h)
  | right i => simpa [emitCFG, emitValueCFG] using Eval.inl (inject_eval i h)

/-- Any finite execution of a scoped flat region returns one of its finite labels. -/
theorem flat_eval_label_lt {r : LambdaSSA.Flat Φ labels n}
    {env : LambdaSSA.Semantics.Env α} {s s' : σ} {label : Nat} {value : Value α}
    (h : LambdaSSA.Semantics.Region.Eval instr env r.erase s label value s') :
    label < labels := by
  induction r generalizing env s s' value with
  | br i a => cases h; exact i.isLt
  | let₁ a b ih => cases h with | let₁ _ hb => exact ih hb
  | let₂ a b ih => cases h with | let₂ _ hb => exact ih hb
  | case e l r ihl ihr => cases h with
      | case_inl _ hl => exact ihl hl
      | case_inr _ hr => exact ihr hr

/-- Finite flat execution is preserved by every emitter that preserves its
payload computation and adds the prescribed runtime result. -/
theorem encodeFlatWith_eval
    {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
    {emitValue : Fin labels → Value α → Value α}
    (hemit : ∀ {n : Nat} {bound : BoundEnv α n} {i : Fin labels} {a : Tm Empty Φ n}
      {s s' : σ} {value : Value α}, Eval instr free bound a s value s' →
        Eval instr free bound (emit i a) s (emitValue i value) s')
    {r : LambdaSSA.Flat Φ labels n} {env : LambdaSSA.Semantics.Env α}
    {bound : BoundEnv α n} {s s' : σ} {label : Nat} {value : Value α}
    (agree : CaseSSA.EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Region.Eval instr env r.erase s label value s') :
    ∃ i : Fin labels, i.val = label ∧
      Eval instr free bound (encodeFlatWith emit r) s (emitValue i value) s' := by
  induction r generalizing env s s' value with
  | br i a =>
      cases h with
      | br ha => exact ⟨i, rfl, hemit (CaseSSA.eval_of_erase agree ha)⟩
  | let₁ a b ih =>
      cases h with
      | let₁ ha hb =>
          obtain ⟨i, hi, ht⟩ := ih (agree.extend _) hb
          exact ⟨i, hi, .let₁ (CaseSSA.eval_of_erase agree ha) ht⟩
  | let₂ a b ih =>
      cases h with
      | let₂ ha hb =>
          obtain ⟨i, hi, ht⟩ := ih ((agree.extend _).extend _) hb
          exact ⟨i, hi, .let₂ (CaseSSA.eval_of_erase agree ha) ht⟩
  | case e l r ihl ihr =>
      cases h with
      | case_inl he hl =>
          obtain ⟨i, hi, ht⟩ := ihl (agree.extend _) hl
          exact ⟨i, hi, .case_inl (CaseSSA.eval_of_erase agree he) ht⟩
      | case_inr he hr =>
          obtain ⟨i, hi, ht⟩ := ihr (agree.extend _) hr
          exact ⟨i, hi, .case_inr (CaseSSA.eval_of_erase agree he) ht⟩

theorem encodeFlat_eval {r : LambdaSSA.Flat Φ labels n}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} {label : Nat} {value : Value α} (agree : CaseSSA.EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Region.Eval instr env r.erase s label value s') :
    ∃ i : Fin labels, i.val = label ∧
      Eval instr free bound (encodeFlat r) s (tagValue i value) s' :=
  encodeFlatWith_eval (fun {_n _bound i _a _s _s' _value} ha => inject_eval i ha) agree h

/-- A graph block execution becomes one iteration-body evaluation. The captured
environment is reused, while only the selected block parameter is replaced. -/
theorem loopBody_eval {captured : Nat}
    {g : LambdaSSA.FiniteCFG Φ blocks exits captured} {i : Fin blocks}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α captured}
    {s s' : σ} {next : Nat} {current value : Value α}
    (agree : CaseSSA.EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Region.Eval instr (LambdaSSA.Semantics.extend env current)
      (g.block i).erase s next value s') :
    ∃ j : Fin (blocks + exits), j.val = next ∧
      Eval instr free (extend bound (tagValue i current)) (loopBody g)
        s (emitValueCFG j value) s' := by
  obtain ⟨j, hj, hb⟩ := encodeFlatWith_eval
    (fun {_n _bound i _a _s _s' _value} ha => emitCFG_eval i ha) (agree.extend current) h
  exact ⟨j, hj, dispatch_eval i .bv (eval_underBinder hb)⟩

end Silmaril.Isotope.Morphism.SSAIter
