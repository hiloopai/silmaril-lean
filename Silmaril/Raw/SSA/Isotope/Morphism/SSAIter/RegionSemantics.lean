module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Region
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Correctness

/-! # Finite execution of nested SSA encodings -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv Empty α}

def regionLoopBody {count labels n : Nat} (blocks : Fin count → LambdaSSA.Region Φ)
    (hscope : ∀ i, (blocks i).Scoped (count + labels) (n + 1)) : Tm Empty Φ (n + 1) :=
  dispatch (.bv 0) (fun i =>
    (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (hscope i)).underBinder)

theorem encodeExpr_eval {n : Nat} {arg : LambdaSSA.Tm Φ} (hscope : arg.Scoped n)
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} {value : Value α} (agree : CaseSSA.EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Tm.Eval instr env arg s value s') :
    Eval instr free bound (encodeExpr arg hscope) s value s' := by
  apply CaseSSA.eval_of_erase agree
  simpa only [CaseSSA.erase_ofScoped] using h

/-- Arbitrary nested region execution preserves the selected label, payload,
and complete state. The result holds for nondeterministic primitive relations. -/
theorem encodeRegionWith_eval {r : LambdaSSA.Region Φ} {env : LambdaSSA.Semantics.Env α}
    {s s' : σ} {label : Nat} {value : Value α}
    (run : LambdaSSA.Semantics.Region.Eval instr env r s label value s') :
    ∀ {labels n : Nat} (hscope : r.Scoped labels n)
      {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
      {emitValue : Fin labels → Value α → Value α},
      (∀ {n : Nat} {bound : BoundEnv α n} {i : Fin labels} {a : Tm Empty Φ n}
        {s s' : σ} {v : Value α}, Eval instr free bound a s v s' →
          Eval instr free bound (emit i a) s (emitValue i v) s') →
      ∀ (bound : BoundEnv α n), CaseSSA.EnvAgrees env bound →
      ∃ i : Fin labels, i.val = label ∧
        Eval instr free bound (encodeRegionWith emit r hscope) s (emitValue i value) s' := by
  induction run using LambdaSSA.Semantics.Region.Eval.rec
      (motive_2 := fun env count bs first current s out value s' _ =>
        ∀ {labels n : Nat} (hscope : ∀ i, (bs i).Scoped (count + labels) (n + 1))
          (bound : BoundEnv α n), CaseSSA.EnvAgrees env bound →
          ∀ i : Fin count, first = i.val →
          ∃ e : Fin labels, e.val = out ∧
            Loop instr free bound (regionLoopBody bs hscope)
              (tagValue i current) s (tagValue e value) s') with
  | br arg =>
    intro labels n hs emit emitValue hemit bound agree
    exact ⟨⟨_, hs.1⟩, rfl, hemit (encodeExpr_eval hs.2 agree arg)⟩
  | let₁ arg body ih =>
    intro labels n hs emit emitValue hemit bound agree
    obtain ⟨i, hi, hb⟩ := ih (emit := @emit) (emitValue := emitValue) hs.2 (@hemit) _ (agree.extend _)
    exact ⟨i, hi, .let₁ (encodeExpr_eval hs.1 agree arg) hb⟩
  | let₂ arg body ih =>
    intro labels n hs emit emitValue hemit bound agree
    obtain ⟨i, hi, hb⟩ := ih (emit := @emit) (emitValue := emitValue) hs.2 (@hemit) _ ((agree.extend _).extend _)
    exact ⟨i, hi, .let₂ (encodeExpr_eval hs.1 agree arg) hb⟩
  | case_inl arg body ih =>
    intro labels n hs emit emitValue hemit bound agree
    obtain ⟨i, hi, hb⟩ := ih (emit := @emit) (emitValue := emitValue) hs.2.1 (@hemit) _ (agree.extend _)
    exact ⟨i, hi, .case_inl (encodeExpr_eval hs.1 agree arg) hb⟩
  | case_inr arg body ih =>
    intro labels n hs emit emitValue hemit bound agree
    obtain ⟨i, hi, hb⟩ := ih (emit := @emit) (emitValue := emitValue) hs.2.2 (@hemit) _ (agree.extend _)
    exact ⟨i, hi, .case_inr (encodeExpr_eval hs.1 agree arg) hb⟩
  | @cfg env entry count blocks s s₁ s₂ initial value first label entryRun follow ihe ihf =>
    intro labels n hs emit emitValue hemit bound agree
    obtain ⟨i, hi, he⟩ := ihe (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
      hs.1 (fun {_n _bound i _a _s _s' _v} h => emitCFG_eval i h) bound agree
    cases i using Fin.addCases with
    | left i =>
      obtain ⟨e, hout, hl⟩ := ihf hs.2 bound agree i hi.symm
      refine ⟨e, hout, dispatch_eval e ?_ (hemit .bv)⟩
      exact .case_inr (by simpa [emitValueCFG] using he)
        (.iter .bv (hl.rename Fin.succ _ (fun _ => rfl)))
    | right e =>
      have outside : count ≤ (Fin.natAdd count e).val := Nat.le_add_right _ _
      rw [hi] at outside
      obtain ⟨hout, rfl, rfl⟩ := follow_outside follow outside
      refine ⟨e, ?_, dispatch_eval e ?_ (hemit .bv)⟩
      · rw [← hi, Fin.val_natAdd, Nat.add_sub_cancel_left] at hout
        exact hout.symm
      · exact .case_inl (by simpa [emitValueCFG] using he) .bv
  | exit outside =>
    rename_i labels n hs bound agree i hi
    exact False.elim (Nat.not_lt_of_ge outside (hi.symm ▸ i.isLt))
  | @step env count first next out bs current middle value s s₁ s₂ inside head tail ihh iht =>
    rename_i labels n hs bound agree i hi
    subst first
    obtain ⟨j, hj, hh⟩ := ihh (emit := fun {n} => emitCFG (blocks := count) (exits := labels)) (hs i)
      (fun {_n _bound i _a _s _s' _v} h => emitCFG_eval i h) _ (agree.extend current)
    have hstep : Eval instr free (extend bound (tagValue i current))
        (regionLoopBody bs hs) s (emitValueCFG j middle) s₁ :=
      dispatch_eval i .bv (eval_underBinder hh)
    cases j using Fin.addCases with
    | left j =>
      obtain ⟨e, he, ht⟩ := iht hs bound agree j hj.symm
      exact ⟨e, he, .step (by simpa [emitValueCFG] using hstep) ht⟩
    | right e =>
      have outside : count ≤ next := by
        rw [← hj]
        exact Nat.le_add_right _ _
      obtain ⟨hout, rfl, rfl⟩ := follow_outside tail outside
      refine ⟨e, ?_, .done (by simpa [emitValueCFG] using hstep)⟩
      rw [← hj, Fin.val_natAdd, Nat.add_sub_cancel_left] at hout
      exact hout.symm

theorem encodeRegion_eval {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hscope : r.Scoped labels n) {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} {label : Nat} {value : Value α} (agree : CaseSSA.EnvAgrees env bound)
    (run : LambdaSSA.Semantics.Region.Eval instr env r s label value s') :
    ∃ i : Fin labels, i.val = label ∧
      Eval instr free bound (encodeRegion r hscope) s (tagValue i value) s' :=
  encodeRegionWith_eval run hscope (fun {_n _bound i _a _s _s' _v} h => inject_eval i h) bound agree

end Silmaril.Isotope.Morphism.SSAIter
