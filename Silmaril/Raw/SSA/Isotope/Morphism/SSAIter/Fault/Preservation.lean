module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Fault.Dispatch

/-! Arbitrary nested SSA faults propagate through the structured encoding. -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : FreeEnv Empty α}

theorem followFault_inside {count : Nat} {blocks : Fin count → LambdaSSA.Region Φ}
    {env : LambdaSSA.Semantics.Env α} {first : Nat} {value : Value α} {s s' : σ}
    (h : LambdaSSA.Semantics.Region.FollowFault instr faults env blocks first value s s') :
    first < count := by cases h <;> assumption

/-- Emitter interfaces are fault-transparent. The proof follows finite successful
prefixes and the failing block, including arbitrary nested CFGs. -/
theorem encodeRegionWith_fault {r : LambdaSSA.Region Φ} {env : LambdaSSA.Semantics.Env α}
    {s s' : σ} (run : LambdaSSA.Semantics.Region.Fault instr faults env r s s') :
    ∀ {labels n : Nat} (scope : r.Scoped labels n)
      {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n},
      (∀ {n : Nat} {bound : BoundEnv α n} {i : Fin labels} {a : Tm Empty Φ n}
        {s s' : σ}, Fault instr faults free bound a s s' →
          Fault instr faults free bound (emit i a) s s') →
      ∀ (bound : BoundEnv α n), CaseSSA.EnvAgrees env bound →
        Fault instr faults free bound (encodeRegionWith emit r scope) s s' := by
  induction run using LambdaSSA.Semantics.Region.Fault.rec
      (motive_2 := fun env count bs first current s s' _ =>
        ∀ {labels n : Nat} (scope : ∀ i, (bs i).Scoped (count + labels) (n + 1))
          (bound : BoundEnv α n), CaseSSA.EnvAgrees env bound →
          ∀ i : Fin count, first = i.val →
            LoopFault instr faults free bound (regionLoopBody bs scope) (tagValue i current) s s') with
  | br arg =>
    intro labels n hs emit hemit bound agree
    exact hemit ((encodeExpr_fault_iff hs.2 agree).mpr arg)
  | let₁_arg arg =>
    intro labels n hs emit hemit bound agree
    exact .let₁_arg ((encodeExpr_fault_iff hs.1 agree).mpr arg)
  | let₁_body arg body ih =>
    intro labels n hs emit hemit bound agree
    exact .let₁_body (encodeExpr_eval hs.1 agree arg)
      (ih hs.2 (emit := @emit) (@hemit) _ (agree.extend _))
  | let₂_arg arg =>
    intro labels n hs emit hemit bound agree
    exact .let₂_arg ((encodeExpr_fault_iff hs.1 agree).mpr arg)
  | let₂_body arg body ih =>
    intro labels n hs emit hemit bound agree
    exact .let₂_body (encodeExpr_eval hs.1 agree arg)
      (ih hs.2 (emit := @emit) (@hemit) _ ((agree.extend _).extend _))
  | case_arg arg =>
    intro labels n hs emit hemit bound agree
    exact .case_arg ((encodeExpr_fault_iff hs.1 agree).mpr arg)
  | case_inl arg body ih =>
    intro labels n hs emit hemit bound agree
    exact .case_inl (encodeExpr_eval hs.1 agree arg)
      (ih hs.2.1 (emit := @emit) (@hemit) _ (agree.extend _))
  | case_inr arg body ih =>
    intro labels n hs emit hemit bound agree
    exact .case_inr (encodeExpr_eval hs.1 agree arg)
      (ih hs.2.2 (emit := @emit) (@hemit) _ (agree.extend _))
  | @cfg_entry env entry count bs s s' fault ih =>
    intro labels n hs emit hemit bound agree
    exact dispatch_fault_arg (.case_arg
      (ih hs.1 (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
        (fun {_n _bound i _a _s _s'} h => (emitCFG_fault_iff i).mpr h) bound agree))
  | @cfg_follow env entry count bs s mid s' label value entryRun follow ih =>
    intro labels n hs emit hemit bound agree
    obtain ⟨i, hi, he⟩ := encodeRegionWith_eval entryRun hs.1
      (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
      (fun {_n _bound i _a _s _s' _v} h => emitCFG_eval i h) bound agree
    cases i using Fin.addCases with
    | left i =>
      have loop := ih hs.2 bound agree i hi.symm
      apply dispatch_fault_arg
      apply Fault.case_inr (by simpa [emitValueCFG] using he)
      apply Fault.iter_loop .bv
      exact loop.map_body (fun h => eval_underBinder h) (fun h => fault_underBinder_iff.mpr h)
    | right e =>
      have outside : count ≤ label := hi ▸ Nat.le_add_right count e.val
      exact False.elim (Nat.not_lt_of_ge outside (followFault_inside follow))
  | @body env count label bs value s s' inside fault ih =>
    rename_i labels n hs bound agree i hi
    subst label
    apply LoopFault.body
    apply dispatch_fault_branch i (Eval.bv)
    exact fault_underBinder_iff.mpr
      (ih (hs i) (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
        (fun {_n _bound j _a _s _s'} h => (emitCFG_fault_iff j).mpr h) _ (agree.extend _))
  | @step env count label next bs value output s mid s' inside head tail ih =>
    rename_i labels n hs bound agree i hi
    subst label
    obtain ⟨j, hj, hh⟩ := encodeRegionWith_eval head (hs i)
      (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
      (fun {_n _bound j _a _s _s' _v} h => emitCFG_eval j h) _ (agree.extend _)
    have step : Eval instr free (extend bound (tagValue i value))
        (regionLoopBody bs hs) s (emitValueCFG j output) mid :=
      dispatch_eval i .bv (eval_underBinder hh)
    cases j using Fin.addCases with
    | left j =>
      exact .step (by simpa [emitValueCFG] using step) (ih hs bound agree j hj.symm)
    | right e =>
      have outside : count ≤ next := hj ▸ Nat.le_add_right count e.val
      exact False.elim (Nat.not_lt_of_ge outside (followFault_inside tail))

theorem encodeRegion_fault {labels n : Nat} {r : LambdaSSA.Region Φ}
    (scope : r.Scoped labels n) {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} (agree : CaseSSA.EnvAgrees env bound)
    (fault : LambdaSSA.Semantics.Region.Fault instr faults env r s s') :
    Fault instr faults free bound (encodeRegion r scope) s s' :=
  encodeRegionWith_fault fault scope
    (fun {_n _bound i _a _s _s'} h => (inject_fault_iff i).mpr h) bound agree

end Silmaril.Isotope.Morphism.SSAIter
