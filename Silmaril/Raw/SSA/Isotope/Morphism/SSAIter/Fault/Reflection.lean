module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Fault.Preservation

/-! The structured encoding introduces no additional explicit faults. -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : FreeEnv Empty α}

theorem regionLoopBody_fault_reflect {count labels n : Nat}
    {blocks : Fin count → LambdaSSA.Region Φ}
    {hs : ∀ i, (blocks i).Scoped (count + labels) (n + 1)}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    (reflects : ∀ i {current : Value α} {s s' : σ},
      Fault instr faults free (extend bound current)
        (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (hs i)) s s' →
      LambdaSSA.Semantics.Region.Fault instr faults (LambdaSSA.Semantics.extend env current)
        (blocks i) s s')
    (i : Fin count) {current : Value α} {s s' : σ}
    (h : Fault instr faults free (extend bound (tagValue i current)) (regionLoopBody blocks hs) s s') :
    LambdaSSA.Semantics.Region.Fault instr faults (LambdaSSA.Semantics.extend env current)
      (blocks i) s s' := by
  rcases dispatch_fault_iff.mp h with arg | ⟨j, payload, mid, arg, branch⟩
  · cases arg
  · obtain ⟨eq, rfl⟩ := eval_bv_result arg
    obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp eq
    exact reflects _ (fault_underBinder_iff.mp branch)

theorem regionLoopFault_reflect {count labels n : Nat}
    {blocks : Fin count → LambdaSSA.Region Φ}
    {hs : ∀ i, (blocks i).Scoped (count + labels) (n + 1)}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    (reflects : ∀ i {current result : Value α} {s s' : σ},
      Eval instr free (extend bound current)
        (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (hs i))
        s result s' →
      ∃ (j : Fin (count + labels)) (value : Value α),
        LambdaSSA.Semantics.Region.Eval instr (LambdaSSA.Semantics.extend env current)
          (blocks i) s j.val value s' ∧ result = emitValueCFG j value)
    (reflectsFault : ∀ i {current : Value α} {s s' : σ},
      Fault instr faults free (extend bound current)
        (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (hs i)) s s' →
      LambdaSSA.Semantics.Region.Fault instr faults (LambdaSSA.Semantics.extend env current)
        (blocks i) s s')
    {current : Value α} {s s' : σ}
    (h : LoopFault instr faults free bound (regionLoopBody blocks hs) current s s') :
    ∀ (i : Fin count) (v : Value α), current = tagValue i v →
      LambdaSSA.Semantics.Region.FollowFault instr faults env blocks i.val v s s' := by
  generalize hbody : regionLoopBody blocks hs = code at h
  induction h using LoopFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | body fault _ =>
    intro i v eq
    subst eq
    rw [← hbody] at fault
    exact .body i.isLt (regionLoopBody_fault_reflect reflectsFault i fault)
  | step head tail ih =>
    intro i v eq
    subst eq
    rw [← hbody] at head
    obtain ⟨j, value, block, eq⟩ := regionLoopBody_reflect reflects i head
    cases j using Fin.addCases with
    | right e => simp [emitValueCFG] at eq
    | left j =>
      have eq' := Value.inr.inj (by simpa [emitValueCFG] using eq)
      exact .step i.isLt block (ih reflects reflectsFault hbody j value eq')
  | _ => trivial

theorem encodeRegionWith_fault_reflect {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hs : r.Scoped labels n)
    {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
    (hemit : ∀ {n : Nat} {bound : BoundEnv α n} {i : Fin labels} {a : Tm Empty Φ n}
      {s s' : σ}, Fault instr faults free bound (emit i a) s s' →
        Fault instr faults free bound a s s')
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} (agree : CaseSSA.EnvAgrees env bound)
    (run : Fault instr faults free bound (encodeRegionWith emit r hs) s s') :
    LambdaSSA.Semantics.Region.Fault instr faults env r s s' := by
  induction r generalizing labels n env s s' with
  | br label arg => exact .br ((encodeExpr_fault_iff hs.2 agree).mp (hemit run))
  | let₁ value body ih =>
    cases run with
    | let₁_arg arg => exact .let₁_arg ((encodeExpr_fault_iff hs.1 agree).mp arg)
    | let₁_body arg rest =>
      exact .let₁_body ((encodeExpr_eval_iff hs.1 agree).mp arg)
        (ih hs.2 (emit := @emit) (@hemit) (agree.extend _) rest)
  | let₂ value body ih =>
    cases run with
    | let₂_arg arg => exact .let₂_arg ((encodeExpr_fault_iff hs.1 agree).mp arg)
    | let₂_body arg rest =>
      exact .let₂_body ((encodeExpr_eval_iff hs.1 agree).mp arg)
        (ih hs.2 (emit := @emit) (@hemit) ((agree.extend _).extend _) rest)
  | case discr left right ihl ihr =>
    cases run with
    | case_arg arg => exact .case_arg ((encodeExpr_fault_iff hs.1 agree).mp arg)
    | case_inl arg rest =>
      exact .case_inl ((encodeExpr_eval_iff hs.1 agree).mp arg)
        (ihl hs.2.1 (emit := @emit) (@hemit) (agree.extend _) rest)
    | case_inr arg rest =>
      exact .case_inr ((encodeExpr_eval_iff hs.1 agree).mp arg)
        (ihr hs.2.2 (emit := @emit) (@hemit) (agree.extend _) rest)
  | cfg entry count blocks ihe ihb =>
    rcases dispatch_fault_iff.mp run with core | ⟨i, payload, mid, _, branch⟩
    · cases core with
      | case_arg arg =>
        exact .cfg_entry (ihe hs.1
          (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
          (fun {_n _bound i _a _s _s'} h => (emitCFG_fault_iff i).mp h) agree arg)
      | case_inl arg returned => cases returned
      | case_inr arg iterated =>
        obtain ⟨j, v, source, eq⟩ := encodeRegionWith_reflect hs.1
          (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
          (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i) agree arg
        cases j using Fin.addCases with
        | right j => simp [emitValueCFG] at eq
        | left j =>
          have tagged := Value.inr.inj (by simpa [emitValueCFG] using eq)
          cases iterated with
          | iter_init bad => cases bad
          | iter_loop init loop =>
            obtain ⟨rfl, rfl⟩ := eval_bv_result init
            have loop' := loop.map_body (fun h => eval_underBinder_iff.mp h)
              (fun h => fault_underBinder_iff.mp h)
            apply LambdaSSA.Semantics.Region.Fault.cfg_follow source
            exact regionLoopFault_reflect
              (fun i {_current _result _s _s'} h => encodeRegionWith_reflect (hs.2 i)
                (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
                (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i) (agree.extend _) h)
              (fun i {_current _s _s'} h => ihb i (hs.2 i)
                (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
                (fun {_n _bound i _a _s _s'} h => (emitCFG_fault_iff i).mp h) (agree.extend _) h)
              loop' j v tagged
    · have bad := hemit branch
      cases bad

/-- Faults agree for all scoped nested regions. The same explicit primitive
fault relation and exact final state appear on both sides. -/
theorem encodeRegion_fault_iff {labels n : Nat} {r : LambdaSSA.Region Φ}
    (scope : r.Scoped labels n) {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} (agree : CaseSSA.EnvAgrees env bound) :
    Fault instr faults free bound (encodeRegion r scope) s s' ↔
      LambdaSSA.Semantics.Region.Fault instr faults env r s s' :=
  ⟨encodeRegionWith_fault_reflect scope
    (fun {_n _bound i _a _s _s'} h => (inject_fault_iff i).mp h) agree,
    encodeRegion_fault scope agree⟩

end Silmaril.Isotope.Morphism.SSAIter
