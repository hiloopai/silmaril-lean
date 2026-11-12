module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.RegionSemantics

/-! # Reflection of nested SSA execution -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless LetIter.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv Empty α}

/-- Finite tags preserve both the chosen label and its payload. -/
theorem tagValue_eq_iff {k : Nat} (i j : Fin k) (x y : Value α) :
    tagValue i x = tagValue j y ↔ i = j ∧ x = y := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp
    · simp only [tagValue_zero, tagValue_succ, reduceCtorEq, false_iff, not_and]
      intro eq
      have := congrArg Fin.val eq
      simp only [Fin.val_zero, Fin.val_succ] at this
      omega
    · simp
    · simpa using ih _ _

theorem emitCFG_eval_iff {count labels n : Nat} (i : Fin (count + labels))
    {bound : BoundEnv α n} {a : Tm Empty Φ n} {s s' : σ} {result : Value α} :
    Eval instr free bound (emitCFG i a) s result s' ↔
      ∃ value, Eval instr free bound a s value s' ∧ result = emitValueCFG i value := by
  cases i using Fin.addCases with
  | left i =>
    constructor
    · intro h
      have h' : Eval instr free bound (.inr (inject i a)) s result s' := by
        simpa only [emitCFG, Fin.addCases_left] using h
      cases h' with | inr h =>
        obtain ⟨v, hv, rfl⟩ := (inject_eval_iff i).mp h
        exact ⟨v, hv, by simp [emitValueCFG]⟩
    · rintro ⟨v, hv, rfl⟩
      exact emitCFG_eval _ hv
  | right i =>
    constructor
    · intro h
      have h' : Eval instr free bound (.inl (inject i a)) s result s' := by
        simpa only [emitCFG, Fin.addCases_right] using h
      cases h' with | inl h =>
        obtain ⟨v, hv, rfl⟩ := (inject_eval_iff i).mp h
        exact ⟨v, hv, by simp [emitValueCFG]⟩
    · rintro ⟨v, hv, rfl⟩
      exact emitCFG_eval _ hv

theorem encodeExpr_eval_iff {n : Nat} {arg : LambdaSSA.Tm Φ} (hscope : arg.Scoped n)
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} {value : Value α} (agree : CaseSSA.EnvAgrees env bound) :
    Eval instr free bound (encodeExpr arg hscope) s value s' ↔
      LambdaSSA.Semantics.Tm.Eval instr env arg s value s' := by
  simpa only [encodeExpr, CaseSSA.erase_ofScoped] using
    (CaseSSA.erase_eval_iff (t := CaseSSA.ofScoped arg hscope) agree).symm

theorem eval_bv_result {n : Nat} {bound : BoundEnv α n} {i : Fin n}
    {s s' : σ} {value : Value α} (h : Eval instr free bound (.bv i) s value s') :
    value = bound i ∧ s' = s := by cases h; exact ⟨rfl, rfl⟩

/-- Reflection for one selected block, given reflection for its encoded body. -/
theorem regionLoopBody_reflect {count labels n : Nat}
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
    (i : Fin count) {current result : Value α} {s s' : σ}
    (h : Eval instr free (extend bound (tagValue i current)) (regionLoopBody blocks hs) s result s') :
    ∃ (j : Fin (count + labels)) (value : Value α),
      LambdaSSA.Semantics.Region.Eval instr (LambdaSSA.Semantics.extend env current)
        (blocks i) s j.val value s' ∧ result = emitValueCFG j value := by
  obtain ⟨j, payload, mid, arg, branch⟩ := dispatch_eval_iff.mp h
  obtain ⟨eq, rfl⟩ := eval_bv_result arg
  obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp eq
  exact reflects _ (eval_underBinder_iff.mp branch)

/-- A finite target loop follows the same internal and external SSA jumps. -/
theorem regionLoop_reflect {count labels n : Nat}
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
    {current result : Value α} {s s' : σ}
    (h : Loop instr free bound (regionLoopBody blocks hs) current s result s') :
    ∀ (i : Fin count) (v : Value α), current = tagValue i v →
    ∃ (e : Fin labels) (value : Value α), result = tagValue e value ∧
      LambdaSSA.Semantics.Region.Follow instr env blocks i.val v s e.val value s' := by
  generalize hbody : regionLoopBody blocks hs = code at h
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | @done n' bound' body' current out s₀ s₁ body _ =>
    intro i v eq
    subst eq
    rw [← hbody] at body
    obtain ⟨j, value, block, eq⟩ := regionLoopBody_reflect reflects i body
    cases j using Fin.addCases with
    | left j => simp [emitValueCFG] at eq
    | right e =>
      have eq' := Value.inl.inj (by simpa [emitValueCFG] using eq)
      refine ⟨e, value, eq', ?_⟩
      have tail : LambdaSSA.Semantics.Region.Follow instr env blocks
          (Fin.natAdd count e).val value s₁ e.val value s₁ := by
        simpa using (LambdaSSA.Semantics.Region.Follow.exit
          (instr := instr) (env := env) (blocks := blocks) (value := value)
          (s := s₁) (Nat.le_add_right count e.val))
      exact .step i.isLt block tail
  | step body loop _ ih =>
    intro i v eq
    subst eq
    rw [← hbody] at body
    obtain ⟨j, value, block, eq⟩ := regionLoopBody_reflect reflects i body
    cases j using Fin.addCases with
    | right e => simp [emitValueCFG] at eq
    | left j =>
      have eq' := Value.inr.inj (by simpa [emitValueCFG] using eq)
      obtain ⟨e, out, result, tail⟩ := ih reflects hbody j value eq'
      exact ⟨e, out, result, .step i.isLt block tail⟩
  | _ => trivial

theorem encodeRegionWith_reflect {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hs : r.Scoped labels n)
    {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
    {emitValue : Fin labels → Value α → Value α}
    (hemit : ∀ {n : Nat} {bound : BoundEnv α n} {i : Fin labels} {a : Tm Empty Φ n}
      {s s' : σ} {result : Value α},
      Eval instr free bound (emit i a) s result s' ↔
        ∃ value, Eval instr free bound a s value s' ∧ result = emitValue i value)
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} {result : Value α} (agree : CaseSSA.EnvAgrees env bound)
    (run : Eval instr free bound (encodeRegionWith emit r hs) s result s') :
    ∃ (i : Fin labels) (value : Value α),
      LambdaSSA.Semantics.Region.Eval instr env r s i.val value s' ∧ result = emitValue i value := by
  induction r generalizing labels n env s s' result with
  | br label arg =>
    obtain ⟨v, ha, eq⟩ := hemit.mp run
    exact ⟨⟨label, hs.1⟩, v, .br ((encodeExpr_eval_iff hs.2 agree).mp ha), eq⟩
  | let₁ value body ih =>
    cases run with
    | let₁ arg rest =>
      obtain ⟨i, v, body, eq⟩ := ih hs.2 (emit := @emit) (emitValue := emitValue)
        (@hemit) (agree.extend _) rest
      exact ⟨i, v, .let₁ ((encodeExpr_eval_iff hs.1 agree).mp arg) body, eq⟩
  | let₂ value body ih =>
    cases run with
    | let₂ arg rest =>
      obtain ⟨i, v, body, eq⟩ := ih hs.2 (emit := @emit) (emitValue := emitValue)
        (@hemit) ((agree.extend _).extend _) rest
      exact ⟨i, v, .let₂ ((encodeExpr_eval_iff hs.1 agree).mp arg) body, eq⟩
  | case discr left right ihl ihr =>
    cases run with
    | case_inl arg rest =>
      obtain ⟨i, v, body, eq⟩ := ihl hs.2.1 (emit := @emit) (emitValue := emitValue)
        (@hemit) (agree.extend _) rest
      exact ⟨i, v, .case_inl ((encodeExpr_eval_iff hs.1 agree).mp arg) body, eq⟩
    | case_inr arg rest =>
      obtain ⟨i, v, body, eq⟩ := ihr hs.2.2 (emit := @emit) (emitValue := emitValue)
        (@hemit) (agree.extend _) rest
      exact ⟨i, v, .case_inr ((encodeExpr_eval_iff hs.1 agree).mp arg) body, eq⟩
  | cfg entry count blocks ihe ihb =>
    obtain ⟨e, payload, mid, core, branch⟩ := dispatch_eval_iff.mp run
    obtain ⟨v, hv, eq⟩ := hemit.mp branch
    obtain ⟨valueEq, stateEq⟩ := eval_bv_result hv
    change v = payload at valueEq
    subst v
    subst s'
    refine ⟨e, payload, ?_, eq⟩
    cases core with
    | case_inl arg returned =>
      obtain ⟨returnedEq, rfl⟩ := eval_bv_result returned
      obtain ⟨j, v, source, eq⟩ := ihe hs.1 (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
        (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i) agree arg
      cases j using Fin.addCases with
      | left j => simp [emitValueCFG] at eq
      | right j =>
        have tagged := Value.inl.inj (by simpa [emitValueCFG] using eq)
        obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp (returnedEq.trans tagged)
        apply LambdaSSA.Semantics.Region.Eval.cfg source
        simpa using (LambdaSSA.Semantics.Region.Follow.exit
          (instr := instr) (env := env) (blocks := blocks) (value := payload)
          (s := _) (Nat.le_add_right count e.val))
    | case_inr arg iterated =>
      obtain ⟨j, v, source, eq⟩ := ihe hs.1 (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
        (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i) agree arg
      cases j using Fin.addCases with
      | right j => simp [emitValueCFG] at eq
      | left j =>
        have tagged := Value.inr.inj (by simpa [emitValueCFG] using eq)
        cases iterated with
        | iter init loop =>
          obtain ⟨rfl, rfl⟩ := eval_bv_result init
          have loop' := loop.map_body (fun h => eval_underBinder_iff.mp h)
          obtain ⟨out, value, eqout, follow⟩ := regionLoop_reflect
            (fun i {_current _result _s _s'} h => ihb i (hs.2 i)
              (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
              (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i)
              (agree.extend _) h) loop' j v tagged
          obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp eqout
          exact .cfg source follow

/-- Finite outcomes of arbitrary nested SSA and its let-iter encoding agree
exactly, without determinism, totality, or a typing hypothesis. -/
theorem encodeRegion_eval_iff {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hs : r.Scoped labels n) {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    {s s' : σ} {result : Value α} (agree : CaseSSA.EnvAgrees env bound) :
    Eval instr free bound (encodeRegion r hs) s result s' ↔
      ∃ (i : Fin labels) (value : Value α),
        LambdaSSA.Semantics.Region.Eval instr env r s i.val value s' ∧ result = tagValue i value := by
  constructor
  · exact encodeRegionWith_reflect hs
      (fun {_n _bound i _a _s _s' _result} => inject_eval_iff i) agree
  · rintro ⟨i, value, source, rfl⟩
    obtain ⟨j, label, target⟩ := encodeRegion_eval hs agree source
    have : j = i := Fin.ext label
    subst j
    exact target

end Silmaril.Isotope.Morphism.SSAIter
