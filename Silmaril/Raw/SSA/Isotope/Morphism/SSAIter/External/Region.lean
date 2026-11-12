module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.External.Helpers
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.RegionDivergence

/-! # External and internal infinite execution of arbitrary nested SSA regions -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.SSAIter.External

open LetIter.LocallyNameless
open LetIter.Semantics (BoundEnv FreeEnv Config Eval extend)
open LetIter.Semantics.External (Diverges)

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv Empty α}
  {prim : Φ → Value α → σ → Prop}

theorem follow_diverges_inside {count : Nat} {blocks : Fin count → LambdaSSA.Region Φ}
    {env : LambdaSSA.Semantics.Env α} {label : Nat} {value : Value α} {s : σ}
    (h : LambdaSSA.Semantics.External.Diverges instr prim (.follow env blocks label value s)) :
    label < count := by
  cases h.unfold with | core h => cases h <;> assumption

theorem regionLoopBody_diverges_iff {count labels n : Nat}
    {blocks : Fin count → LambdaSSA.Region Φ}
    {hs : ∀ i, (blocks i).Scoped (count + labels) (n + 1)}
    {bound : BoundEnv α n} (i : Fin count) {current : Value α} {s : σ} :
    Diverges instr free prim (.term (extend bound (tagValue i current)) (regionLoopBody blocks hs) s) ↔
      Diverges instr free prim (.term (extend bound current)
        (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (hs i)) s) := by
  constructor
  · intro h
    rcases dispatch_diverges_iff.mp h with arg | ⟨j, payload, mid, lookup, branch⟩
    · cases arg.unfold with | core h => cases h
    · obtain ⟨eq, rfl⟩ := eval_bv_result lookup
      obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp eq
      exact diverges_underBinder_iff.mp branch
  · intro h
    exact dispatch_diverges_iff.mpr (Or.inr ⟨i, current, s, .bv, diverges_underBinder_iff.mpr h⟩)

theorem regionLoop_diverges_iff {count labels n : Nat}
    {blocks : Fin count → LambdaSSA.Region Φ}
    {hs : ∀ i, (blocks i).Scoped (count + labels) (n + 1)}
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n}
    (agree : CaseSSA.EnvAgrees env bound)
    (bodyEquiv : ∀ (i : Fin count) (current : Value α) (s : σ),
      Diverges instr free prim (.term (extend bound current)
        (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (hs i)) s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim
        (.region (LambdaSSA.Semantics.extend env current) (blocks i) s))
    (i : Fin count) (current : Value α) (s : σ) :
    Diverges instr free prim (.loop bound (regionLoopBody blocks hs) (tagValue i current) s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim (.follow env blocks i.val current s) := by
  constructor
  · intro h
    let R : LambdaSSA.Semantics.Config α Φ σ → Prop := fun c =>
      LambdaSSA.Semantics.External.Diverges instr prim c ∨ ∃ (j : Fin count) (value : Value α) (state : σ),
        c = .follow env blocks j.val value state ∧
          Diverges instr free prim (.loop bound (regionLoopBody blocks hs) (tagValue j value) state)
    refine LambdaSSA.Semantics.External.Diverges.coinduct R ?_ (Or.inr ⟨i, current, s, rfl, h⟩)
    intro c hc
    rcases hc with existing | ⟨j, value, state, rfl, target⟩
    · exact existing.unfold.mono (fun _ h => Or.inl h)
    · apply LambdaSSA.Semantics.External.DivergenceStep.core
      cases target.unfold with | core target => cases target with
      | loop_body body =>
        exact .follow_body j.isLt (Or.inl ((bodyEquiv j value state).mp
          ((regionLoopBody_diverges_iff j).mp body)))
      | loop_step head tail =>
        obtain ⟨k, payload, run, eq⟩ := regionLoopBody_reflect
          (fun j {_current _result _s _s'} h => encodeRegionWith_reflect (hs j)
            (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i) (agree.extend _) h) j head
        cases k using Fin.addCases with
        | right k => simp [emitValueCFG] at eq
        | left k =>
          have eq' := Value.inr.inj (by simpa [emitValueCFG] using eq)
          subst eq'
          exact .follow_next j.isLt run (Or.inr ⟨k, payload, _, rfl, tail⟩)
  · intro h
    let R : Config α Empty Φ σ → Prop := fun c =>
      Diverges instr free prim c ∨ ∃ (j : Fin count) (value : Value α) (state : σ),
        c = .loop bound (regionLoopBody blocks hs) (tagValue j value) state ∧
          LambdaSSA.Semantics.External.Diverges instr prim (.follow env blocks j.val value state)
    refine Diverges.coinduct R ?_ (Or.inr ⟨i, current, s, rfl, h⟩)
    intro c hc
    rcases hc with existing | ⟨j, value, state, rfl, source⟩
    · exact existing.unfold.mono (fun _ h => Or.inl h)
    · apply LetIter.Semantics.External.DivergenceStep.core
      cases source.unfold with | core source => cases source with
      | follow_body inside body =>
        exact .loop_body (Or.inl ((regionLoopBody_diverges_iff j).mpr
          ((bodyEquiv j value state).mpr body)))
      | follow_next inside head tail =>
        obtain ⟨k, hk, run⟩ := regionLoopBody_eval_nested hs agree j head
        have insideNext : k.val < count := by
          rw [hk]
          exact follow_diverges_inside tail
        let next : Fin count := ⟨k.val, insideNext⟩
        have eq : k = next.castAdd labels := Fin.ext rfl
        rw [eq] at run
        refine .loop_step (by simpa [emitValueCFG] using run) (Or.inr ⟨next, _, _, rfl, ?_⟩)
        simpa only [show next.val = k.val from rfl, hk] using tail

theorem encodeRegionWith_diverges_iff {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hs : r.Scoped labels n)
    {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
    (emitDiverges : ∀ {n : Nat} {bound : BoundEnv α n} {i : Fin labels} {a : Tm Empty Φ n} {s : σ},
      Diverges instr free prim (.term bound (emit i a) s) ↔ Diverges instr free prim (.term bound a s))
    {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    Diverges instr free prim (.term bound (encodeRegionWith emit r hs) s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim (.region env r s) := by
  induction r generalizing labels n env s with
  | br label arg =>
    constructor
    · intro h
      exact .fold (.br ((CaseSSA.ofScoped_external_iff hs.2 agree).mp (emitDiverges.mp h)))
    · intro h; cases h.unfold with
      | core h => cases h
      | br arg => exact emitDiverges.mpr ((CaseSSA.ofScoped_external_iff hs.2 agree).mpr arg)
  | let₁ arg body ih =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | let₁_arg arg => exact .fold (.let₁_arg ((CaseSSA.ofScoped_external_iff hs.1 agree).mp arg))
      | let₁_body arg rest => exact .fold_core (.let₁ ((encodeExpr_eval_iff hs.1 agree).mp arg)
          ((ih hs.2 (emit := @emit) (@emitDiverges) (agree.extend _)).mp rest))
    · intro h; cases h.unfold with
      | let₁_arg arg => exact .fold_core (.let₁_arg ((CaseSSA.ofScoped_external_iff hs.1 agree).mpr arg))
      | core h => cases h with
        | let₁ arg rest => exact .fold_core (.let₁_body (encodeExpr_eval hs.1 agree arg)
          ((ih hs.2 (emit := @emit) (@emitDiverges) (agree.extend _)).mpr rest))
  | let₂ arg body ih =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | let₂_arg arg => exact .fold (.let₂_arg ((CaseSSA.ofScoped_external_iff hs.1 agree).mp arg))
      | let₂_body arg rest => exact .fold_core (.let₂ ((encodeExpr_eval_iff hs.1 agree).mp arg)
          ((ih hs.2 (emit := @emit) (@emitDiverges) ((agree.extend _).extend _)).mp rest))
    · intro h; cases h.unfold with
      | let₂_arg arg => exact .fold_core (.let₂_arg ((CaseSSA.ofScoped_external_iff hs.1 agree).mpr arg))
      | core h => cases h with
        | let₂ arg rest => exact .fold_core (.let₂_body (encodeExpr_eval hs.1 agree arg)
          ((ih hs.2 (emit := @emit) (@emitDiverges) ((agree.extend _).extend _)).mpr rest))
  | case arg left right ihl ihr =>
    constructor
    · intro h; cases h.unfold with | core h => cases h with
      | case_scrutinee arg => exact .fold (.case_arg ((CaseSSA.ofScoped_external_iff hs.1 agree).mp arg))
      | case_inl arg rest => exact .fold_core (.case_inl ((encodeExpr_eval_iff hs.1 agree).mp arg)
          ((ihl hs.2.1 (emit := @emit) (@emitDiverges) (agree.extend _)).mp rest))
      | case_inr arg rest => exact .fold_core (.case_inr ((encodeExpr_eval_iff hs.1 agree).mp arg)
          ((ihr hs.2.2 (emit := @emit) (@emitDiverges) (agree.extend _)).mp rest))
    · intro h; cases h.unfold with
      | case_arg arg => exact .fold_core (.case_scrutinee ((CaseSSA.ofScoped_external_iff hs.1 agree).mpr arg))
      | core h => cases h with
        | case_inl arg rest => exact .fold_core (.case_inl (encodeExpr_eval hs.1 agree arg)
            ((ihl hs.2.1 (emit := @emit) (@emitDiverges) (agree.extend _)).mpr rest))
        | case_inr arg rest => exact .fold_core (.case_inr (encodeExpr_eval hs.1 agree arg)
            ((ihr hs.2.2 (emit := @emit) (@emitDiverges) (agree.extend _)).mpr rest))
  | cfg entry count blocks ihe ihb =>
    have entryEquiv := ihe (s := s) hs.1 (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
      (fun {_n _bound i _a _s} => emitCFG_diverges_iff i) agree
    have bodyEquiv := fun (i : Fin count) (current : Value α) (state : σ) =>
      ihb i (hs.2 i) (emit := fun {n} => emitCFG (blocks := count) (exits := labels))
        (s := state) (fun {_n _bound i _a _s} => emitCFG_diverges_iff i) (agree.extend current)
    constructor
    · intro h
      rcases dispatch_diverges_iff.mp h with core | ⟨e, payload, mid, arg, branch⟩
      · cases core.unfold with | core core => cases core with
        | case_scrutinee arg => exact .fold_core (.cfg_entry (entryEquiv.mp arg))
        | case_inl arg branch => cases branch.unfold with | core h => cases h
        | case_inr arg branch =>
          obtain ⟨j, value, source, eq⟩ := encodeRegionWith_reflect hs.1
            (fun {_n _bound i _a _s _s' _result} => emitCFG_eval_iff i) agree arg
          cases j using Fin.addCases with
          | right j => simp [emitValueCFG] at eq
          | left j =>
            have tagged := Value.inr.inj (by simpa [emitValueCFG] using eq)
            cases branch.unfold with | core branch => cases branch with
            | iter_init arg => cases arg.unfold with | core h => cases h
            | iter_loop init loop =>
              obtain ⟨valueEq, stateEq⟩ := eval_bv_result init
              have loop' := loop.map_loop_body
                (fun h => eval_underBinder_iff.mp h) (fun h => diverges_underBinder_iff.mp h)
              have tagged' := valueEq.trans tagged
              rw [stateEq, tagged'] at loop'
              exact .fold_core (.cfg_follow source ((regionLoop_diverges_iff agree bodyEquiv j value _).mp loop'))
      · have impossible := emitDiverges.mp branch
        cases impossible.unfold with | core h => cases h
    · intro h
      apply dispatch_diverges_iff.mpr
      apply Or.inl
      cases h.unfold with | core h => cases h with
      | cfg_entry rest => exact .fold_core (.case_scrutinee (entryEquiv.mpr rest))
      | cfg_follow entry follow =>
        obtain ⟨i, hi, run⟩ := encodeRegionWith_eval entry hs.1
          (fun {_n _bound i _a _s _s' _v} h => emitCFG_eval i h) bound agree
        have inside : i.val < count := by
          rw [hi]
          exact follow_diverges_inside follow
        let j : Fin count := ⟨i.val, inside⟩
        have eq : i = j.castAdd labels := Fin.ext rfl
        rw [eq] at run
        have loop := (regionLoop_diverges_iff agree bodyEquiv j _ _).mpr
          (by simpa only [show j.val = i.val from rfl, hi] using follow)
        refine .fold_core (.case_inr (by simpa [emitValueCFG] using run) ?_)
        exact .fold_core (.iter_loop .bv (loop.map_loop_body
          (fun h => eval_underBinder h) (fun h => diverges_underBinder_iff.mpr h)))

/-- The encoding preserves and reflects divergence, including infinite primitive
computations and arbitrary nested CFG traversal. No typing or determinism is required. -/
theorem encodeRegion_diverges_iff {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hs : r.Scoped labels n) {env : LambdaSSA.Semantics.Env α} {bound : BoundEnv α n} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    Diverges instr free prim (.term bound (encodeRegion r hs) s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim (.region env r s) :=
  encodeRegionWith_diverges_iff hs (fun {_n _bound i _a _s} => inject_diverges_iff i) agree

end Silmaril.Isotope.Morphism.SSAIter.External
