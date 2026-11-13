module

public import Silmaril.Proofs.Wasm.FnInst.Ground.NumInv
public import Silmaril.Proofs.Wasm.FnInst.Ground.Sim

@[expose] public section

/-! # The bridge for the stack fragment

`nBaseSim : BaseSim P closedHost F NBI NB gCodeRank` at every numerical profile and function
relation. The right side stutters while the left side steps (`pairRef_step`). It commits to
its whole run when the left side has become values (`finish_ok`) or has **stopped** at a
`trap` or a taken `br_if` (`finish_stop`): then both sides are the same values, the same
`trap` or `br`, and the same code after it, so the pair dissolves into equal code.
-/

namespace Silmaril.Wasm.FnInst.Ground.Num

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics
open Silmaril.Wasm.FnInst.Ground (gCodeRank gAdminRank gCodeRank_append gCodeRank_vals
  gCodeRank_cons gCodeRank_nil)

variable {H : Type} {P : Profile}

/-! ## The rank -/

theorem gAdminRank_lower {i : NInstr} (hc : i.isConst = false) :
    gAdminRank (.plain i.lower) = 2 := by
  cases i <;> first | rfl | exact absurd hc (by simp [NInstr.isConst])

theorem bin_rank (t : IntType) (op : IntBinOp) (x y : BitVec t.width) (st : List Val) :
    gCodeRank (match intBinOp t op x y with
      | .ok z => Out1.ok (.num ⟨.int t, z⟩ :: st)
      | .error _ => Out1.stop st .trap).code ≤ st.length + 2 := by
  cases intBinOp t op x y <;> simp [Out1.code, gAdminRank]

theorem brIf_rank (l : LabelIdx) (c : BitVec 32) (st : List Val) :
    gCodeRank (if c = 0 then Out1.ok st else Out1.stop st (.plain (.br l))).code ≤
      st.length + 2 := by
  by_cases h0 : c = 0
  · rw [ite_eq_left h0]
    simp [Out1.code]
  · rw [ite_eq_right h0]
    simp [Out1.code, gAdminRank]

theorem nstep_rank_bin {t : IntType} {op : IntBinOp} {X : List Val} {o : Out1}
    (h : nstep (.bin t op) X = some o) : gCodeRank o.code ≤ X.length + 1 := by
  rcases X with _ | ⟨y, _ | ⟨x, X⟩⟩
  · cases h
  · cases h
  · obtain ⟨a, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h'
    refine le_trans (bin_rank t op a b X) ?_
    simp only [List.length_cons]
    omega

theorem nstep_rank_brIf {l : LabelIdx} {X : List Val} {o : Out1}
    (h : nstep (.brIf l) X = some o) : gCodeRank o.code ≤ X.length + 1 := by
  rcases X with _ | ⟨c, X⟩
  · cases h
  · obtain ⟨cc, -, rfl⟩ := Option.map_eq_some_iff.mp h
    refine le_trans (brIf_rank l cc X) ?_
    simp only [List.length_cons]
    omega

/-- One instruction's outcome weighs at most one more than its input stack. -/
theorem nstep_rank {i : NInstr} {X : List Val} {o : Out1} (h : nstep i X = some o) :
    gCodeRank o.code ≤ X.length + 1 := by
  cases i with
  | bin => exact nstep_rank_bin h
  | brIf => exact nstep_rank_brIf h
  | _ =>
    rcases X with _ | ⟨v, _ | ⟨w, _ | ⟨u, X⟩⟩⟩ <;>
      simp only [nstep, Option.map_eq_some_iff, Option.bind_eq_some_iff, reduceCtorEq,
        Option.some.injEq] at h <;>
      first
      | (obtain rfl := h; simp [Out1.code])
      | (obtain ⟨x, -, rfl⟩ := h; simp [Out1.code])
      | (obtain ⟨x, -, y, -, rfl⟩ := h; simp [Out1.code])

theorem step_rank {i : NInstr} (hc : i.isConst = false) {W : List Val} {o : Out1}
    (h : nstep i W.reverse = some o) (R : List Admin) :
    gCodeRank (o.code ++ R) < gCodeRank (vals W ++ .plain i.lower :: R) := by
  have h₁ := nstep_rank h
  have h₂ := gAdminRank_lower hc
  simp only [gCodeRank_append, gCodeRank_vals, gCodeRank_cons, List.length_reverse, h₂] at h₁ ⊢
  omega

/-! ## Shapes -/

theorem code_split (vs q : List Val) (pre : List NInstr) (hpre : ∀ j ∈ pre, j.isConst = true)
    (i : NInstr) (a₁ : List NInstr) (rest : List Admin) :
    vals vs ++ (vals q ++ expression (lower (pre ++ i :: a₁))) ++ rest =
      vals (vs ++ q ++ cvals pre) ++ .plain i.lower :: (expression (lower a₁) ++ rest) := by
  have hk : expression (lower pre) = vals (cvals pre) := expression_consts hpre
  have e : expression (lower (pre ++ i :: a₁)) =
      vals (cvals pre) ++ .plain i.lower :: expression (lower a₁) := by
    rw [← hk]
    simp [lower, expression]
  rw [e]
  simp [List.append_assoc]

/-- Every left side has a non-value head. -/
theorem nb_head {x y : List Admin} (h : NB x y) (vs : List Val) :
    ∃ (W : List Val) (i : NInstr) (R : List Admin), i.isConst = false ∧ vals vs ++ x = vals W ++ .plain i.lower :: R := by
  obtain ⟨q, a, r, b, rfl, -, ha, -⟩ := h
  obtain ⟨pre, i, a₁, rfl, hpre, hi⟩ := split_op ha
  exact ⟨vs ++ q ++ cvals pre, i, expression (lower a₁), hi,
    by simpa using code_split vs q pre hpre i a₁ []⟩

/-! ## The step law -/

/-- The conclusion of `BaseSim.step`, with the bridge's relations and rank. -/
def StepGoal (P : Profile) (F : FuncInst H → FuncInst H → Prop) (t s' : Store H)
    (f f' : Frame) (vs : List Val) (x y rest rest' es' : List Admin) : Prop :=
  ∃ (t' : Store H) (es'' : List Admin),
    (Relation.TransGen (Step P closedHost) ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t', f', es''⟩ ∨
      (t' = t ∧ f' = f ∧ es'' = vals vs ++ y ++ rest' ∧
        gCodeRank es' < gCodeRank (vals vs ++ x ++ rest))) ∧
    StoreRel F s' t' ∧ AdminsRel NBI NB es' es''

theorem advance {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs : List Val} {x y rest rest' X Z : List Admin} (hst : StoreRel F s t)
    (hXZ : AdminsRel NBI NB X Z)
    (hrun : Steps P closedHost ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t, f, Z ++ rest'⟩)
    (hrank : gCodeRank (X ++ rest) < gCodeRank (vals vs ++ x ++ rest))
    (hrest : AdminsRel NBI NB rest rest') :
    StepGoal P F t s f f vs x y rest rest' (X ++ rest) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrun with he | ht
  · have hz : Z ++ rest' = vals vs ++ y ++ rest' := (Config.mk.inj he).2.2
    exact ⟨t, vals vs ++ y ++ rest', Or.inr ⟨rfl, rfl, rfl, hrank⟩, hst, hz ▸ hXZ.append hrest⟩
  · exact ⟨t, Z ++ rest', Or.inl ht, hst, hXZ.append hrest⟩

/-- The left run from before the step, on a deeper stack. -/
theorem run_left {q vs : List Val} {pre : List NInstr} (hpre : ∀ j ∈ pre, j.isConst = true)
    {i : NInstr} {a₁ : List NInstr} {o : Out1}
    (ho : nstep i (vs ++ q ++ cvals pre).reverse = some o) (S : List Val) :
    run (pre ++ i :: a₁) (q.reverse ++ (vs.reverse ++ S)) = (some (o.app S)).bind fun
      | .ok st' => run a₁ st'
      | .stop st' k => some (.stop st' k a₁) := by
  rw [run_consts hpre, run_cons]
  have e : (cvals pre).reverse ++ (q.reverse ++ (vs.reverse ++ S)) =
      (vs ++ q ++ cvals pre).reverse ++ S := by simp
  rw [e, nstep_app ho S]
  rfl

/-- A step to a new stack keeps equal outcomes. -/
theorem pairRef_step {q r Y vs : List Val} {pre : List NInstr}
    (hpre : ∀ j ∈ pre, j.isConst = true) {i : NInstr} {a₁ b : List NInstr}
    (hp : PairRef q (pre ++ i :: a₁) r b)
    (hY : nstep i (vs ++ q ++ cvals pre).reverse = some (.ok Y)) :
    PairRef Y.reverse a₁ (vs ++ r) b := by
  intro S o h
  have hrun : run (pre ++ i :: a₁) (q.reverse ++ (vs.reverse ++ S)) = some o := by
    rw [run_left hpre hY S]
    simpa [Out1.app] using h
  simpa using hp (vs.reverse ++ S) o hrun

/-- The left side stops at a `trap` or a `br`: the right side runs to the same stop. -/
theorem finish_stop {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs q r Y : List Val} {pre : List NInstr} (hpre : ∀ j ∈ pre, j.isConst = true)
    {i : NInstr} (hi : i.isConst = false) {a₁ b : List NInstr} {k : Admin}
    {rest rest' : List Admin} (hst : StoreRel F s t) (hp : PairRef q (pre ++ i :: a₁) r b)
    (hY : nstep i (vs ++ q ++ cvals pre).reverse = some (.stop Y k))
    (hrest : AdminsRel NBI NB rest rest') :
    StepGoal P F t s f f vs (vals q ++ expression (lower (pre ++ i :: a₁)))
      (vals r ++ expression (lower b)) rest rest'
      ((Out1.stop Y k).code ++ (expression (lower a₁) ++ rest)) := by
  have hrun : run (pre ++ i :: a₁) (q.reverse ++ (vs.reverse ++ [])) =
      some (.stop Y k a₁) := by
    rw [run_left hpre hY []]
    simp [Out1.app]
  have hb : run b (r.reverse ++ (vs.reverse ++ [])) = some (.stop Y k a₁) :=
    hp _ _ hrun
  have hb' : run b (vs ++ r).reverse = some (.stop Y k a₁) := by simpa using hb
  have hsteps := run_steps (P := P) (host := closedHost) hb' t f rest'
  have e₁ : (Out1.stop Y k).code ++ (expression (lower a₁) ++ rest) =
      (vals Y.reverse ++ k :: expression (lower a₁)) ++ rest := by simp [Out1.code]
  have hrank := step_rank hi (W := vs ++ q ++ cvals pre) hY (expression (lower a₁) ++ rest)
  rw [← code_split vs q pre hpre i a₁ rest] at hrank
  rw [e₁]
  rw [e₁] at hrank
  refine advance hst (.refl _) (by simpa [Out.code, List.append_assoc] using hsteps) hrank hrest

/-- The left side has become values: the right side runs to them. -/
theorem finish_ok {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs r Y : List Val} {a₁ b : List NInstr} {x rest rest' : List Admin}
    (hst : StoreRel F s t) (hp' : PairRef Y.reverse a₁ (vs ++ r) b) (hop : ¬ StkOp a₁)
    (hrank : gCodeRank (vals Y.reverse ++ expression (lower a₁) ++ rest) <
      gCodeRank (vals vs ++ x ++ rest))
    (hrest : AdminsRel NBI NB rest rest') :
    StepGoal P F t s f f vs x (vals r ++ expression (lower b)) rest rest'
      (vals Y.reverse ++ expression (lower a₁) ++ rest) := by
  have hc := all_consts hop
  have ha : run a₁ Y = some (.ok ((cvals a₁).reverse ++ Y)) := by
    have h₀ := run_consts hc [] Y
    rw [List.append_nil] at h₀
    exact h₀.trans rfl
  have hb : run b ((vs ++ r).reverse) = some (.ok ((cvals a₁).reverse ++ Y)) := by
    simpa using hp' [] _ (by simpa using ha)
  have hsteps := run_steps (P := P) (host := closedHost) hb t f rest'
  have e : vals Y.reverse ++ expression (lower a₁) = vals ((cvals a₁).reverse ++ Y).reverse := by
    simp [expression_consts hc]
  rw [e]
  rw [e] at hrank
  exact advance hst (.refl _) (by simpa [Out.code, List.append_assoc] using hsteps) hrank hrest

/-- The step law for a step to a new stack. -/
theorem ok_step {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs q r Y : List Val} {pre : List NInstr} (hpre : ∀ j ∈ pre, j.isConst = true)
    {i : NInstr} {a₁ b : List NInstr} {rest rest' : List Admin}
    (hst : StoreRel F s t) (hp : PairRef q (pre ++ i :: a₁) r b)
    (ho : nstep i (vs ++ q ++ cvals pre).reverse = some (.ok Y))
    (hrank : gCodeRank ((Out1.ok Y).code ++ (expression (lower a₁) ++ rest)) <
      gCodeRank (vals vs ++ (vals q ++ expression (lower (pre ++ i :: a₁))) ++ rest))
    (hrest : AdminsRel NBI NB rest rest') :
    StepGoal P F t s f f vs (vals q ++ expression (lower (pre ++ i :: a₁)))
      (vals r ++ expression (lower b)) rest rest'
      ((Out1.ok Y).code ++ (expression (lower a₁) ++ rest)) := by
  have hp' : PairRef Y.reverse a₁ (vs ++ r) b := pairRef_step hpre hp ho
  have e : (Out1.ok Y).code ++ (expression (lower a₁) ++ rest) =
      vals Y.reverse ++ expression (lower a₁) ++ rest := by simp [Out1.code]
  rw [e]
  rw [e] at hrank
  by_cases hop : StkOp a₁
  · have hB : NB (vals Y.reverse ++ expression (lower a₁))
        (vals vs ++ (vals r ++ expression (lower b))) :=
      ⟨Y.reverse, a₁, vs ++ r, b, rfl, by simp, hop, hp'⟩
    exact advance hst (.base hB) .refl (by simpa using hrank) hrest
  · exact finish_ok hst hp' hop hrank hrest

/-- **The step law.** -/
theorem n_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs q r : List Val} {a b : List NInstr} {rest rest' es' : List Admin}
    (hst : StoreRel F s t) (ha : StkOp a) (hp : PairRef q a r b)
    (hrest : AdminsRel NBI NB rest rest')
    (hstep : Step P closedHost ⟨s, f, vals vs ++ (vals q ++ expression (lower a)) ++ rest⟩
      ⟨s', f', es'⟩) :
    StepGoal P F t s' f f' vs (vals q ++ expression (lower a))
      (vals r ++ expression (lower b)) rest rest' es' := by
  obtain ⟨pre, i, a₁, rfl, hpre, hi⟩ := split_op ha
  have hstep' := hstep
  rw [code_split vs q pre hpre] at hstep'
  obtain ⟨o, ho, hc⟩ := nstep_inv hi hstep'
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
  have hrank := step_rank hi ho (expression (lower a₁) ++ rest)
  rw [← code_split vs q pre hpre i a₁ rest] at hrank
  cases o with
  | stop Y k => exact finish_stop hpre hi hst hp ho hrest
  | ok Y => exact ok_step hpre hst hp ho hrank hrest

theorem not_exit_lower {i : NInstr} (hc : i.isConst = false) {W us : List Val}
    {R k j : List Admin} (hk : Exit k) (h : vals W ++ .plain i.lower :: R = vals us ++ k ++ j) :
    False :=
  GuardSim.not_exit (lower_val hc) (by cases i <;> simp [NInstr.lower])
    (by cases i <;> simp [NInstr.lower]) (by cases i <;> simp [NInstr.lower, Admin.IsReturnCallRef])
    (by simp) (by cases i <;> simp [NInstr.lower]) hk h

/-- **The bridge**: good pairs of the stack fragment satisfy silmaril's base obligations, at
every numerical profile, for every function relation. -/
theorem nBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F NBI NB gCodeRank where
  src := by
    rintro x y ⟨a, b, ⟨ha, href⟩, rfl, rfl⟩
    exact ⟨[], a, [], b, rfl, rfl, ha, fun S o h => href _ o h⟩
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨q, a, r, b, rfl, rfl, ha, hp⟩ := hxy
    exact n_step hst ha hp hrest hstep
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    obtain ⟨W, i, R, hi, hW⟩ := nb_head hxy vs
    exact absurd (hW.symm.trans he) (fun h => not_exit_lower hi hk h)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨W, i, R, hi, hW⟩ := nb_head hxy vs
    have hm : Admin.plain i.lower ∈ vals (vs ++ us) := by
      rw [vals_append, ← hx, hW]
      simp
    exact SingleThreaded.Det.mem_vals hm (lower_val hi)

end Silmaril.Wasm.FnInst.Ground.Num
