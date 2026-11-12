module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRun10T

/-!
# The unrestricted `br-zero` leaf is false

Round 3 proved the control leaves `br-zero`, `br-succ`, `return-label`, `return-frame` and
`trap-vals` only at a **plain** suffix (`Plain10`): each of these rules types the code after its
redex as `instr*`, and an administrative instruction (`TRAP`, `LABEL_`, `FRAME_`, `CALL_ADDR`) is
not an `instr`. V1 has no such restriction. This module shows that the restriction is needed, at
`br-zero`:

* the configuration `z; LABEL_ 0 {ε} (BR 0; TRAP)` is typed (the label body is `admininstr*`),
  V1 steps it to `z; ε` (`labelBranch` with tail `TRAP`), and the 1.0 script is **stuck** there
  (`not_sstep10_brTrap`), at every builtins:
  * `Step_pure`: of the rules whose tags fit, `label-vals` needs a body of values, `br-zero` types
    the tail `TRAP` as `instr` (`not_hasTyp_trap_instr10`, kernel check of `instr`'s cases),
    `br-succ` needs `BR (l + 1)`, `return-label` a `RETURN`, `trap-label` a body `TRAP`;
  * `Step/ctxt-label` would need `z; BR 0; TRAP` to step, and it is stuck: `trap-vals` would
    type `BR 0` as a value, and `Step/ctxt-instrs` would need `z; ε` or `z; BR 0` to step;
  * `Step/ctxt-instrs` at one instruction would need `z; ε` to step; the other rules' tags do not
    fit.
* **`not_labelBranchField10`**: so the unrestricted `br-zero` obligation (`LabelBranchField10`,
  round 3's `fwdAt10_labelBranch` for every tail) is false, at every builtins. Round 3's
  restatement at `Plain10` code (`fwdAt10_labelBranchP`) is the documented fix, and `Plain10` holds
  along every V1 run from an invocation (`plain10_steps`, `plain10_invoke`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SRead SPure Fires cfgV
  dderives_iff_fires ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (ruleTags relRules LhsIn TagsIn checkAvoid checkAvoid_sound
  not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (not_dderives_of_table)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val quant_listT evalExp_valsN_inv eval_labelVals
  eval_trapVals eval_returnLabel eval_brZero eval_brSucc labelidxT evalExp_caseNil)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## The values -/

/-- The image of `BR 0`. -/
abbrev brV10 : Value := .case "BR" (pctV 0)

/-- The image of `TRAP`. -/
abbrev trapV10 : Value := caseNilV "TRAP"

/-- The image of the label `LABEL_ 0 {ε} (BR 0; TRAP)`. -/
abbrev labV10 : Value :=
  .case "LABEL_%{%}%" (.tuple [.num (.natN 0), .list [], .list [brV10, trapV10]])

/-- **The code**: a label whose body branches out and then has a `TRAP`. -/
def brTrapCode10 : List Admin := [.label 0 [] [.source (.br ⟨0⟩), .trap]]

theorem adminsToV_brTrap10 : adminsToV brTrapCode10 = [labV10] := rfl

/-! ## `TRAP` is not an `instr` -/

/-- `TRAP` names no case of 1.0's `instr`. -/
theorem trap_not_instrCase10 : "TRAP" ∉ StoreAgree.instrCases10.map caseName10 := by
  decide +kernel

/-- **`TRAP` is not typed as `instr`**, in any scope without type variables. -/
theorem not_hasTyp_trap_instr10 {ρ : VarEnv} (hρ : ValsOnly ρ) :
    ¬ HasTyp (simEnv10 B) ρ (.varT "instr" []) trapV10 := by
  intro h
  have h₀ : HasTyp (simEnv10 B) VarEnv.empty (.varT "instr" []) trapV10 :=
    Sim.IntNumeric.hasTyp_varT_nil_congr hρ ⟨rfl, rfl, rfl⟩ h
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1
    (Sim20.Whole.hasTypDef_of_closed (StoreAgree.findTyp_instr10 B) h₀)
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
  exact trap_not_instrCase10 (List.mem_map.2 ⟨_, hm, rfl⟩)

/-! ## Values in front of a non-value -/

/-- A run of values in front of `x :: l`, with `x` not a value, is empty. -/
theorem nil_of_consts10 {ws l l' : List Value} {x : Value}
    (hc : ∀ u ∈ ws, ∃ w, u = .case "CONST" w) (hx : ∀ w, x ≠ .case "CONST" w)
    (h : x :: l = ws ++ l') : ws = [] := by
  rcases ws with _ | ⟨u, ws⟩
  · rfl
  · obtain ⟨w, hw⟩ := hc u List.mem_cons_self
    have hu : x = u := (List.cons.inj h).1
    exact absurd (hu.trans hw) (hx w)

theorem brV10_ne_const : ∀ w, brV10 ≠ .case "CONST" w := fun _ h => by simp at h

/-- The consts of a `val*` typed in a scope. -/
theorem consts_of_quant10 {ρ : VarEnv} (hρ : ValsOnly ρ) {ws : List Value}
    (h : HasTyp (simEnv10 B) ρ (.iterT (.varT "val" []) .list) (.list ws)) :
    ∀ u ∈ ws, ∃ w, u = .case "CONST" w :=
  consts_of_typed10 hρ h

/-! ## The `Step_pure` rules at the label -/

/-- The label's body, read off a rule's left-hand side `[LABEL_ (n, cs, b)]`. -/
theorem body_of_lhs10 {nv : Value} {cs b : List Value}
    (h : Value.list [labV10] = .list [.case "LABEL_%{%}%" (.tuple [nv, .list cs, .list b])]) :
    b = [brV10, trapV10] := by
  simp only [Value.list.injEq, List.cons.injEq, Value.case.injEq, Value.tuple.injEq,
    and_true, true_and] at h
  exact h.2.2.symm

/-- **`label-vals` does not fire**: the body is not a run of values. -/
theorem not_fires10_labelVals_brTrap (w : Value) :
    ¬ Fires (simEnv10 B) "Step_pure" 7 (.tuple [.list [labV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hasRuleAt10_labelVals B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  have hb := body_of_lhs10 (tuple_split (EvalExp.unique he (eval_labelVals fn fc fv))).1
  have hn := nil_of_consts10 (l' := []) (consts_of_quant10 B (Sim.valsOnly_bindVals σ) ht)
    brV10_ne_const (by rw [List.append_nil, hb])
  rw [hn] at hb
  exact List.cons_ne_nil _ _ hb.symm

/-- An element of a typed `instr*` is a typed `instr`. -/
theorem instr_of_list10 {ρ : VarEnv} {rs : List Value} {u : Value}
    (h : HasTyp (simEnv10 B) ρ (.iterT (.varT "instr" []) .list) (.list rs)) (hu : u ∈ rs) :
    HasTyp (simEnv10 B) ρ (.varT "instr" []) u := by
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hvs).symm
  exact hasTypList_iff.1 hl u hu

/-- The body `val'* val^n (BR 0) instr*` of `br-zero`, matched against `BR 0; TRAP`. -/
theorem brZero_tail10 {ws₁ ws rs : List Value} (hc : ∀ u ∈ ws₁ ++ ws, ∃ w, u = .case "CONST" w)
    (hb : ws₁ ++ ws ++ [.case "BR" (pctV 0)] ++ rs = [brV10, trapV10]) : rs = [trapV10] := by
  have hn : ws₁ ++ ws = [] := nil_of_consts10 (l := [trapV10]) (l' := .case "BR" (pctV 0) :: rs)
    hc brV10_ne_const (by rw [← hb]; simp)
  rw [hn] at hb
  simpa using hb

/-- **`br-zero` does not fire**: its tail `TRAP` would be an `instr`. -/
theorem not_fires10_brZero_brTrap (w : Value) :
    ¬ Fires (simEnv10 B) "Step_pure" 8 (.tuple [.list [labV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hasRuleAt10_brZero B) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht'⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨v₁, v₂, h₁, -, -⟩ := evalExp_catE_iff.1 (Sim.RefsGC.rhs_of_concl he)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) h₁
  obtain rfl : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hb := body_of_lhs10 (tuple_split (EvalExp.unique he (eval_brZero fn fc fv₁ fv fi))).1
  have hc : ∀ u ∈ ws₁ ++ ws', ∃ w, u = .case "CONST" w := fun u hu =>
    (List.mem_append.1 hu).elim (consts_of_quant10 B hρ ht₁ u) (consts_of_quant10 B hρ ht' u)
  have hrs := brZero_tail10 hc hb
  rw [hrs] at hti
  exact not_hasTyp_trap_instr10 B hρ (instr_of_list10 B hti (List.mem_singleton_self _))

/-- **`br-succ` does not fire**: the branch is to label `0`. -/
theorem not_fires10_brSucc_brTrap (w : Value) :
    ¬ Fires (simEnv10 B) "Step_pure" 9 (.tuple [.list [labV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hasRuleAt10_brSucc B) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨lv, fl, hlt⟩ := hq "l" labelidxT (by simp)
  obtain ⟨k, rfl⟩ := labelidx10_inv hρ hlt
  obtain ⟨rs, fi, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hb := body_of_lhs10 (tuple_split (EvalExp.unique he (eval_brSucc fn fc fv fl fi))).1
  have hn : ws = [] := nil_of_consts10 (l := [trapV10]) (l' := .case "BR" (pctV (k + 1)) :: rs)
    (consts_of_quant10 B hρ ht) brV10_ne_const (by rw [← hb]; simp)
  rw [hn] at hb
  have h0 : pctV 0 = pctV (k + 1) := by simpa using hb.symm
  exact absurd (Sim20.Pure.pctV_inj h0) (by omega)

/-- **`return-label` does not fire**: the body has no `RETURN`. -/
theorem not_fires10_returnLabel_brTrap (w : Value) :
    ¬ Fires (simEnv10 B) "Step_pure" 16 (.tuple [.list [labV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hasRuleAt10_returnLabel B) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hb := body_of_lhs10 (tuple_split (EvalExp.unique he (eval_returnLabel fn fc fv fi))).1
  have hn : ws = [] := nil_of_consts10 (l := [trapV10]) (l' := caseNilV "RETURN" :: rs)
    (consts_of_quant10 B hρ ht) brV10_ne_const (by rw [← hb]; simp)
  rw [hn] at hb
  simp [caseNilV] at hb

/-- **`trap-label` does not fire**: the body is not `TRAP` alone. -/
theorem not_fires10_trapLabel_brTrap (w : Value) :
    ¬ Fires (simEnv10 B) "Step_pure" 18 (.tuple [.list [labV10], w]) := by
  intro hf
  rw [← adminsToV_brTrap10] at hf
  obtain ⟨σ, -, hes, -, -⟩ := firesPure10_inv (hasRuleAt10_trapLabel B) hf
  obtain ⟨a, ha, he⟩ := codes10_one hes
  obtain rfl : a = .label 0 [] [.source (.br ⟨0⟩), .trap] := by
    simpa [brTrapCode10] using ha.symm
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 he
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, -, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, -, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  have hb : Value.list [brV10, trapV10] = u₃ := by
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
    exact hcu.2.2.1
  have hb' := hb.trans (EvalExp.unique h₃ (Sim.evalExp_list1 evalExp_caseNil))
  simp at hb'

/-! ## `z; BR 0; TRAP` is stuck -/

/-- **`trap-vals` does not fire at `BR 0; TRAP`**: `BR 0` is not a value. -/
theorem not_fires10_trapVals_brTrap (w : Value) :
    ¬ Fires (simEnv10 B) "Step_pure" 17 (.tuple [.list [brV10, trapV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hasRuleAt10_trapVals B) hf
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hl := (tuple_split (EvalExp.unique he (eval_trapVals fv fi))).1
  have hl' : [brV10, trapV10] = ws ++ trapV10 :: rs := Value.list.inj hl
  have hn : ws = [] := nil_of_consts10 (consts_of_quant10 B (Sim.valsOnly_bindVals σ) ht)
    brV10_ne_const hl'
  rw [hn] at hl'
  simp [caseNilV] at hl'

theorem tagsIn_br10 : TagsIn ["BR"] [brV10] := by
  intro x hx op w hxw
  obtain rfl := List.mem_singleton.1 hx
  simp only [Value.case.injEq] at hxw
  simp [← hxw.1]

theorem tagsIn_brTrap10 : TagsIn ["BR", "TRAP"] [brV10, trapV10] := by
  intro x hx op w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simp only [Value.case.injEq] at hxw
    simp [← hxw.1]
  · simp only [caseNilV, Value.case.injEq] at hxw
    simp [← hxw.1]

theorem tagsIn_lab10 : TagsIn ["LABEL_%{%}%"] [labV10] := by
  intro x hx op w hxw
  obtain rfl := List.mem_singleton.1 hx
  simp only [Value.case.injEq] at hxw
  simp [← hxw.1]

/-- **`z; BR 0` is stuck.** -/
theorem not_sstep10_br0 (z w : Value) : ¬ SStep (simEnv10 B) (cfgV z [brV10]) w := by
  obtain ⟨t, rules, hp⟩ := findRel_pure10 B
  obtain ⟨t', rules', hr⟩ := findRel_read10 B
  refine not_sstep10_of B tagsIn_br10 (by decide) (not_fires10_pure B fun js => ?_)
    (not_fires10_read B fun js => ?_) (not_fires10_ctxtInstrs B (by decide) (not_sstep10_nil B))
  · exact not_dderives_of_table hp (T := pureTags10)
      (by rw [relRules_simEnv10]; exact pureTags10_eq) (S := ["BR"]) (exc := [])
      (Or.inl ⟨_, rfl, tagsIn_br10⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)
  · exact not_dderives_of_table hr (T := readTags10)
      (by rw [relRules_simEnv10]; exact readTags10_eq) (S := ["BR"]) (exc := [])
      (Or.inr ⟨z, _, rfl, tagsIn_br10⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)

/-- A split of a two-element list with a non-empty right part. -/
theorem split_two10 {α : Type} {a b : α} {is rest : List α} (h : is ++ rest = [a, b])
    (hne : rest ≠ []) : is = [] ∨ is = [a] := by
  rcases is with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact .inl rfl
  · exact .inr (by simp at h; rw [h.1])
  · simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨-, -, h'⟩ := h
    exact absurd (List.append_eq_nil_iff.1 h').2 hne

/-- `Step/ctxt-instrs` does not fire at `z; BR 0; TRAP`. -/
theorem not_fires10_ctxtInstrs_brTrap (z w : Value) :
    ¬ Fires (simEnv10 B) "Step" 4 (.tuple [cfgV z [brV10, trapV10], w]) := by
  intro hf
  obtain ⟨z₁, z', vs, is, is', rest, ⟨ρ, hρ, htv⟩, hne, h₁, -, hs⟩ :=
    inv_ctxtInstrs10 (hasRuleAt_ctxtInstrs10 B) hf
  have he : [brV10, trapV10] = vs ++ is ++ rest := (Sim.Bwd.cfgV_inj h₁).2
  have hvs : vs = [] := nil_of_consts10 (consts_of_quant10 B hρ htv) brV10_ne_const
    (by rw [he, List.append_assoc])
  subst hvs
  have hr : rest ≠ [] := hne.resolve_left (fun h => h rfl)
  rcases split_two10 (by simpa using he.symm) hr with rfl | rfl
  · exact not_sstep10_nil B z₁ _ hs
  · exact not_sstep10_br0 B z₁ _ hs

/-- **`z; BR 0; TRAP` is stuck.** -/
theorem not_sstep10_brTrapBody (z w : Value) :
    ¬ SStep (simEnv10 B) (cfgV z [brV10, trapV10]) w := by
  obtain ⟨t, rules, hp⟩ := findRel_pure10 B
  obtain ⟨t', rules', hr⟩ := findRel_read10 B
  refine not_sstep10_of B tagsIn_brTrap10 (by decide) (not_fires10_pure B fun js => ?_)
    (not_fires10_read B fun js => ?_) (not_fires10_ctxtInstrs_brTrap B z w)
  · refine not_dderives_of_table hp (T := pureTags10)
      (by rw [relRules_simEnv10]; exact pureTags10_eq) (S := ["BR", "TRAP"]) (exc := [17])
      (Or.inl ⟨_, rfl, tagsIn_brTrap10⟩) (by decide) ?_
    intro i hi r hr' hb
    obtain rfl : i = 17 := List.mem_singleton.1 hi
    exact not_fires10_trapVals_brTrap B _ ⟨t, rules, r, hp, hr', hb⟩
  · exact not_dderives_of_table hr (T := readTags10)
      (by rw [relRules_simEnv10]; exact readTags10_eq) (S := ["BR", "TRAP"]) (exc := [])
      (Or.inr ⟨z, _, rfl, tagsIn_brTrap10⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)

/-! ## `z; LABEL_ 0 {ε} (BR 0; TRAP)` is stuck -/

/-- A `Step` rule outside 0, 1, 2 and 4 does not fire at a left-hand side avoiding its tags. -/
theorem not_fires_step_tag10' {S : List MixopS} {k : Nat} {a w : Value} (ha : LhsIn S a)
    (hc : checkAvoid stepTags10 stepTags10.length [0, 1, 2, 4] S = true) (hk : k ∉ [0, 1, 2, 4]) :
    ¬ Fires (simEnv10 B) "Step" k (.tuple [a, w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hT : rules.map ruleTags = stepTags10 := by
    have h₀ := stepTags10_eq
    rw [← relRules_simEnv10 B] at h₀
    simpa [relRules, hrel] using h₀
  have hlt : k < stepTags10.length := by
    rw [← hT, List.length_map]
    exact (List.getElem?_eq_some_iff.1 hr).1
  have htag : stepTags10[k]?.getD [] = ruleTags r := by
    rw [← hT, List.getElem?_map, hr]
    rfl
  obtain ⟨op, hop, hS⟩ := checkAvoid_sound hc hlt hk
  exact not_ruleBody_of_tags ha (htag ▸ hop) hS hb

/-- `Step/ctxt-label` does not fire at the label: its body `BR 0; TRAP` is stuck. -/
theorem not_fires10_ctxtLabel_brTrap (z w : Value) :
    ¬ Fires (simEnv10 B) "Step" 2 (.tuple [cfgV z [labV10], w]) := by
  intro hf
  obtain ⟨z₁, z', n, cont, is, is', h₁, -, hs⟩ := inv_ctxtLabel10 (hasRuleAt_ctxtLabel10 B) hf
  have he := (Sim.Bwd.cfgV_inj h₁).2
  simp only [List.cons.injEq, Value.case.injEq, Value.tuple.injEq, Value.list.injEq,
    and_true, true_and] at he
  rw [← he.2.2] at hs
  exact not_sstep10_brTrapBody B z₁ _ hs

/-- The `Step_pure` rules at the label: 7, 8, 9, 16 and 18 do not fire, the others' tags do not
fit. -/
theorem not_spure10_lab (js : List Value) : ¬ SPure (simEnv10 B) [labV10] js := by
  obtain ⟨t, rules, hp⟩ := findRel_pure10 B
  refine not_dderives_of_table hp (T := pureTags10)
    (by rw [relRules_simEnv10]; exact pureTags10_eq) (S := ["LABEL_%{%}%"])
    (exc := [7, 8, 9, 16, 18]) (Or.inl ⟨_, rfl, tagsIn_lab10⟩) (by decide) ?_
  intro i hi r hr hb
  have hf : Fires (simEnv10 B) "Step_pure" i (.tuple [.list [labV10], .list js]) :=
    ⟨t, rules, r, hp, hr, hb⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact not_fires10_labelVals_brTrap B _ hf
  · exact not_fires10_brZero_brTrap B _ hf
  · exact not_fires10_brSucc_brTrap B _ hf
  · exact not_fires10_returnLabel_brTrap B _ hf
  · exact not_fires10_trapLabel_brTrap B _ hf

/-- **`z; LABEL_ 0 {ε} (BR 0; TRAP)` is stuck in the wasm-1.0 script**, at every builtins. -/
theorem not_sstep10_brTrap (z w : Value) : ¬ SStep (simEnv10 B) (cfgV z [labV10]) w := by
  intro hs
  obtain ⟨t, rules, hrel⟩ := findRel_step10 B
  obtain ⟨t', rules', hr⟩ := findRel_read10 B
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  by_cases hi : i ∈ [0, 1, 2, 4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact not_fires10_pure B (not_spure10_lab B) hf
    · refine not_fires10_read B (fun js => ?_) hf
      exact not_dderives_of_table hr (T := readTags10)
        (by rw [relRules_simEnv10]; exact readTags10_eq) (S := ["LABEL_%{%}%"]) (exc := [])
        (Or.inr ⟨z, _, rfl, tagsIn_lab10⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)
    · exact not_fires10_ctxtLabel_brTrap B z w hf
    · exact not_fires10_ctxtInstrs B (by decide) (not_sstep10_nil B) hf
  · exact not_fires_step_tag10' B (Or.inr ⟨z, _, rfl, tagsIn_lab10⟩) (by decide) hi hf

/-! ## The witness -/

/-- An empty store. -/
def emptyStore10 (H : Type) : Store H := {}

/-- A frame over the empty module. -/
def emptyFrame10 : Frame := { module := {} }

/-- **The configuration**: `LABEL_ 0 {ε} (BR 0; TRAP)` over the empty store. -/
def brTrapCfg10 (H : Type) : Config H := ⟨emptyStore10 H, emptyFrame10, brTrapCode10⟩

/-- What V1 steps it to: the empty code. -/
def brTrapCfg10' (H : Type) : Config H := ⟨emptyStore10 H, emptyFrame10, []⟩

/-- **V1 steps it**, by `labelBranch` with the tail `TRAP`. -/
theorem step_brTrap10 {H : Type} (host : HostSemantics H) :
    Step host (brTrapCfg10 H) (brTrapCfg10' H) :=
  .pure _ _ (.labelBranch 0 [] [] [] [.trap] rfl)

set_option maxHeartbeats 4000000 in
theorem typed10_brTrap {H : Type} (hn : H → String) : Typed10 (simEnv10 B) hn (brTrapCfg10 H) :=
  ⟨100, by with_unfolding_all rfl⟩

set_option maxHeartbeats 4000000 in
theorem typed10_brTrap' {H : Type} (hn : H → String) : Typed10 (simEnv10 B) hn (brTrapCfg10' H) :=
  ⟨100, by with_unfolding_all rfl⟩

/-- **The script is stuck there** under the backend reading. -/
theorem stuck10_brTrap {H : Type} (hn : H → String) (w : Value) :
    ¬ SStepB (simEnv10 B) (configV hn (brTrapCfg10 H)) w := by
  intro h
  have h' := (sstepB10_iff B).1 h
  rw [configV_eq_cfgV10, show (brTrapCfg10 H).code = brTrapCode10 from rfl,
    adminsToV_brTrap10] at h'
  exact not_sstep10_brTrap B _ _ h'

/-- **The unrestricted `br-zero` obligation**: round 3's `fwdAt10_labelBranch` for every tail. -/
def LabelBranchField10 {H : Type} (B : Builtins) (hn : H → String) : Prop :=
  ∀ (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) (extra vs : List Execution.Runtime.Value)
    (tail : List Admin), vs.length = n →
    FwdAt10 B hn ⟨s, f, [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)]⟩
      ⟨s, f, values vs ++ expression cont⟩

/-- **The unrestricted `br-zero` obligation is false**, at every builtins: at
`LABEL_ 0 {ε} (BR 0; TRAP)` both images are typed, V1 steps, and the 1.0 script is stuck. -/
theorem not_labelBranchField10 {H : Type} (hn : H → String) : ¬ LabelBranchField10 B hn := by
  intro F
  have hc := typed10_brTrap B hn (H := H)
  have hc' := typed10_brTrap' B hn (H := H)
  exact stuck10_brTrap B hn _ (F (emptyStore10 H) emptyFrame10 0 [] [] [] [.trap] rfl
    (typedV_state_of_typed10 hc) (typedV_state_of_typed10 hc') (typedV_code_of_typed10 hc)
    (typedV_code_of_typed10 hc'))

end Silmaril.Wasm.SpecTec.Sim10.Whole
