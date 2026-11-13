module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlRefute10

/-!
# Stuck 1.0 control configurations in every environment like `simEnv10` (track v10)

Round 5 refuted the unrestricted `br-zero` leaf in `simEnv10` only (`CtrlRefute10`). The
argument reads three facts about the environment: its relations are those of `simEnv10`, a
`val*` typed there is a run of `CONST`s, `TRAP` is not an `instr` there, and a `labelidx` is a
number. **`Like10 B E`**
collects them; `simEnv10 B` and the corrected `simEnv10T B` satisfy it (`like10_simEnv10`,
`like10_simEnv10T`). This module proves, for every such `E` and at every builtins:

* `z; ε`, `z; x` (for `x` a `BR` or `RETURN`) and `z; x TRAP` are stuck (`not_sstepG_nil`,
  `not_sstepG_one`, `not_sstepG_xTrap`);
* `z; LABEL_ 0 {ε} (x TRAP)` is stuck (`not_sstepG_labX`): `label-vals` needs a body of values,
  and `br-zero`, `br-succ` and `return-label` each type the code after their redex as `instr*`,
  which would make `TRAP` an `instr`; `trap-label` needs the body `TRAP`; `Step/ctxt-label` needs
  the body to step;
* `z; FRAME_ 0 {f} (x TRAP)` is stuck (`not_sstepG_frmX`), likewise through `frame-vals`,
  `return-frame`, `trap-frame` and `Step/ctxt-frame`;
* `z; TRAP TRAP` is stuck (`not_sstepG_trapTrap`): `trap-vals` would type the second `TRAP` as an
  `instr`, and `z; TRAP` is stuck because `trap-vals` needs a non-empty context.

`x` ranges over instruction images (`instrToV i`) that are neither `CONST` nor tagged by any rule
alone; the tag side conditions are closed by `decide` at each use.
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
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SRead SPure Fires cfgV stV
  dderives_iff_fires ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (ruleTags relRules LhsIn TagsIn checkAvoid checkAvoid_sound
  not_ruleBody_of_tags)
open Silmaril.Wasm.SpecTec.Sim20.Whole (not_dderives_of_table)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val quant_listT evalExp_valsN_inv eval_labelVals
  eval_trapVals eval_returnLabel eval_brZero eval_brSucc eval_returnFrame eval_frameVals
  evalExp_caseNil or_of_eval ifPrem labelidxT)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixCase10)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (findRel?_simEnv10T hasTyp_vals10T hasTyp_off10T)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (goodT_of_all)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## Environments like `simEnv10` -/

/-- **What the refutations read of an environment**: the relations of `simEnv10`, `val*` typed
as `CONST`s, and `TRAP` not an `instr`. -/
structure Like10 (E : Env) : Prop where
  rel : ∀ x, E.findRel? x = (simEnv10 B).findRel? x
  consts : ∀ {ρ : VarEnv}, ValsOnly ρ → ∀ {ws : List Value},
    HasTyp E ρ (.iterT (.varT "val" []) .list) (.list ws) → ∀ u ∈ ws, ∃ w, u = .case "CONST" w
  trap : ∀ {ρ : VarEnv}, ValsOnly ρ → ¬ HasTyp E ρ (.varT "instr" []) trapV10
  labelidx : ∀ {ρ : VarEnv}, ValsOnly ρ → ∀ {v : Value}, HasTyp E ρ labelidxT v → ∃ k, v = pctV k

/-- `simEnv10` is like itself. -/
theorem like10_simEnv10 : Like10 B (simEnv10 B) :=
  ⟨fun _ => rfl, fun hρ _ h => consts_of_typed10 hρ h, fun hρ => not_hasTyp_trap_instr10 B hρ,
    fun hρ _ h => labelidx10_inv hρ h⟩

/-- **`TRAP` is not an `instr` in `simEnv10T`**: the corrected declaration renames no case. -/
theorem not_hasTyp_trap_instr10T {ρ : VarEnv} (hρ : ValsOnly ρ) :
    ¬ HasTyp (simEnv10T B) ρ (.varT "instr" []) trapV10 := by
  intro h
  have h₀ : HasTyp (simEnv10T B) VarEnv.empty (.varT "instr" []) trapV10 :=
    Sim.IntNumeric.hasTyp_varT_nil_congr hρ ⟨rfl, rfl, rfl⟩ h
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1
    (Sim20.Whole.hasTypDef_of_closed (instrT_lift (StoreAgree.findTyp_instr10 B)) h₀)
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
  obtain ⟨c, hc', hfix⟩ := List.mem_map.1 hm
  have hn : caseName10 c = "TRAP" := by
    rw [← caseName10_fixCase10, hfix]
    rfl
  exact trap_not_instrCase10 (List.mem_map.2 ⟨c, hc', hn⟩)

/-- **`simEnv10T` is like `simEnv10`.** -/
theorem like10_simEnv10T : Like10 B (simEnv10T B) :=
  ⟨findRel?_simEnv10T B, fun hρ _ h => consts_of_typed10 hρ ((hasTyp_vals10T B hρ.1).1 h),
    fun hρ => not_hasTyp_trap_instr10T B hρ,
    fun hρ _ h => labelidx10_inv hρ ((hasTyp_off10T B hρ.1 (goodT_of_all (by decide))).1 h)⟩

variable {B} {E : Env}

theorem Like10.ruleAt (hL : Like10 B E) {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    (h : HasRuleAt (simEnv10 B) x op k r) : HasRuleAt E x op k r :=
  let ⟨ps, t, rules, hrel, hps, hk⟩ := h
  ⟨ps, t, rules, (hL.rel x).trans hrel, hps, hk⟩

theorem Like10.relRules (hL : Like10 B E) (x : IL.Id) :
    relRules E x = relRules (simEnv10 B) x := by
  unfold Sim.RefsGC.relRules
  rw [hL.rel x]

theorem Like10.findRel (hL : Like10 B E) {x : IL.Id} {t : Typ} {rules : List Rule}
    (h : (simEnv10 B).findRel? x = some ([], "%~>%", t, rules)) :
    E.findRel? x = some ([], "%~>%", t, rules) :=
  (hL.rel x).trans h

/-- An element of a typed `instr*` is a typed `instr`. -/
theorem instr_of_listG {ρ : VarEnv} {rs : List Value} {u : Value}
    (h : HasTyp E ρ (.iterT (.varT "instr" []) .list) (.list rs)) (hu : u ∈ rs) :
    HasTyp E ρ (.varT "instr" []) u := by
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hvs).symm
  exact hasTypList_iff.1 hl u hu

/-! ## The generic kit: `MemSizeRefute`'s lemmas over `E` -/

/-- A `Step` rule outside `exc` does not fire at a left-hand side avoiding its tags. -/
theorem not_fires_step_tagG (hL : Like10 B E) {S : List MixopS} {exc : List Nat} {k : Nat}
    {a w : Value} (ha : LhsIn S a)
    (hc : checkAvoid stepTags10 stepTags10.length exc S = true) (hk : k ∉ exc) :
    ¬ Fires E "Step" k (.tuple [a, w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hT : rules.map ruleTags = stepTags10 := by
    have h₀ := stepTags10_eq
    rw [← relRules_simEnv10 B, ← hL.relRules] at h₀
    simpa [Sim.RefsGC.relRules, hrel] using h₀
  have hlt : k < stepTags10.length := by
    rw [← hT, List.length_map]
    exact (List.getElem?_eq_some_iff.1 hr).1
  have htag : stepTags10[k]?.getD [] = ruleTags r := by
    rw [← hT, List.getElem?_map, hr]
    rfl
  obtain ⟨op, hop, hS⟩ := checkAvoid_sound hc hlt hk
  exact not_ruleBody_of_tags ha (htag ▸ hop) hS hb

/-- No `Step_pure` derivation at a code whose tags avoid every rule outside `exc`. -/
theorem not_spureG (hL : Like10 B E) {S : List MixopS} {exc : List Nat} {l js : List Value}
    (hS : TagsIn S l) (hc : checkAvoid pureTags10 pureTags10.length exc S = true)
    (hexc : ∀ i ∈ exc, ¬ Fires E "Step_pure" i (.tuple [.list l, .list js])) :
    ¬ SPure E l js := by
  obtain ⟨t, rules, hp⟩ := findRel_pure10 B
  refine not_dderives_of_table (hL.findRel hp) (T := pureTags10)
    (by rw [hL.relRules, relRules_simEnv10]; exact pureTags10_eq) (S := S) (exc := exc)
    (Or.inl ⟨_, rfl, hS⟩) hc ?_
  intro i hi r hr hb
  exact hexc i hi ⟨t, rules, r, hL.findRel hp, hr, hb⟩

/-- No `Step_read` derivation at a code whose tags avoid every rule. -/
theorem not_sreadG (hL : Like10 B E) {S : List MixopS} {z : Value} {l js : List Value}
    (hS : TagsIn S l) (hc : checkAvoid readTags10 readTags10.length [] S = true) :
    ¬ SRead E (cfgV z l) js := by
  obtain ⟨t, rules, hr⟩ := findRel_read10 B
  exact not_dderives_of_table (hL.findRel hr) (T := readTags10)
    (by rw [hL.relRules, relRules_simEnv10]; exact readTags10_eq) (S := S) (exc := [])
    (Or.inr ⟨z, _, rfl, hS⟩) hc (fun _ h => absurd h List.not_mem_nil)

/-- `Step/pure` does not fire at `z; l` when `Step_pure` has no step from `l`. -/
theorem not_firesG_pure (hL : Like10 B E) {z w : Value} {l : List Value}
    (hp : ∀ js, ¬ SPure E l js) : ¬ Fires E "Step" 0 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, -, -, hs⟩ := inv_pure10 (hL.ruleAt (hasRuleAt_pure10 B)) hf
  exact hp js ((Sim.Bwd.cfgV_inj h₁).2 ▸ hs)

/-- `Step/read` does not fire at `c` when `Step_read` has no step from `c`. -/
theorem not_firesG_read (hL : Like10 B E) {c w : Value} (hr : ∀ js, ¬ SRead E c js) :
    ¬ Fires E "Step" 1 (.tuple [c, w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, -, -, hs⟩ := inv_read10 (hL.ruleAt (hasRuleAt_read10 B)) hf
  exact hr js (h₁ ▸ hs)

/-- **No `Step` from `z; l`** when the structural rules in `exc` do not fire and `l`'s tags avoid
the other rules. -/
theorem not_sstepG_of (hL : Like10 B E) {z w : Value} {l : List Value} {S : List MixopS}
    {exc : List Nat} (hS : TagsIn S l)
    (hc : checkAvoid stepTags10 stepTags10.length exc S = true)
    (hexc : ∀ i ∈ exc, ¬ Fires E "Step" i (.tuple [cfgV z l, w])) :
    ¬ SStep E (cfgV z l) w := by
  intro hs
  obtain ⟨t, rules, hrel⟩ := findRel_step10 B
  obtain ⟨i, hf⟩ := (dderives_iff_fires (hL.findRel hrel)).1 hs
  by_cases hi : i ∈ exc
  · exact hexc i hi hf
  · exact not_fires_step_tagG hL (Or.inr ⟨z, _, rfl, hS⟩) hc hi hf

/-- `Step/ctxt-instrs` does not fire at `z; ε`. -/
theorem not_firesG_ctxtInstrs_nil (hL : Like10 B E) {z w : Value} :
    ¬ Fires E "Step" 4 (.tuple [cfgV z [], w]) := by
  intro hf
  obtain ⟨z₁, z', vs, is, is', rest, -, hne, h₁, -, -⟩ :=
    inv_ctxtInstrs10 (hL.ruleAt (hasRuleAt_ctxtInstrs10 B)) hf
  have e : vs ++ is ++ rest = [] := ((Sim.Bwd.cfgV_inj h₁).2).symm
  have ev : vs = [] ∧ rest = [] := ⟨by simp_all, by simp_all⟩
  rcases hne with h | h
  · exact h ev.1
  · exact h ev.2

/-- **`z; ε` is stuck.** -/
theorem not_sstepG_nil (hL : Like10 B E) (z w : Value) : ¬ SStep E (cfgV z []) w := by
  refine not_sstepG_of hL (S := []) (exc := [0, 1, 4]) (tagsIn_nil10 _) (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact not_firesG_pure hL fun js => not_spureG hL (exc := []) (tagsIn_nil10 []) (by decide)
      (fun _ h => absurd h List.not_mem_nil)
  · exact not_firesG_read hL fun js => not_sreadG hL (tagsIn_nil10 []) (by decide)
  · exact not_firesG_ctxtInstrs_nil hL

/-- `Step/ctxt-instrs` does not fire at `z; l`, for `l` of length at most one. -/
theorem not_firesG_ctxtInstrs_short (hL : Like10 B E) {z w : Value} {l : List Value}
    (hl : l.length ≤ 1) : ¬ Fires E "Step" 4 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z₁, z', vs, is, is', rest, -, hne, h₁, -, hs⟩ :=
    inv_ctxtInstrs10 (hL.ruleAt (hasRuleAt_ctxtInstrs10 B)) hf
  have his : is = [] := ctxt_mid_nil10 hl hne (Sim.Bwd.cfgV_inj h₁).2
  exact not_sstepG_nil hL z₁ _ (his ▸ hs)

/-! ## One instruction, and one instruction before `TRAP` -/

theorem tagsIn_one {op : MixopS} {p : Value} : TagsIn [op] [.case op p] := by
  intro x hx o w hxw
  obtain rfl := List.mem_singleton.1 hx
  simp only [Value.case.injEq] at hxw
  simp [← hxw.1]

theorem tagsIn_xTrap {op : MixopS} {p : Value} : TagsIn [op, "TRAP"] [.case op p, trapV10] := by
  intro x hx o w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simp only [Value.case.injEq] at hxw
    simp [← hxw.1]
  · simp only [caseNilV, Value.case.injEq] at hxw
    simp [← hxw.1]

/-- **`z; x` is stuck** for an `x` whose tag no rule forces alone. -/
theorem not_sstepG_one (hL : Like10 B E) {op : MixopS} {p : Value}
    (hcp : checkAvoid pureTags10 pureTags10.length [] [op] = true)
    (hcr : checkAvoid readTags10 readTags10.length [] [op] = true)
    (hcs : checkAvoid stepTags10 stepTags10.length [0, 1, 4] [op] = true) (z w : Value) :
    ¬ SStep E (cfgV z [.case op p]) w := by
  refine not_sstepG_of hL (exc := [0, 1, 4]) tagsIn_one hcs ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact not_firesG_pure hL fun js => not_spureG hL (exc := []) tagsIn_one hcp
      (fun _ h => absurd h List.not_mem_nil)
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_one hcr
  · exact not_firesG_ctxtInstrs_short hL (by simp)

/-- `trap-vals` does not fire at `x TRAP` for `x` neither a value nor `TRAP`. -/
theorem not_firesG_trapVals_xTrap (hL : Like10 B E) {x w : Value}
    (hx : ∀ w, x ≠ .case "CONST" w) (ht : x ≠ trapV10) :
    ¬ Fires E "Step_pure" 17 (.tuple [.list [x, trapV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_trapVals B)) hf
  obtain ⟨ws, fv, htv⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hl := (tuple_split (EvalExp.unique he (eval_trapVals fv fi))).1
  have hl' : [x, trapV10] = ws ++ trapV10 :: rs := Value.list.inj hl
  have hn : ws = [] := nil_of_consts10 (hL.consts (Sim.valsOnly_bindVals σ) htv) hx hl'
  rw [hn] at hl'
  exact ht (List.cons.inj hl').1

/-- `Step/ctxt-instrs` does not fire at `z; x TRAP` when `z'; x` is stuck. -/
theorem not_firesG_ctxtInstrs_xTrap (hL : Like10 B E) {z w x : Value}
    (hx : ∀ w, x ≠ .case "CONST" w) (hst : ∀ z' w', ¬ SStep E (cfgV z' [x]) w') :
    ¬ Fires E "Step" 4 (.tuple [cfgV z [x, trapV10], w]) := by
  intro hf
  obtain ⟨z₁, z', vs, is, is', rest, ⟨ρ, hρ, htv⟩, hne, h₁, -, hs⟩ :=
    inv_ctxtInstrs10 (hL.ruleAt (hasRuleAt_ctxtInstrs10 B)) hf
  have he : [x, trapV10] = vs ++ is ++ rest := (Sim.Bwd.cfgV_inj h₁).2
  have hvs : vs = [] := nil_of_consts10 (hL.consts hρ htv) hx (by rw [he, List.append_assoc])
  subst hvs
  have hr : rest ≠ [] := hne.resolve_left (fun h => h rfl)
  rcases split_two10 (by simpa using he.symm) hr with rfl | rfl
  · exact not_sstepG_nil hL z₁ _ hs
  · exact hst z₁ _ hs

/-- **`z; x TRAP` is stuck**, for `x` stuck alone and tagged by no rule except `trap-vals`. -/
theorem not_sstepG_xTrap (hL : Like10 B E) {op : MixopS} {p : Value} (hop : op ≠ "CONST")
    (hT : op ≠ "TRAP")
    (hcp : checkAvoid pureTags10 pureTags10.length [17] [op, "TRAP"] = true)
    (hcr : checkAvoid readTags10 readTags10.length [] [op, "TRAP"] = true)
    (hcs : checkAvoid stepTags10 stepTags10.length [0, 1, 4] [op, "TRAP"] = true)
    (hst : ∀ z' w', ¬ SStep E (cfgV z' [.case op p]) w') (z w : Value) :
    ¬ SStep E (cfgV z [.case op p, trapV10]) w := by
  have hx : ∀ w, Value.case op p ≠ .case "CONST" w := fun _ h => hop (Value.case.inj h).1
  have ht : Value.case op p ≠ trapV10 := fun h => hT (Value.case.inj h).1
  refine not_sstepG_of hL (exc := [0, 1, 4]) tagsIn_xTrap hcs ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · refine not_firesG_pure hL fun js => not_spureG hL (exc := [17]) tagsIn_xTrap hcp ?_
    intro i hi
    obtain rfl : i = 17 := List.mem_singleton.1 hi
    exact not_firesG_trapVals_xTrap hL hx ht
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_xTrap hcr
  · exact not_firesG_ctxtInstrs_xTrap hL hx hst

/-! ## `TRAP TRAP` -/

theorem tagsIn_trap1 : TagsIn ["TRAP"] [trapV10] := tagsIn_one
theorem tagsIn_trap2 : TagsIn ["TRAP"] [trapV10, trapV10] := by
  intro x hx o w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
  subst hx
  simp only [caseNilV, Value.case.injEq] at hxw
  simp [← hxw.1]

theorem trapV10_ne_const : ∀ w, trapV10 ≠ .case "CONST" w := fun _ h => by simp [caseNilV] at h

/-- `trap-vals` does not fire at `TRAP` alone: its context would be empty. -/
theorem not_firesG_trapVals_trap (hL : Like10 B E) {w : Value} :
    ¬ Fires E "Step_pure" 17 (.tuple [.list [trapV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, hp⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_trapVals B)) hf
  obtain ⟨ws, fv, htv⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hl' : [trapV10] = ws ++ trapV10 :: rs :=
    Value.list.inj (tuple_split (EvalExp.unique he (eval_trapVals fv fi))).1
  have hn : ws = [] := nil_of_consts10 (l' := trapV10 :: rs)
    (hL.consts (Sim.valsOnly_bindVals σ) htv) trapV10_ne_const (by simpa using hl')
  rw [hn] at hl'
  have hr : rs = [] := (List.cons.inj hl').2.symm
  have hor : ws ≠ [] ∨ rs ≠ [] := or_of_eval fv fi (ifPrem (hp _ (List.mem_singleton_self _)))
  rcases hor with h | h
  · exact h hn
  · exact h hr

/-- `trap-vals` does not fire at `TRAP TRAP`: the second `TRAP` would be an `instr`. -/
theorem not_firesG_trapVals_trapTrap (hL : Like10 B E) {w : Value} :
    ¬ Fires E "Step_pure" 17 (.tuple [.list [trapV10, trapV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_trapVals B)) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨ws, fv, htv⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hl' : [trapV10, trapV10] = ws ++ trapV10 :: rs :=
    Value.list.inj (tuple_split (EvalExp.unique he (eval_trapVals fv fi))).1
  have hn : ws = [] := nil_of_consts10 (hL.consts hρ htv) trapV10_ne_const hl'
  rw [hn] at hl'
  have hr : rs = [trapV10] := (List.cons.inj hl').2.symm
  rw [hr] at hti
  exact hL.trap hρ (instr_of_listG hti (List.mem_singleton_self _))

/-- **`z; TRAP` is stuck.** -/
theorem not_sstepG_trap (hL : Like10 B E) (z w : Value) : ¬ SStep E (cfgV z [trapV10]) w := by
  refine not_sstepG_of hL (exc := [0, 1, 4]) tagsIn_trap1 (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · refine not_firesG_pure hL fun js => not_spureG hL (exc := [17]) tagsIn_trap1 (by decide) ?_
    intro i hi
    obtain rfl : i = 17 := List.mem_singleton.1 hi
    exact not_firesG_trapVals_trap hL
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_trap1 (by decide)
  · exact not_firesG_ctxtInstrs_short hL (by simp)

/-- **`z; TRAP TRAP` is stuck.** -/
theorem not_sstepG_trapTrap (hL : Like10 B E) (z w : Value) :
    ¬ SStep E (cfgV z [trapV10, trapV10]) w := by
  refine not_sstepG_of hL (exc := [0, 1, 4]) tagsIn_trap2 (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · refine not_firesG_pure hL fun js => not_spureG hL (exc := [17]) tagsIn_trap2 (by decide) ?_
    intro i hi
    obtain rfl : i = 17 := List.mem_singleton.1 hi
    exact not_firesG_trapVals_trapTrap hL
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_trap2 (by decide)
  · exact not_firesG_ctxtInstrs_xTrap hL trapV10_ne_const (not_sstepG_trap hL)

end Silmaril.Wasm.SpecTec.Sim10.Whole
