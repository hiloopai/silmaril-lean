module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlRefuteAll

/-!
# `trap-vals` in V1's `trapValues` form is false unrestricted

An earlier step refuted the unrestricted `trap-vals` obligation in V1's `trapTail` form only
(`not_trapTailField10`). The `trapValues` form, with a non-empty value prefix, was left open:
at `CONST; TRAP; TRAP` the script is not stuck, since `trap-vals` fires on `CONST; TRAP` inside
`Step/ctxt-instrs`, giving `TRAP; TRAP`. A refutation has to rule out the one step V1 takes, to
`TRAP`.

This module does that, in every environment like `simEnv10` (`Like10`) and at every builtins:

* `not_sstepG_constTrap_nil`: `z; CONST TRAP` does not step to `z'; ε`. `trap-vals` is the only
  pure rule whose tags fit, and it yields `TRAP`; `Step/ctxt-instrs` would need an empty value
  prefix and an empty tail, which its side condition forbids.
* **`not_sstepG_constTrapTrap_trap`**: `z; CONST TRAP TRAP` does not step to `z'; TRAP`.
  `trap-vals` would type the last `TRAP` as an `instr`. `Step/ctxt-instrs` with a value prefix
  keeps the `CONST` in front of the result; with an empty prefix its tail must be the last
  `TRAP`, so the inner step is `CONST TRAP` to `ε`, which the first lemma rules out.

The witness is `CONST i32 0; TRAP; TRAP` over the empty store and frame; V1 steps it to `TRAP`
by `trapValues`, and both images are IL-typed (kernel evaluation of the type checker). So the
unrestricted `TrapValuesField10` and `TrapValuesField10T` are false. Round 3's restatement at a
plain suffix (`fwdAt10_trapValues`) is the documented fix, as for the other control leaves.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm.SpecTec.Sim (SStep SPure Fires cfgV)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_listT eval_trapVals)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (typed10T_of_typed10)

set_option maxRecDepth 100000

variable {B : Builtins} {E : Env}

/-! ## Tags -/

theorem tagsIn_constTrap {p : Value} : TagsIn ["CONST", "TRAP"] [.case "CONST" p, trapV10] := by
  intro x hx o w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simp only [Value.case.injEq] at hxw
    simp [← hxw.1]
  · simp only [caseNilV, Value.case.injEq] at hxw
    simp [← hxw.1]

theorem tagsIn_constTrapTrap {p : Value} :
    TagsIn ["CONST", "TRAP"] [.case "CONST" p, trapV10, trapV10] := by
  intro x hx o w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simp only [Value.case.injEq] at hxw
    simp [← hxw.1]
  all_goals
    simp only [caseNilV, Value.case.injEq] at hxw
    simp [← hxw.1]

/-! ## `CONST TRAP` does not step to `ε` -/

/-- `trap-vals` does not take any code to `ε`: its right-hand side is `TRAP`. -/
theorem not_firesG_trapVals_nil (hL : Like10 B E) {l : List Value} :
    ¬ Fires E "Step_pure" 17 (.tuple [.list l, .list []]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_trapVals B)) hf
  obtain ⟨ws, fv, -⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hr := (tuple_split (EvalExp.unique he (eval_trapVals fv fi))).2
  exact absurd (Value.list.inj hr) (by simp)

/-- `Step/pure` does not take `z; CONST TRAP` to `z'; ε`. -/
theorem not_firesG_pure_constTrap_nil (hL : Like10 B E) {p z z' : Value} :
    ¬ Fires E "Step" 0 (.tuple [cfgV z [.case "CONST" p, trapV10], cfgV z' []]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, h₂, -, -, hs⟩ := inv_pure10 (hL.ruleAt (hasRuleAt_pure10 B)) hf
  have hjs : js = [] := ((Sim.Bwd.cfgV_inj h₂).2).symm
  have his : is = [.case "CONST" p, trapV10] := ((Sim.Bwd.cfgV_inj h₁).2).symm
  subst hjs his
  refine not_spureG hL (exc := [17]) tagsIn_constTrap (by decide) ?_ hs
  intro i hi
  obtain rfl : i = 17 := List.mem_singleton.1 hi
  exact not_firesG_trapVals_nil hL

/-- `Step/ctxt-instrs` takes no code to `z'; ε`. -/
theorem not_firesG_ctxtInstrs_to_nil (hL : Like10 B E) {v z' : Value} :
    ¬ Fires E "Step" 4 (.tuple [v, cfgV z' []]) := by
  intro hf
  obtain ⟨z₁, z₂, vs, is, is', rest, -, hne, -, h₂, -⟩ :=
    inv_ctxtInstrs10 (hL.ruleAt (hasRuleAt_ctxtInstrs10 B)) hf
  have e : vs ++ is' ++ rest = [] := ((Sim.Bwd.cfgV_inj h₂).2).symm
  rcases hne with h | h
  · exact h (by simp_all)
  · exact h (by simp_all)

/-- **`z; CONST TRAP` does not step to `z'; ε`.** -/
theorem not_sstepG_constTrap_nil (hL : Like10 B E) (p z z' : Value) :
    ¬ SStep E (cfgV z [.case "CONST" p, trapV10]) (cfgV z' []) := by
  refine not_sstepG_of hL (exc := [0, 1, 4]) tagsIn_constTrap (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact not_firesG_pure_constTrap_nil hL
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_constTrap (by decide)
  · exact not_firesG_ctxtInstrs_to_nil hL

/-! ## `CONST TRAP TRAP` does not step to `TRAP` -/

/-- `trap-vals` does not fire at `CONST TRAP TRAP`: the last `TRAP` would be an `instr`. -/
theorem not_firesG_trapVals_constTrapTrap (hL : Like10 B E) {p w : Value} :
    ¬ Fires E "Step_pure" 17 (.tuple [.list [.case "CONST" p, trapV10, trapV10], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_trapVals B)) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨ws, fv, htv⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hl' : [.case "CONST" p, trapV10, trapV10] = ws ++ trapV10 :: rs :=
    Value.list.inj (tuple_split (EvalExp.unique he (eval_trapVals fv fi))).1
  have hc := hL.consts hρ htv
  rcases ws with _ | ⟨u, ws⟩
  · exact absurd (List.cons.inj hl').1 (by simp [caseNilV])
  · have ht : [trapV10, trapV10] = ws ++ trapV10 :: rs := (List.cons.inj hl').2
    have hn : ws = [] :=
      nil_of_consts10 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) trapV10_ne_const ht
    rw [hn] at ht
    have hr : rs = [trapV10] := (List.cons.inj ht).2.symm
    rw [hr] at hti
    exact hL.trap hρ (instr_of_listG hti (List.mem_singleton_self _))

/-- The split of `CONST TRAP TRAP` that `Step/ctxt-instrs` would need for the target `TRAP`. -/
theorem ctxt_split_constTrapTrap {x : Value} {vs is is' rest : List Value}
    (hvs : vs = []) (hne : rest ≠ [])
    (h₁ : [x, trapV10, trapV10] = vs ++ is ++ rest) (h₂ : [trapV10] = vs ++ is' ++ rest) :
    is = [x, trapV10] ∧ is' = [] := by
  subst hvs
  simp only [List.nil_append] at h₁ h₂
  rcases is' with _ | ⟨a, is'⟩
  · simp only [List.nil_append] at h₂
    subst h₂
    refine ⟨?_, rfl⟩
    have := congrArg List.dropLast h₁
    simpa using this.symm
  · simp only [List.cons_append, List.cons.injEq] at h₂
    exact absurd (List.append_eq_nil_iff.1 h₂.2.symm).2 hne

/-- `Step/ctxt-instrs` does not take `z; CONST TRAP TRAP` to `z'; TRAP`. -/
theorem not_firesG_ctxtInstrs_constTrapTrap (hL : Like10 B E) {p z z' : Value} :
    ¬ Fires E "Step" 4 (.tuple [cfgV z [.case "CONST" p, trapV10, trapV10], cfgV z' [trapV10]]) := by
  intro hf
  obtain ⟨z₁, z₂, vs, is, is', rest, ⟨ρ, hρ, htv⟩, hne, h₁, h₂, hs⟩ :=
    inv_ctxtInstrs10 (hL.ruleAt (hasRuleAt_ctxtInstrs10 B)) hf
  have e₁ : [.case "CONST" p, trapV10, trapV10] = vs ++ is ++ rest := (Sim.Bwd.cfgV_inj h₁).2
  have e₂ : [trapV10] = vs ++ is' ++ rest := (Sim.Bwd.cfgV_inj h₂).2
  have hvs : vs = [] := nil_of_consts10 (x := trapV10) (hL.consts hρ htv) trapV10_ne_const
    (by rw [e₂, List.append_assoc])
  have hr : rest ≠ [] := hne.resolve_left (fun h => h hvs)
  obtain ⟨rfl, rfl⟩ := ctxt_split_constTrapTrap hvs hr e₁ e₂
  exact not_sstepG_constTrap_nil hL p z₁ z₂ hs

/-- **`z; CONST TRAP TRAP` does not step to `z'; TRAP`.** -/
theorem not_sstepG_constTrapTrap_trap (hL : Like10 B E) (p z z' : Value) :
    ¬ SStep E (cfgV z [.case "CONST" p, trapV10, trapV10]) (cfgV z' [trapV10]) := by
  refine not_sstepG_of hL (exc := [0, 1, 4]) tagsIn_constTrapTrap (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · refine not_firesG_pure hL fun js => not_spureG hL (exc := [17]) tagsIn_constTrapTrap
      (by decide) fun i hi => ?_
    obtain rfl : i = 17 := List.mem_singleton.1 hi
    exact not_firesG_trapVals_constTrapTrap hL
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_constTrapTrap (by decide)
  · exact not_firesG_ctxtInstrs_constTrapTrap hL

/-! ## The witness and the refutations -/

variable {H : Type} (hn : H → String)

/-- `i32.const 0`. -/
def zero32 : Execution.Runtime.Value := ⟨.int .i32, 0⟩

/-- `CONST i32 0; TRAP; TRAP`. -/
def constTrapTrapCode10 : List Admin := values [zero32] ++ [.trap] ++ [.trap]

/-- **V1 steps it to `TRAP`**, by `trapValues`. -/
theorem step_constTrapTrap10 (host : HostSemantics H) :
    Step host (cfgE10 H constTrapTrapCode10) (cfgE10 H [.trap]) :=
  .pure _ _ (.trapValues zero32 [] [.trap])

set_option maxHeartbeats 4000000 in
theorem typed10_constTrapTrap : Typed10 (simEnv10 B) hn (cfgE10 H constTrapTrapCode10) :=
  ⟨100, by with_unfolding_all rfl⟩

/-- **The unrestricted `trap-vals` obligation, V1's `trapValues` form.** -/
def TrapValuesField10 (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (v : Execution.Runtime.Value) (vs : List Execution.Runtime.Value)
    (tail : List Admin), FwdAt10 B hn ⟨s, f, values (v :: vs) ++ [.trap] ++ tail⟩ ⟨s, f, [.trap]⟩

/-- `trap-vals` (`trapValues`) in `simEnv10T`. -/
def TrapValuesField10T (B : Builtins) : Prop :=
  ∀ (s : Store H) (f : Frame) (v : Execution.Runtime.Value) (vs : List Execution.Runtime.Value)
    (tail : List Admin),
    FwdAt10T B hn ⟨s, f, values (v :: vs) ++ [.trap] ++ tail⟩ ⟨s, f, [.trap]⟩

/-- The image of `CONST i32 0; TRAP; TRAP`. -/
theorem adminsToV_constTrapTrap :
    ∃ p, adminsToV constTrapTrapCode10 = [.case "CONST" p, trapV10, trapV10] :=
  ⟨_, rfl⟩

/-- **The unrestricted `trap-vals` obligation (`trapValues`) is false**, at every builtins. -/
theorem not_trapValuesField10 : ¬ TrapValuesField10 hn B := by
  intro F
  have h := F (emptyStore10 H) emptyFrame10 zero32 [] [.trap]
    (typedV_state_of_typed10 (typed10_constTrapTrap hn)) (typedV_state_of_typed10 (typed10_trap hn))
    (typedV_code_of_typed10 (typed10_constTrapTrap hn)) (typedV_code_of_typed10 (typed10_trap hn))
  obtain ⟨p, hp⟩ := adminsToV_constTrapTrap
  have h' := (sstepB10_iff B).1 h
  exact not_sstepG_constTrapTrap_trap (like10_simEnv10 B) p _ _ (by
    change SStep _ (cfgV _ (adminsToV constTrapTrapCode10)) (cfgV _ (adminsToV [.trap])) at h'
    rw [hp] at h'
    exact h')

/-- **The unrestricted `trap-vals` obligation (`trapValues`) is false in `simEnv10T`.** -/
theorem not_trapValuesField10T : ¬ TrapValuesField10T hn B := by
  intro F
  have t₁ := typed10T_of_typed10 (typed10_constTrapTrap (B := B) hn)
  have t₂ := typed10T_of_typed10 (typed10_trap (B := B) hn)
  have h := F (emptyStore10 H) emptyFrame10 zero32 [] [.trap]
    (typedV_state_of_typed10T t₁) (typedV_state_of_typed10T t₂)
    (typedV_code_of_typed10T t₁) (typedV_code_of_typed10T t₂)
  obtain ⟨p, hp⟩ := adminsToV_constTrapTrap
  have h' := (Sim10.StoreFix.sstepB10T_iff B).1 h
  exact not_sstepG_constTrapTrap_trap (like10_simEnv10T B) p _ _ (by
    change SStep _ (cfgV _ (adminsToV constTrapTrapCode10)) (cfgV _ (adminsToV [.trap])) at h'
    rw [hp] at h'
    exact h')

end Silmaril.Wasm.SpecTec.Sim10.Whole
