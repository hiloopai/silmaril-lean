module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCtxS
public import Silmaril.Wasm.SpecTec.Sim20.RelFree.Thms

/-!
# The transfer hypotheses of the erratum route, proved

Pass 4's `fwd_ctxTop20S` assumed `StepAgreeS B` (an original firing of `Step` rule `k ≥ 4` is a
corrected firing of rule `k + 1`) and `TypAgreeS B` (`state`, `admininstr*`, `val*` type alike in
`simEnv20 B` and `simEnv20S B`). Both hold at every builtins:

* `simEnv20S B` is `simEnv20 B` with another relation table (`RelFree.simEnv20S_eq`);
* the original rules 4–21 are rules 5–22 of the corrected `Step` and pass `RelFree.ruleOkB`: they
  refer to no relation, not to `$instantiate`, and have no `otherwise` premise
  (`RelFree.stepRules20_spec`, kernel);
* every definition other than `$instantiate`, and every type, of the 2.0 script is relation-free
  (`RelFree.defsGood_simEnv20`, `RelFree.typsGood_simEnv20`, kernel), so the rule bodies and the
  three types evaluate and type alike under any relation table (`RelFree.ruleBody_withRels`,
  `RelFree.hasTyp_withRels_iff`).

So `stepAgreeS`, `typAgreeS` and **`wholeStepCtxS20 : Task.wholeStepCtxS20`** hold outright. The
frozen target still assumes that the successor configuration is typed; dropping that is subject
reduction for the image, which this module does not prove.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV stateT ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy valsTy pureFix readFix ctxtInstrsFix
  ctxtLabelFix ctxtFrameFix)
open Silmaril.Wasm.SpecTec.Sim20.RelFree (bad20 withRels simEnv20S_eq stepRules20_spec
  defsGood_simEnv20 typsGood_simEnv20 ruleBody_withRels hasTyp_withRels_iff goodEvs_of_all)

/-- The `k`-th original rule, `k ≥ 4`, is the `k + 1`-st corrected rule. -/
theorem getElem?_fix_succ {α : Type} (pre : List α) (hpre : pre.length = 5) (rules : List α)
    {k : Nat} (hk : 4 ≤ k) : (pre ++ rules.drop 4)[k + 1]? = rules[k]? := by
  rw [List.getElem?_append_right (by omega), List.getElem?_drop, hpre]
  congr 1
  omega

/-- **`StepAgreeS` holds at every builtins.** -/
theorem stepAgreeS (B : Builtins) : StepAgreeS B := by
  obtain ⟨t, rules, h₁, h₂, hok⟩ := stepRules20_spec B
  intro k hk v ⟨t', rules', r, hrel, hr, hbody⟩
  rw [h₁] at hrel
  obtain ⟨rfl, rfl⟩ : t = t' ∧ rules = rules' := by simpa using hrel
  have hr' := (getElem?_fix_succ [pureFix, readFix, ctxtInstrsFix, ctxtLabelFix, ctxtFrameFix] rfl
    rules hk).trans hr
  have hmem : r ∈ rules.drop 4 := by
    have hd : (rules.drop 4)[k - 4]? = some r := by
      rw [List.getElem?_drop, show 4 + (k - 4) = k by omega]
      exact hr
    exact List.mem_of_getElem? hd
  have hb := ruleBody_withRels (R := (simEnv20S B).rels) (D' := Sim.DDerives (simEnv20S B)
    (Sim.otherwise (simEnv20S B))) (els' := Sim.otherwise (simEnv20S B) "Step" [] (k + 1) v)
    (defsGood_simEnv20 B) (typsGood_simEnv20 B) (List.all_eq_true.1 hok r hmem) hbody
  rw [← simEnv20S_eq B] at hb
  exact ⟨t, _, r, h₂, hr', hb⟩

/-- A type whose only event is a type reference is relation-free. -/
theorem typedV_withRels20 {B : Builtins} {t : Typ}
    (ht : (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evTyp t).all (RelFree.rfEvB bad20) = true)
    {v : Value} (h : TypedV (simEnv20 B) t v) : TypedV (simEnv20S B) t v := by
  intro ρ hρ
  rw [simEnv20S_eq B]
  refine (hasTyp_withRels_iff (defsGood_simEnv20 B) (typsGood_simEnv20 B) ?_ ?_
    (goodEvs_of_all ht)).2 (h ρ hρ)
  · intro p hp; rw [hρ.2.1] at hp; simp at hp
  · intro p hp; rw [hρ.1] at hp; simp at hp

/-- **`TypAgreeS` holds at every builtins.** -/
theorem typAgreeS (B : Builtins) : TypAgreeS B where
  state _ h := typedV_withRels20 (by decide) h
  admins _ h := typedV_withRels20 (by decide) h
  vals _ h := typedV_withRels20 (by decide) h

/-- **`Task.wholeStepCtxS20` is proved**: at `growB`, every top-level fragment step under a
value prefix and a suffix, with typed inner configurations and suffix and whole pages, is a step
of the corrected script between the images. -/
theorem wholeStepCtxS20 : Task.wholeStepCtxS20 :=
  wholeStepCtxS20_of_agree fun _ => ⟨stepAgreeS _, typAgreeS _⟩

/-- `fwd_ctxTop20S` with the transfer hypotheses discharged, at any `GrowCalls20` builtins. -/
theorem fwd_ctxTop20S' {H : Type} {hn : H → String} {B : Builtins} {P : Profile}
    (hG : GrowCalls20 B) {s s' : Store H} {f f' : Frame} {code code' : List Admin} (vs : List Val)
    (rest : List Admin)
    (hc : Typed20 (simEnv20 B) hn ⟨s, f, code⟩) (hc' : Typed20 (simEnv20 B) hn ⟨s', f', code'⟩)
    (hrest : TypedV (simEnv20 B) adminsTy (.list (adminsToV rest))) (hw : WholePages s)
    (h : TopVStep20 P ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    Sim.Round6.Reading.SStepB (simEnv20S B) (configV hn ⟨s, f, vals vs ++ code ++ rest⟩)
      (configV hn ⟨s', f', vals vs ++ code' ++ rest⟩) :=
  fwd_ctxTop20S hG (stepAgreeS B) (typAgreeS B) vs rest hc hc' hrest hw h

end Silmaril.Wasm.SpecTec.Sim20.Whole
