module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreePairs

/-!
# `Task.elseAgree20T`: the seventeen `otherwise` premises agree

The kernel checks every pair of an `otherwise` rule and an earlier rule of `Step_read` (atoms read
by `VElse.ruleAtom`) and of `Step_pure` (atoms read by `pureAtom`) with `pairOkB`
(`readPairs20S`, `purePairs20S`), and checks that no other relation of the corrected wasm-2.0
script has an `otherwise` rule (`otherElseFree20S`). With `otherwiseAt_move` and the soundness of
`pairOkB`, this proves the open target :

* **`elseAgree20T : StoreAgree.Task.elseAgree20T`**.

So every step of `simEnv20S B` is a step of `simEnv20T B` with no hypothesis
(`sstepB20T_of_sstepB20S'`), `Fwd20` gives `Fwd20T` (`fwd20T_of_fwd20'`), and `Fwd20T` holds on
`GoodT20 = Good20C ∨ GoodStore20T` (`fwd20T_goodT20'`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (otherwise)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7 (VElse.ruleAtom)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (envSame20T typRepair20T ElseAgree20T RuleCtx)

/-! ## Kernel checks -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_read`'s pairs pass `pairOkB`** (kernel). -/
theorem readPairs20S (B : Builtins) : ∃ t rules,
    (simEnv20S B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      pairsOkB VElse.ruleAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_pure`'s pairs pass `pairOkB`** (kernel). -/
theorem purePairs20S (B : Builtins) : ∃ t rules,
    (simEnv20S B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      pairsOkB pureAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

/-- No relation other than `Step_read` and `Step_pure` has an `otherwise` rule, as a check. -/
def otherElseFreeB (m : Map RelDef) : Bool :=
  m.all fun p => p.1 == "Step_read" || p.1 == "Step_pure" || p.2.2.2.2.all fun r => !ruleElseB r

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Only `Step_read` and `Step_pure` have `otherwise` rules** (kernel). -/
theorem otherElseFree20S : otherElseFreeB (relsOfDefs StepFix.fixedS20) = true := by
  decide +kernel

/-! ## The target -/

/-- **No relation other than `Step_read` and `Step_pure` has an `otherwise` rule.** -/
theorem noElse_other {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {r : Rule} (hx : x ≠ "Step_read") (hx' : x ≠ "Step_pure")
    (hrel : (simEnv20S B).findRel? x = some (ps, op, t, rules)) (hri : rules[i]? = some r)
    (hel : RuleHasElse r) : False := by
  have hm : (x, (ps, op, t, rules)) ∈ relsOfDefs StepFix.fixedS20 := by
    have h' : (relsOfDefs StepFix.fixedS20).find? x = some (ps, op, t, rules) := by
      simpa [simEnv20S, Env.withBuiltins, Env.findRel?, envOfScript, envOfDefs_eq, Env.empty,
        Map.empty] using hrel
    exact mem_of_find? h'
  have h : (rules.all fun r => !ruleElseB r) = true := by
    simpa only [beq_iff_eq, hx, hx', false_or, Bool.or_eq_true] using
      List.all_eq_true.1 otherElseFree20S _ hm
  have hr : (!ruleElseB r) = true := List.all_eq_true.1 h _ (List.mem_of_getElem? hri)
  rw [ruleElseB_of hel] at hr
  exact absurd hr (by decide)

/-- `otherwise` moves on a relation whose pairs pass `pairOkB`. -/
theorem else_of_pairs {B : Builtins} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value}
    {atom : Rule → Option MixopS} (hA : AtomSound atom) {t : Typ} {rules : List Rule}
    (hrel : (simEnv20S B).findRel? x = some ([], "%~>%", t, rules))
    (hok : pairsOkB atom rules = true) (hC : RuleCtx (simEnv20S B) x args i v)
    (hO : otherwise (simEnv20S B) x args i v) : otherwise (simEnv20T B) x args i v :=
  otherwiseAt_move (envSame20T B) (typRepair20T B) hrel (pairBack_of_pairsOkB hA hok) i v hC hO

/-- **`Task.elseAgree20T`**: the `otherwise` premises of `simEnv20S B` hold in `simEnv20T B`
wherever the rest of their rule holds in `simEnv20S B`. -/
theorem elseAgree20T : StoreAgree.Task.elseAgree20T := by
  intro B x args i v hO hC
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, hrel, hri, hel, -, -, -⟩ := id hC
  by_cases hx : x = "Step_read"
  · subst hx
    obtain ⟨t', rules', hrel', hok⟩ := readPairs20S B
    exact else_of_pairs atomSound_ruleAtom hrel' hok hC hO
  by_cases hx' : x = "Step_pure"
  · subst hx'
    obtain ⟨t', rules', hrel', hok⟩ := purePairs20S B
    exact else_of_pairs atomSound_pureAtom hrel' hok hC hO
  exact (noElse_other (r := .ruleD nm qs op e prems) hx hx' hrel hri hel).elim

/-! ## Consequences -/

/-- **Every step of `simEnv20S B` is a step of `simEnv20T B`**, with no hypothesis. -/
theorem sstepB20T_of_sstepB20S' {B : Builtins} {c c' : Value}
    (h : SStepB (simEnv20S B) c c') : SStepB (simEnv20T B) c c' :=
  StoreAgree.sstepB20T_of_sstepB20S (elseAgree20T B) h

/-- **`Fwd20` gives `Fwd20T`**, with no hypothesis. -/
theorem fwd20T_of_fwd20' {H : Type} {hn : H → String} {tgt : HostSemantics H} {B : Builtins}
    {Good : Config H → Prop} (h : Sim10.Fwd20 hn tgt B Good) : StoreAgree.Fwd20T hn tgt B Good :=
  StoreAgree.fwd20T_of_fwd20 (elseAgree20T B) h

/-- **`Fwd20T` holds on `GoodT20`**, with no hypothesis. -/
theorem fwd20T_goodT20' {H : Type} (hn : H → String) (host : HostSemantics H) :
    StoreAgree.Fwd20T hn host (Whole.storeB Silmaril.Wasm.Lime1.Execution.v2Profile)
      (StoreAgree.GoodT20 hn Silmaril.Wasm.Lime1.Execution.v2Profile host) :=
  StoreAgree.fwd20T_goodT20 hn host (elseAgree20T _)

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
