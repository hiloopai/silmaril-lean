module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Pairs
public import Silmaril.Wasm.SpecTec.Sim10.Round5Fwd.Thms

/-!
# Every step of `simEnv10T` is a step of the 1.0 `$utf8` erratum

The 1.0 form 's `Sim20.Utf8Else.sstepB_utf8_20T`. The kernel checks every pair of an
`otherwise` rule and an earlier rule of 1.0's `Step_read` and `Step_pure` with `pairOkN`
(`readPairsN10`, `purePairsN10`), and checks that no other relation of `fixedT10` has an
`otherwise` rule (`otherElseFree10T`). Then:

* **`elseMonoR10T`**: `Utf8Else.ElseMonoR (simEnv10T B) (utf8Env10T B)` for every `B` that leaves
  `$utf8` uninterpreted;
* **`sstepB_utf8_10T`**: every step of `simEnv10T B` is a step of `utf8Env10T B`;
  `typed10_utf8_10T`: typing moves too;
* `bytesB10_utf8`: the 1.0 forward primitives leave `$utf8` uninterpreted;
* **`wholeRunFwd10T_utf8`**: round 4's forward run theorem `Whole.wholeRunFwd10T` holds in the
  fixed script `fixedU10`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Config HostSemantics Steps)
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (otherwiseB SStepB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7 (VElse.ruleAtom)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (otherElseFreeB ruleElseB pureAtom atomSound_ruleAtom
  atomSound_pureAtom AtomSound)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (RuleHasElseB ruleElseB_of' RuleCtxB ElseMonoR
  otherwiseAtB_moveU sstepB_extR)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixedT10)

/-! ## Kernel checks -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **1.0's `Step_read` pairs pass `pairOkN`** (kernel). -/
theorem readPairsN10 (B : Builtins) : ∃ t rules,
    (simEnv10T B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      pairsOkN VElse.ruleAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **1.0's `Step_pure` pairs pass `pairOkN`** (kernel). -/
theorem purePairsN10 (B : Builtins) : ∃ t rules,
    (simEnv10T B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      pairsOkN pureAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Only `Step_read` and `Step_pure` have `otherwise` rules in `fixedT10`** (kernel). -/
theorem otherElseFree10T : otherElseFreeB (relsOfDefs fixedT10) = true := by
  decide +kernel

/-! ## The `otherwise` premises that occur -/

/-- **No relation of `simEnv10T B` other than `Step_read` and `Step_pure` has an `otherwise`
rule.** -/
theorem noElse_other10T {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {r : Rule} (hx : x ≠ "Step_read") (hx' : x ≠ "Step_pure")
    (hrel : (simEnv10T B).findRel? x = some (ps, op, t, rules)) (hri : rules[i]? = some r)
    (hel : RuleHasElseB r) : False := by
  have hm : (x, (ps, op, t, rules)) ∈ relsOfDefs fixedT10 := by
    have h' : (relsOfDefs fixedT10).find? x = some (ps, op, t, rules) := by
      simpa [simEnv10T, Env.withBuiltins, Env.findRel?, envOfScript, envOfDefs_eq, Env.empty,
        Map.empty] using hrel
    exact mem_of_find? h'
  have h : (rules.all fun r => !ruleElseB r) = true := by
    simpa only [beq_iff_eq, hx, hx', false_or, Bool.or_eq_true] using
      List.all_eq_true.1 otherElseFree10T _ hm
  have hr : (!ruleElseB r) = true := List.all_eq_true.1 h _ (List.mem_of_getElem? hri)
  rw [ruleElseB_of' hel] at hr
  exact absurd hr (by decide)

/-- `otherwise` moves on a relation whose pairs pass `pairOkN`. -/
theorem elseU_of_pairs10 {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {x : IL.Id}
    {args : List ArgV} {i : Nat} {v : Value} {atom : Rule → Option MixopS}
    (hA : AtomSound atom) {t : Typ} {rules : List Rule}
    (hrel : (simEnv10T B).findRel? x = some ([], "%~>%", t, rules))
    (hok : pairsOkN atom rules = true) (hC : RuleCtxB (simEnv10T B) x args i v)
    (hO : otherwiseB (simEnv10T B) x args i v) : otherwiseB (utf8Env10T B) x args i v :=
  otherwiseAtB_moveU (envExt10T B hB) hrel (pairBackU_of_pairsOkN hB hA hok) i v hC hO

/-- **The `otherwise` premises of `simEnv10T B` that occur hold in `utf8Env10T B`.** -/
theorem elseMonoR10T {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) :
    ElseMonoR (simEnv10T B) (utf8Env10T B) := by
  intro x args i v hC hO
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hri, hel, -, -, -, -⟩ := id hC
  by_cases hx : x = "Step_read"
  · subst hx
    obtain ⟨t', rules', hrel', hok⟩ := readPairsN10 B
    exact elseU_of_pairs10 hB atomSound_ruleAtom hrel' hok hC hO
  by_cases hx' : x = "Step_pure"
  · subst hx'
    obtain ⟨t', rules', hrel', hok⟩ := purePairsN10 B
    exact elseU_of_pairs10 hB atomSound_pureAtom hrel' hok hC hO
  exact (noElse_other10T (r := .ruleD nm qs op e prems) hx hx' hrel hri hel).elim

/-- **Every step of `simEnv10T B` is a step of `utf8Env10T B`**, for `B` that leaves `$utf8`
uninterpreted. -/
theorem sstepB_utf8_10T {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {c c' : Value}
    (h : SStepB (simEnv10T B) c c') : SStepB (utf8Env10T B) c c' :=
  sstepB_extR (envExt10T B hB) (elseMonoR10T hB) h

/-- Runs move too. -/
theorem runB_utf8_10T {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {c c' : Value}
    (h : Relation.ReflTransGen (SStepB (simEnv10T B)) c c') :
    Relation.ReflTransGen (SStepB (utf8Env10T B)) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ h₂ ih => exact .tail ih (sstepB_utf8_10T hB h₂)

variable {H : Type}

/-- **Typing moves** from `simEnv10T B` to `utf8Env10T B`. -/
theorem typed10_utf8_10T {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {hn : H → String}
    {c : Config H} (h : Typed10 (simEnv10T B) hn c) : Typed10 (utf8Env10T B) hn c :=
  Sim20.Utf8Mono.hasTyp_ext (envExt10T B hB) h

/-! ## The 1.0 forward run in the fixed script -/

/-- **The 1.0 forward primitives leave `$utf8` uninterpreted.** -/
theorem bytesB10_utf8 (P : Silmaril.Wasm.Numerics.Profile) (ws : List ArgV) :
    (Whole.bytesB10 P).call "utf8" ws = none := by
  simp only [Whole.bytesB10]
  simp only [ite_false, String.reduceEq]
  exact Sim20.Utf8Mono.floatIntB_utf8 P ws

/-- **Round 4's forward run theorem holds in the fixed script `fixedU10`.** -/
theorem wholeRunFwd10T_utf8 {hn : H → String} {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {c c' : Config H} (hc : Typed10 (simEnv10T (Whole.fwdB10 nd r)) hn c)
    (hpl : Whole.Plain10 c.code) (hal : Whole.MemsAligned10 c.store)
    (hg : ∀ d, Steps host c d → GSetOk d.store d.frame d.code) (h : Steps host c c') :
    Typed10 (utf8Env10T (Whole.fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (utf8Env10T (Whole.fwdB10 nd r))) (configV hn c)
        (configV hn c') := by
  obtain ⟨ht, hrun⟩ := Whole.wholeRunFwd10T hc hpl hal hg h
  exact ⟨typed10_utf8_10T (bytesB10_utf8 _) ht, runB_utf8_10T (bytesB10_utf8 _) hrun⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
