module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElsePairs

/-!
# The `otherwise` premises of `simEnv20T` hold in `utf8Env20T`

The kernel checks every pair of an `otherwise` rule and an earlier rule of `Step_read` (atoms read
by `VElse.ruleAtom`) and of `Step_pure` (atoms read by `ElseAgree.pureAtom`) with `pairOkU`
(`readPairsU`, `purePairsU`), and checks that no other relation of `fixedT20` has an `otherwise`
rule (`otherElseFree20T`). With `otherwiseAtB_moveU` and the soundness of `pairOkU`:

* **`elseMonoR20T`**: `ElseMonoR (simEnv20T B) (utf8Env20T B)` for every `B` that leaves `$utf8`
  uninterpreted: each `otherwise` premise of `simEnv20T B`, at a point where the rest of its rule
  holds, holds in `utf8Env20T B`.
* **`sstepB_utf8_20T`**: every step of `simEnv20T B` is a step of `utf8Env20T B`.
* **`fwd_good20B_utf8T'`**, `runU_good20B'`: round 6's `Utf8Mono.fwd_good20B_utf8T` and
  `runU_good20B` without the `ElseMono` hypothesis. Every V2 step from a `Good20B` configuration
  is a step of `utf8Env20T (storeB P)` between the images, and its successor is `Good20B` and
  `Good20BU`.

`Utf8Mono.ElseMono` itself (every `otherwise` instance, at any point) is not proved; the
restricted form is what steps use.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (otherwiseB SStepB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7 (VElse.ruleAtom)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (otherElseFreeB ruleElseB pureAtom atomSound_ruleAtom
  atomSound_pureAtom)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixedT20)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (Good20B fwd_good20B good20B_steps)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T envExt20T Good20BU good20BU_of_good20B
  storeB_utf8)

/-! ## Kernel checks -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_read`'s pairs pass `pairOkU`** (kernel). -/
theorem readPairsU (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      pairsOkU VElse.ruleAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_pure`'s pairs pass `pairOkU`** (kernel). -/
theorem purePairsU (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      pairsOkU pureAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Only `Step_read` and `Step_pure` have `otherwise` rules in `fixedT20`** (kernel). -/
theorem otherElseFree20T : otherElseFreeB (relsOfDefs fixedT20) = true := by
  decide +kernel

/-! ## The `otherwise` premises that occur -/

/-- **No relation of `simEnv20T B` other than `Step_read` and `Step_pure` has an `otherwise`
rule.** -/
theorem noElse_other20T {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {r : Rule} (hx : x ≠ "Step_read") (hx' : x ≠ "Step_pure")
    (hrel : (simEnv20T B).findRel? x = some (ps, op, t, rules)) (hri : rules[i]? = some r)
    (hel : RuleHasElseB r) : False := by
  have hm : (x, (ps, op, t, rules)) ∈ relsOfDefs fixedT20 := by
    have h' : (relsOfDefs fixedT20).find? x = some (ps, op, t, rules) := by
      simpa [simEnv20T, Env.withBuiltins, Env.findRel?, envOfScript, envOfDefs_eq, Env.empty,
        Map.empty] using hrel
    exact mem_of_find? h'
  have h : (rules.all fun r => !ruleElseB r) = true := by
    simpa only [beq_iff_eq, hx, hx', false_or, Bool.or_eq_true] using
      List.all_eq_true.1 otherElseFree20T _ hm
  have hr : (!ruleElseB r) = true := List.all_eq_true.1 h _ (List.mem_of_getElem? hri)
  rw [ruleElseB_of' hel] at hr
  exact absurd hr (by decide)

/-- `otherwise` moves on a relation whose pairs pass `pairOkU`. -/
theorem elseU_of_pairs {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {x : IL.Id}
    {args : List ArgV} {i : Nat} {v : Value} {atom : Rule → Option MixopS}
    (hA : ElseAgree.AtomSound atom) {t : Typ} {rules : List Rule}
    (hrel : (simEnv20T B).findRel? x = some ([], "%~>%", t, rules))
    (hok : pairsOkU atom rules = true) (hC : RuleCtxB (simEnv20T B) x args i v)
    (hO : otherwiseB (simEnv20T B) x args i v) : otherwiseB (utf8Env20T B) x args i v :=
  otherwiseAtB_moveU (envExt20T B hB) hrel (pairBackU_of_pairsOkU hB hA hok) i v hC hO

/-- **The `otherwise` premises of `simEnv20T B` that occur hold in `utf8Env20T B`.** -/
theorem elseMonoR20T {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) :
    ElseMonoR (simEnv20T B) (utf8Env20T B) := by
  intro x args i v hC hO
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hri, hel, -, -, -, -⟩ := id hC
  by_cases hx : x = "Step_read"
  · subst hx
    obtain ⟨t', rules', hrel', hok⟩ := readPairsU B
    exact elseU_of_pairs hB atomSound_ruleAtom hrel' hok hC hO
  by_cases hx' : x = "Step_pure"
  · subst hx'
    obtain ⟨t', rules', hrel', hok⟩ := purePairsU B
    exact elseU_of_pairs hB atomSound_pureAtom hrel' hok hC hO
  exact (noElse_other20T (r := .ruleD nm qs op e prems) hx hx' hrel hri hel).elim

/-- **Every step of `simEnv20T B` is a step of `utf8Env20T B`**, for `B` that leaves `$utf8`
uninterpreted. -/
theorem sstepB_utf8_20T {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {c c' : Value}
    (h : SStepB (simEnv20T B) c c') : SStepB (utf8Env20T B) c c' :=
  sstepB_extR (envExt20T B hB) (elseMonoR20T hB) h

/-! ## The forward theorem in `utf8Env20T`, unconditionally -/

variable {H : Type} {hn : H → String}

/-- **The forward theorem in `utf8Env20T`, from `Good20B`.** Every V2 step from a `Good20B`
configuration is a step of `utf8Env20T (storeB P)` between the images; its successor is
`Good20B`, hence `Good20BU`. Round 6's `Utf8Mono.fwd_good20B_utf8T` without `ElseMono`. -/
theorem fwd_good20B_utf8T' {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20B hn P c) (h : Step P host c c') :
    Good20B hn P c' ∧ Good20BU hn P c' ∧
      SStepB (utf8Env20T (Whole.storeB P)) (configV hn c) (configV hn c') := by
  obtain ⟨hg', hs⟩ := fwd_good20B hg h
  exact ⟨hg', good20BU_of_good20B hg', sstepB_utf8_20T (storeB_utf8 P) hs⟩

/-- **Runs from `Good20B` are runs of `utf8Env20T (storeB P)`**, unconditionally. -/
theorem runU_good20B' {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20B hn P c) :
    Relation.ReflTransGen (SStepB (utf8Env20T (Whole.storeB P))) (configV hn c)
      (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20B_utf8T' (good20B_steps h₁ hg) h₂).2.2

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
