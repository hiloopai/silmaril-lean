module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerPairs

/-!
# The `otherwise` premises of `simEnv20T` and `simEnv20V` agree, and the transfer

The kernel checks every pair of an `otherwise` rule and an earlier rule of `Step_read` (atoms read
by `VElse.ruleAtom`) and of `Step_pure` (atoms read by `ElseAgree.pureAtom`) with `pairOkV`
(`readPairsV`, `purePairsV`). Round 7's `Utf8Else.otherElseFree20T` already shows that no other
relation of `fixedT20` has an `otherwise` rule. These are the 2 `Step_pure` and 15 `Step_read`
rules listed : the kernel check covers all of them, whatever the list.

* **`else_iffV`**: at an `otherwise` rule whose quantifiers are typed in both environments,
  `otherwiseB (simEnv20T B)` and `otherwiseB (simEnv20V B)` agree, for every `B`.
* **`elseMoveV`**: `ElseMoveS sideV (simEnv20T B) (simEnv20V B)`.
* **`dderivesBS_toV'`**, **`sstepBS_toV'`**: every derivation, and every `Step`, of
  `simEnv20T B` whose rule instances bind their quantifiers harmlessly (`QuantsV`) is one of
  `simEnv20V B`, with no hypothesis left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB otherwiseB SStepB)
open Silmaril.Wasm.SpecTec.Sim.Round7 (VElse.ruleAtom)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (pureAtom atomSound_ruleAtom atomSound_pureAtom)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (noElse_other20T)

/-! ## Kernel checks -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_read`'s pairs pass `pairOkV`** (kernel). -/
theorem readPairsV (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      pairsOkV VElse.ruleAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_pure`'s pairs pass `pairOkV`** (kernel). -/
theorem purePairsV (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      pairsOkV pureAtom rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

/-! ## `otherwise` -/

/-- `otherwise` agrees on a relation whose pairs pass `pairOkV`. -/
theorem elseV_of_pairs {B : Builtins} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value}
    {atom : Rule → Option MixopS} (hA : ElseAgree.AtomSound atom) {t : Typ} {rules : List Rule}
    (hrel : (simEnv20T B).findRel? x = some ([], "%~>%", t, rules))
    (hok : pairsOkV atom rules = true) (hC : Ctx2 (simEnv20T B) (simEnv20V B) x args i v) :
    otherwiseB (simEnv20T B) x args i v ↔ otherwiseB (simEnv20V B) x args i v :=
  otherwiseAtB_sym (envSameTV B) hrel (pairSym_of_pairsOkV hA hok) i v hC

/-- **`otherwise` agrees in `simEnv20T B` and `simEnv20V B`** at an `otherwise` rule typed in
both. -/
theorem else_iffV {B : Builtins} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value}
    (hC : Ctx2 (simEnv20T B) (simEnv20V B) x args i v) :
    otherwiseB (simEnv20T B) x args i v ↔ otherwiseB (simEnv20V B) x args i v := by
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hri, hel, -, -, -, -, -⟩ := id hC
  by_cases hx : x = "Step_read"
  · subst hx
    obtain ⟨t', rules', hrel', hok⟩ := readPairsV B
    exact elseV_of_pairs atomSound_ruleAtom hrel' hok hC
  by_cases hx' : x = "Step_pure"
  · subst hx'
    obtain ⟨t', rules', hrel', hok⟩ := purePairsV B
    exact elseV_of_pairs atomSound_pureAtom hrel' hok hC
  exact (noElse_other20T (r := .ruleD nm qs op e prems) hx hx' hrel hri hel).elim

/-- **The `otherwise` premises of `simEnv20T B` that occur under `QuantsV` hold in
`simEnv20V B`.** -/
theorem elseMoveV (B : Builtins) : ElseMoveS sideV (simEnv20T B) (simEnv20V B) := by
  intro x args i v hC hO
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hri, hel, he', hps, hq, hs, hev⟩ :=
    hC
  exact (else_iffV ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, e', hrel, hri, hel, he', hps, hq,
    quantsOk_toV hq hs, hev⟩).1 hO

/-! ## The transfer -/

/-- **Every derivation of `simEnv20T B` with harmless quantifiers is one of `simEnv20V B`.** -/
theorem dderivesBS_toV' {B : Builtins} {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (h : DDerivesBS sideV (simEnv20T B) (otherwiseB (simEnv20T B)) x op args v) :
    DDerivesB (simEnv20V B) (otherwiseB (simEnv20V B)) x op args v :=
  dderivesBS_toV (elseMoveV B) h

/-- **Every step of `simEnv20T B` with harmless quantifiers is a step of `simEnv20V B`.** -/
theorem sstepBS_toV' {B : Builtins} {c c' : Value} (h : SStepBV B c c') :
    SStepB (simEnv20V B) c c' :=
  sstepBS_toV (elseMoveV B) h

end Silmaril.Wasm.SpecTec.Sim20.VecDer
