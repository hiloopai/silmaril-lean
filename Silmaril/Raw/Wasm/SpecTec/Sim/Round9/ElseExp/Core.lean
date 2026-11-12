module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseExp.Check

/-!
# Round 9, RE: rules with export-free relation premises, backward and forward (unrefined)

* `erase_rulePr`: the asserted expression of a top-level relation premise of a rule instance
  commutes with erasure (as `NxErase.erase_ifPr` for `if` premises).
* `rulePr_self`: when that expression is export-free (`NxSites.nxE`), its value on the original
  side equals its value on the erased side.
* `reflect_coreR`: `ElseBwd.reflect_core` for a rule `j` passing `simpleRuleR`: the backward
  firing, given its `otherwise` premise backward.
* `fireFwdR`: a rule passing `simpleRuleR` fires on the erased side when it fires on the original
  one, given `PairReflectB` at its own pairs if it has an `otherwise` premise
  (`ElseBwd.fireFwd_simple` and `ElseBwd.fireFwd_elseRule` together).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound (DefsVT)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

/-! ## Relation premises of a rule instance -/

section Inst

variable {gr gd : String → Bool} (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m)
  (H : BIErase QT gd (utf8Env B)) {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
  {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
  {prems : List Prem} (hx : reach 0 x = true)
  (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
  (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
  (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
include hD H hx hrel hrule hq

/-- **The asserted expression of a top-level relation premise commutes with erasure.** -/
theorem erase_rulePr
    (hCE : ∀ k, NxErase.CallE gd sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k)
    {y : IL.Id} {args : List Arg} {o : MixopS} {c : Exp}
    (hpr : Prem.rulePr y args o c ∈ prems) (hxc : xExp gr gd c = true) (n : Nat) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) c =
      eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) c := by
  have hF := NxRule.rFacts hx hrel hrule
  obtain ⟨ht, ha, hc⟩ := hF.premsOk _ hpr
  have hb := NxRule.badPr_zero hx hrel hrule hpr rfl
  have hX := NxErase.ruleX_at hx hrel (List.mem_of_getElem? hrule)
  simp only [NxErase.ruleX, Bool.and_eq_true, List.all_eq_true] at hX
  have hXc := hX.2 _ hpr
  simp only [NxErase.premX, Bool.and_eq_true] at hXc
  simp only [premTy, ckRulePr, Bool.and_eq_true] at ht
  simp only [NxRule.premAuxR, Bool.and_eq_true] at ha
  simp only [badPr] at hb
  simp only [freePrem] at hc
  exact NxErase.erase_closed hD H hq hF.wild hCE (NxRule.varsIn_union_right hc) ht.1.2 ha.2
    hXc.2 (by omega) hxc n

/-- **An export-free asserted expression has the same value on both sides.** -/
theorem rulePr_self
    (hCE : ∀ k, NxErase.CallE gd sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k)
    {y : IL.Id} {args : List Arg} {o : MixopS} {c : Exp}
    (hpr : Prem.rulePr y args o c ∈ prems) (hxc : xExp gr gd c = true)
    (hnx : nxE sigX (quantsΓ qs) c = true) {n : Nat} {w : Value}
    (hw : evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) c = .ok w) :
    evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) c = .ok w := by
  rw [erase_rulePr hD H hx hrel hrule hq hCE hpr hxc n] at hw
  obtain ⟨u, hu, rfl⟩ := map_eq_ok hw
  have hok := (NxRule.eOk_rulePr hD hx hrel hrule hq hpr ⟨n, hu⟩).1
  rw [hu, Swap.eraseV_of_nxB _ (NxRule.nxB_of_eOk hok hnx)]

/-- **The forward form of `rulePr_self`.** -/
theorem rulePr_self_fwd
    (hCE : ∀ k, NxErase.CallE gd sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k)
    {y : IL.Id} {args : List Arg} {o : MixopS} {c : Exp}
    (hpr : Prem.rulePr y args o c ∈ prems) (hxc : xExp gr gd c = true)
    (hnx : nxE sigX (quantsΓ qs) c = true) {n : Nat} {w : Value}
    (hw : evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) c = .ok w) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) c = .ok w := by
  rw [erase_rulePr hD H hx hrel hrule hq hCE hpr hxc n, hw]
  have hok := (NxRule.eOk_rulePr hD hx hrel hrule hq hpr ⟨n, hw⟩).1
  simp [Swap.eraseV_of_nxB _ (NxRule.nxB_of_eOk hok hnx)]

end Inst

/-- Arguments `[]` evaluate in any scope. -/
theorem evalArgs_nil {env : Env} {ρ ρ' : VarEnv} {ws : List ArgV} (h : EvalArgs env ρ [] ws) :
    EvalArgs env ρ' [] ws := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rcases n with _ | n
  · simp [evalArgs] at hn
  · simpa [evalArgs] using hn

/-- The parts of `premR` at a relation premise. -/
theorem premR_rulePr {qs : List Param} {y : IL.Id} {args : List Arg} {o : MixopS} {c : Exp}
    (h : premR qs (.rulePr y args o c) = true) :
    args = [] ∧ xExp grE gdE c = true ∧ nxE sigX (quantsΓ qs) c = true := by
  cases args with
  | nil =>
    simp only [premR, Bool.and_eq_true] at h
    exact ⟨rfl, h.1, h.2⟩
  | cons _ _ => simp [premR] at h

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
