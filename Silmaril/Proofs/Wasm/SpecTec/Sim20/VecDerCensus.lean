module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerPat

/-!
# Which rules of the three reduction relations bind harmlessly

`patOkB r`: every quantifier of the rule `r` passes `quantPatB` at every alternative of its
conclusion. The kernel runs it on every rule of `Step`, `Step_pure` and `Step_read` of
`simEnv20T B` (`census_step`, `census_pure`, `census_read`). Exactly six rules fail
(`patOk_fails`):

* `Step_pure` 34–37 and 40, the rules of the three operator families (`vunop`, `vunop-trap`,
  `vbinop-val`, `vbinop-trap`, `vrelop`): their operator quantifier has the family type
  `vunop_(sh)` (and so on), which `VecAgree.TOk` does not cover at a scope variable `sh`;
* `Step_read` 5, `call_addr`: its quantifier `func : func` (a type in `vbad20`) is bound by the
  premises only.

* **`quantsV_of_rule`**: at every other rule of the three relations, a rule instance whose
  conclusion value is `VOk` satisfies `QuantsV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (conclAlts)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (VOk)

/-- **Every quantifier of the rule is read harmlessly off every conclusion alternative.** -/
def patOkB : Rule → Bool
  | .ruleD _ qs _ e _ => (conclAlts e).all fun e' => qs.all (quantPatB e')

/-- The rules of the three relations that fail `patOkB`. -/
def patExcl : List (String × Nat) :=
  [("Step_pure", 34), ("Step_pure", 35), ("Step_pure", 36), ("Step_pure", 37),
    ("Step_pure", 40), ("Step_read", 5)]

/-- Every rule of `x` outside `patExcl` passes `patOkB`. -/
def censusB (x : String) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i => patExcl.contains (x, i) || match rules[i]? with
    | some r => patOkB r
    | none => true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step` passes** (kernel). -/
theorem census_step (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step" = some ([], "%~>%", t, rules) ∧ censusB "Step" rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_pure` passes outside `patExcl`** (kernel). -/
theorem census_pure (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
      censusB "Step_pure" rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Step_read` passes outside `patExcl`** (kernel). -/
theorem census_read (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
      censusB "Step_read" rules = true :=
  ⟨_, _, rfl, by decide +kernel⟩

/-- The rules of `x` that fail `patOkB`. -/
def failsB (rules : List Rule) (is : List Nat) : Bool :=
  is.all fun i => match rules[i]? with
    | some r => !patOkB r
    | none => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The six excluded rules do fail `patOkB`** (kernel), so `patExcl` is exact. -/
theorem patOk_fails (B : Builtins) : ∃ tp rp tr rr,
    (simEnv20T B).findRel? "Step_pure" = some ([], "%~>%", tp, rp) ∧
      (simEnv20T B).findRel? "Step_read" = some ([], "%~>%", tr, rr) ∧
      failsB rp [34, 35, 36, 37, 40] = true ∧ failsB rr [5] = true :=
  ⟨_, _, _, _, rfl, rfl, by decide +kernel, by decide +kernel⟩

/-- `censusB` at one rule. -/
theorem patOkB_of_census {x : String} {rules : List Rule} (h : censusB x rules = true) {i : Nat}
    {r : Rule} (hr : rules[i]? = some r) (hx : patExcl.contains (x, i) = false) :
    patOkB r = true := by
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.1 hr).1
  have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hlt)
  simp only [hx, hr, Bool.false_or] at h₁
  exact h₁

/-- **At a rule of `Step`, `Step_pure` or `Step_read` outside `patExcl`, an instance whose
conclusion value is `VOk` binds its quantifiers harmlessly.** -/
theorem quantsV_of_rule {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem}
    {ρ : VarEnv} {v : Value} (hx : x = "Step" ∨ x = "Step_pure" ∨ x = "Step_read")
    (hrel : (simEnv20T B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hex : patExcl.contains (x, i) = false)
    (halt : e' ∈ conclAlts e) (hρ : ρ.typs = []) (he : EvalExp (simEnv20T B) ρ e' v)
    (hv : VOk v) : QuantsV ρ qs := by
  have hc : censusB x rules = true := by
    rcases hx with rfl | rfl | rfl
    · obtain ⟨t', rules', h', hc⟩ := census_step B
      rw [hrel] at h'; cases h'; exact hc
    · obtain ⟨t', rules', h', hc⟩ := census_pure B
      rw [hrel] at h'; cases h'; exact hc
    · obtain ⟨t', rules', h', hc⟩ := census_read B
      rw [hrel] at h'; cases h'; exact hc
  have hp := patOkB_of_census hc hrule hex
  simp only [patOkB, List.all_eq_true] at hp
  exact quantsV_of_pat hρ (by simpa using hp e' halt) he hv

end Silmaril.Wasm.SpecTec.Sim20.VecDer
