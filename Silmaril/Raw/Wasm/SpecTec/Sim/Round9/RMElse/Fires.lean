module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMElse.Check

/-!
# Round 9, rm: the rule case of `FiresC.fires_erase_rel` with an `otherwise` premise (unrefined)

`fires_erase_else`: a rule of `Step_read` that is `elseRuleC` keeps firing (`Sim.Fires`) when the
function code is erased, given `ElseBwd.ElseBwdDRest`. The rule body moves by
`FiresC.ruleBody_erase`: relation premises by `FiresC.dderives_erase`, the `otherwise` premise by
`ElseBwd.otherwise_eraseC_rest` at the firing itself (`ElseBwd.FiredD`, read off the rule body).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps grC gdC xRule)
open Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

variable {B : Builtins}

theorem elseRuleC_parts {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : elseRuleC (.ruleD nm qs op e prems) = true) :
    xRule grC gdC (.ruleD nm qs op e prems) = true ∧
      ElseBwd.hasElse (.ruleD nm qs op e prems) = true ∧ ∀ pr ∈ prems, elsePremC pr = true := by
  simp only [elseRuleC, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem elsePremC_rels {pr : Prem} (h : elsePremC pr = true) :
    ∀ x ∈ premRelsC pr, relG.contains x = true := by
  cases pr with
  | elsePr => intro x hx; simp [premRelsC] at hx
  | _ => exact relPrem_rels h

theorem elseRule_of {i : Nat} (hi : i ∈ elseRead) :
    ∃ r, (rulesOf "Step_read")[i]? = some r ∧ elseRuleC r = true := by
  have h := List.all_eq_true.1 elseAt_ok i hi
  revert h
  cases (rulesOf "Step_read")[i]? with
  | none => intro h; cases h
  | some r => intro h; exact ⟨r, rfl, h⟩

/-- **An `otherwise` rule of `Step_read` keeps firing when the code is erased**, given the
backward firing at the 68 pairs of `ElseBwdDRest`. -/
theorem fires_erase_else (H : Hyps QT grC gdC (simEnv B))
    (hR : ElseBwd.ElseBwdDRest (simEnv B)) {i : Nat} (hi : i ∈ elseRead) {v : Value}
    (h : Fires (simEnv B) "Step_read" i v) : Fires (simEnv B) "Step_read" i (eraseC v) := by
  obtain ⟨t, rules, r, hf, hr, hb⟩ := h
  refine ⟨t, rules, r, hf, hr, ?_⟩
  obtain ⟨r', hr', hel⟩ := elseRule_of hi
  rw [rulesOf_eq hf, hr, Option.some.injEq] at hr'
  subst hr'
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨hx, hhas, hps⟩ := elseRuleC_parts hel
  have hFd : ElseBwd.FiredD (simEnv B) "Step_read" [] i v := by
    obtain ⟨hop, ρ₀, σ, hb₀, hq, he, -⟩ := hb
    subst hop
    exact ⟨[], "%~>%", t, rules, nm, qs, e, prems, ρ₀, σ, hf, hr, hb₀, hq, he⟩
  refine ruleBody_erase H hx (quants_of_find hf Round8.FiresC.stepRead_reach
    (List.mem_of_getElem? hr)) ?_ ?_ hb
  · intro pr hpr y op avs w hy hd
    exact dderives_erase H hd (elsePremC_rels (hps pr hpr) y hy)
  · intro _ _ _ hO
    exact ElseBwd.otherwise_eraseC_rest hR hf hr hhas hFd hO

/-- **`RMCode.FiresEraseD` at the 28 `otherwise` rules**, given `ElseBwdDRest`. -/
theorem firesEraseD_else (H : Hyps QT grC gdC (simEnv B))
    (hR : ElseBwd.ElseBwdDRest (simEnv B)) {X : Type} (hn : X → String) {i : Nat}
    (hi : i ∈ elseRead) : Round8.RMCode.FiresEraseD (simEnv B) hn "Step_read" i :=
  fun _ _ _ _ h => fires_erase_else H hR hi h

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
