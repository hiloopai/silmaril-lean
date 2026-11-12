module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.FiresC.Der

/-!
# Round 8, firing across code erasure: rules (unrefined)

* `ruleBody_erase`: a rule body (`Sim.RuleBody`) that holds at `v` holds at `eraseC v`, for a
  rule that passes round 8's check, has checked quantifier types, and whose relation and
  `otherwise` premises move.
* `fires_erase_rel`: so a `relRule` of a relation `Step` reaches (no `otherwise` premise,
  relation premises in `relG`) keeps firing (`Sim.Fires`) when the function code is erased; its
  relation premises move by `dderives_erase`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps SG ArgIn grC gdC xRule eraseP)

variable {B : Builtins}

theorem rel_of_relAt {x : IL.Id} {l : List Nat} (hl : relAt x l = true) {i : Nat}
    (hi : i ∈ l) : ∃ r, (rulesOf x)[i]? = some r ∧ relRule r = true := by
  have h := List.all_eq_true.1 hl i hi
  revert h
  cases (rulesOf x)[i]? with
  | none => intro h; cases h
  | some r => intro h; exact ⟨r, rfl, h⟩

section
variable (H : Hyps QT grC gdC (simEnv B))
include H

/-- **A rule body moves across erasure.** -/
theorem ruleBody_erase {D D' : Interp} {els els' : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem} {v : Value}
    (hx : xRule grC gdC (.ruleD nm qs op' e prems) = true)
    (hq : ∀ x t, Param.expP x t ∈ qs → xTy tyC t = true)
    (hR : ∀ pr ∈ prems, ∀ x op avs w, x ∈ premRelsC pr → D x op avs w →
      D' x op (avs.map eraseA) (eraseC w))
    (hE : ∀ pr ∈ prems, premElse pr = true → els → els')
    (h : RuleBody (simEnv B) D els [] [] op (.ruleD nm qs op' e prems) v) :
    RuleBody (simEnv B) D' els' [] [] op (.ruleD nm qs op' e prems) (eraseC v) := by
  obtain ⟨hop, ρ₀, σ, hb, hqs, he, hps⟩ := h
  simp only [bindParams, Option.some.injEq] at hb
  subst hb
  simp only [xRule, Bool.and_eq_true] at hx
  have hρ : SG QT gdC (VarEnv.empty.bindVals σ) := sg_bindVals CodeErase.EraseAll.sg_empty σ
  have hX : XT (VarEnv.empty.bindVals σ) := xt_of_typs xt_empty rfl
  refine ⟨hop, VarEnv.empty, σ.map eraseP, rfl, ?_, ?_, ?_⟩
  · rw [← eraseScope_inst]; exact quantsOk_erase H hρ hX hq hqs
  · rw [← eraseScope_inst]; exact evalExp_erase H hρ hx.1 he
  · intro pr hpr
    rw [← eraseScope_inst]
    exact premW_erase H (hps pr hpr) hρ (CodeErase.EraseAll.xPrems_mem hx.2 pr hpr) (hR pr hpr)
      (hE pr hpr)

/-- **A `relRule` of a relation `Step` reaches keeps firing when the code is erased.** -/
theorem fires_erase_rel {x : IL.Id} {i : Nat}
    (hx : Round7.Script.stepReach.contains (0, x) = true)
    (hp : ∃ r, (rulesOf x)[i]? = some r ∧ relRule r = true) {v : Value}
    (h : Fires (simEnv B) x i v) : Fires (simEnv B) x i (eraseC v) := by
  obtain ⟨t, rules, r, hf, hr, hb⟩ := h
  refine ⟨t, rules, r, hf, hr, ?_⟩
  obtain ⟨r', hr', hpl⟩ := hp
  rw [rulesOf_eq hf, hr, Option.some.injEq] at hr'
  subst hr'
  obtain ⟨nm, qs, op', e, prems⟩ := r
  have hparts := relRule_parts hpl
  refine ruleBody_erase H hparts.1 (quants_of_find hf hx (List.mem_of_getElem? hr)) ?_ ?_ hb
  · intro pr hpr y op avs w hy hd
    exact dderives_erase H hd (relPrem_rels (hparts.2 pr hpr) y hy)
  · intro pr hpr he
    rw [relPrem_else (hparts.2 pr hpr)] at he
    cases he

end

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
