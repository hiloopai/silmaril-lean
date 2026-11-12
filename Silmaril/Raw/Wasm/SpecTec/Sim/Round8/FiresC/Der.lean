module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.FiresC.Prem
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckQuant
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckRel

/-!
# Round 8, derivations across code erasure (unrefined)

`dderives_erase`: a `Sim.DDerives` derivation of a relation of `relG` (`Ref_ok`, `Expand` and the
validation relations they reach) at `w` gives one at `eraseC w`, whatever the reading `O` of
`otherwise` (no rule of `relG` has an `otherwise` premise). By mutual structural recursion on the
derivation: quantifiers by `hasTyp_erase`, conclusions and side conditions by round 8's
evaluator-level erasure, relation premises by recursion (`relG` is closed, `relGOk_fixed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps SG ArgIn grC gdC xRule xPrem xIter
  eraseP)

variable {B : Builtins}

theorem findRel?_simEnv (x : IL.Id) :
    (simEnv B).findRel? x = (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).find? x := by
  unfold simEnv baseEnv
  rw [Env.findRel?_withBuiltins, envOfScript, envOfDefs_eq]
  simp [Env.findRel?, Env.empty, Map.empty]

theorem rulesOf_eq {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (h : (simEnv B).findRel? x = some (ps, op, t, rules)) : rulesOf x = rules := by
  unfold rulesOf
  rw [← findRel?_simEnv (B := B), h]

/-- The quantifier types of a rule of a relation `Step` reaches are checked. -/
theorem quants_of_find {x : IL.Id} {d : RelDef} (h : (simEnv B).findRel? x = some d)
    (hx : Round7.Script.stepReach.contains (0, x) = true) {nm : IL.Id} {qs : List Param}
    {op : MixopS} {e : Exp} {prems : List Prem} (hr : Rule.ruleD nm qs op e prems ∈ d.2.2.2) :
    ∀ y t, Param.expP y t ∈ qs → xTy tyC t = true := by
  rw [findRel?_simEnv] at h
  have hm := Round7.Script.mem_of_find? h
  have h₁ := List.all_eq_true.1 xRelQuants_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or] at h₁
  have h₂ := List.all_eq_true.1 h₁ _ hr
  intro y t hq
  simpa using List.all_eq_true.1 h₂ _ hq

/-- What `relGOk_fixed` says about a relation of `relG`. -/
theorem relG_facts {x : IL.Id} {d : RelDef} (h : (simEnv B).findRel? x = some d)
    (hG : relG.contains x = true) :
    grC x = true ∧ Round7.Script.stepReach.contains (0, x) = true ∧ d.1 = [] ∧
      ∀ r ∈ d.2.2.2, relRule r = true := by
  have hok := relGOk_fixed
  simp only [relGOk, Bool.and_eq_true, List.all_eq_true] at hok
  have h₀ := hok.1 x (by simpa using hG)
  rw [findRel?_simEnv] at h
  have h₁ := hok.2 _ (Round7.Script.mem_of_find? h)
  simp only [hG, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff,
    List.all_eq_true] at h₁
  exact ⟨h₀.1, h₀.2, h₁.1, h₁.2⟩

theorem relRule_parts {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    (h : relRule (.ruleD nm qs op e prems) = true) :
    xRule grC gdC (.ruleD nm qs op e prems) = true ∧ ∀ pr ∈ prems, relPrem pr = true := by
  simp only [relRule, Bool.and_eq_true, List.all_eq_true] at h
  exact h

section
variable (H : Hyps QT grC gdC (simEnv B))
include H

/-- **Quantifiers stay typed on the erased scope.** -/
theorem quantsOk_erase {ρ : VarEnv} {qs : List Param} (hρ : SG QT gdC ρ) (hX : XT ρ)
    (hq : ∀ x t, Param.expP x t ∈ qs → xTy tyC t = true) (h : QuantsOk (simEnv B) ρ qs) :
    QuantsOk (simEnv B) (eraseScope ρ) qs := by
  intro x t hm
  obtain ⟨w, hw, ht⟩ := h x t hm
  refine ⟨eraseC w, ?_, hasTyp_erase H hρ hX (hq x t hm) ht⟩
  rw [CodeErase.Erase.find?_eraseScope, hw]
  rfl

omit H in
theorem eraseScope_inst (σ : List (IL.Id × Value)) :
    eraseScope (VarEnv.empty.bindVals σ) = VarEnv.empty.bindVals (σ.map eraseP) := by
  rw [CodeErase.EraseAll.eraseScope_bindVals, CodeErase.EraseAll.eraseScope_empty]

set_option maxRecDepth 20000 in
mutual

/-- **A derivation of a `relG` relation moves across erasure.** -/
theorem dderives_erase {O : ElseI} : ∀ {x : IL.Id} {op : MixopS} {avs : List ArgV} {w : Value},
    DDerives (simEnv B) O x op avs w → relG.contains x = true →
    DDerives (simEnv B) O x op (avs.map eraseA) (eraseC w)
  | x, op, avs, w, .rule (ps := ps) (rules := rules) (i := i) (nm := nm) (qs := qs) (e := e)
      (prems := prems) (ρ₀ := ρ₀) (σ := σ) hrel hrule hps hq he hp, hG =>
    have ih : ∀ pr ∈ prems, ∀ {els' : Prop}, SG QT gdC (ρ₀.bindVals σ) →
        xPrem grC gdC pr = true → (∀ x ∈ premRelsC pr, relG.contains x = true) →
        premElse pr = false → DPrem (simEnv B) O els' (eraseScope (ρ₀.bindVals σ)) pr :=
      fun pr hpr => dprem_erase (hp pr hpr)
    by
    obtain ⟨-, hreach, hps0, hrules⟩ := relG_facts hrel hG
    simp only at hps0
    subst hps0
    have hargs : avs = [] ∧ ρ₀ = VarEnv.empty := by
      cases avs with
      | nil => simp only [bindParams, Option.some.injEq] at hps; exact ⟨rfl, hps.symm⟩
      | cons _ _ => simp [bindParams] at hps
    obtain ⟨rfl, rfl⟩ := hargs
    have hr := relRule_parts (hrules _ (List.mem_of_getElem? hrule))
    have hx := hr.1
    simp only [xRule, Bool.and_eq_true] at hx
    have hρ : SG QT gdC (VarEnv.empty.bindVals σ) := sg_bindVals CodeErase.EraseAll.sg_empty σ
    have hX : XT (VarEnv.empty.bindVals σ) := xt_of_typs xt_empty rfl
    refine DDerives.rule (σ := σ.map eraseP) hrel hrule rfl ?_ ?_ ?_
    · rw [← eraseScope_inst]
      exact quantsOk_erase H hρ hX (quants_of_find hrel hreach (List.mem_of_getElem? hrule)) hq
    · rw [← eraseScope_inst]
      exact evalExp_erase H hρ hx.1 he
    · intro pr hpr
      rw [← eraseScope_inst]
      exact ih pr hpr hρ (CodeErase.EraseAll.xPrems_mem hx.2 pr hpr)
        (relPrem_rels (hr.2 pr hpr)) (relPrem_else (hr.2 pr hpr))

/-- **A premise of a `relG` rule moves across erasure.** -/
theorem dprem_erase {O : ElseI} : ∀ {els els' : Prop} {ρ : VarEnv} {pr : Prem},
    DPrem (simEnv B) O els ρ pr → SG QT gdC ρ → xPrem grC gdC pr = true →
    (∀ x ∈ premRelsC pr, relG.contains x = true) → premElse pr = false →
    DPrem (simEnv B) O els' (eraseScope ρ) pr
  | _, _, ρ, _, .ifPr he, hρ, hx, _, _ =>
    .ifPr (by simpa using evalExp_erase H hρ (by simpa [xPrem] using hx) he)
  | _, _, _, _, .elsePr _, _, _, _, hE => by simp [premElse] at hE
  | _, _, ρ, _, .letPr he₂ he₁, hρ, hx, _, _ => by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .letPr (evalExp_erase H hρ hx.2 he₂) (evalExp_erase H hρ hx.1 he₁)
  | _, _, ρ, .rulePr x _ _ _, .rulePr hargs he hd, hρ, hx, hR, _ =>
    have ih := dderives_erase hd (hR x (by simp [premRelsC]))
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .rulePr (evalArgs_erase H hρ hx.1.2 hargs) (evalExp_erase H hρ hx.2 he) ih
  | _, _, ρ, _, .iterOptNone (xvs := xvs) hdoms hne hall, hρ, hx, _, _ => by
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterOptNone (evalDoms_erase H hρ hx.2 hdoms) hne ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    simp [eraseP, hall q hq]
  | _, _, ρ, _, .iterOptSome (row := row) hdoms hne hsome hpr, hρ, hx, hR, hE =>
    have ih := fun h => dprem_erase (els' := _) hpr (sg_bindVals hρ row) h hR hE
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterOptSome (row := row.map eraseP) (evalDoms_erase H hρ hx.2 hdoms) hne
      (by rw [domSomes_erase, hsome]; rfl) ?_
    rw [← CodeErase.EraseAll.eraseScope_bindVals]
    exact ih hx.1.1
  | _, _, ρ, _, .iterList (dls := dls) (k := k) hit hdoms hne hdl hlen hrows, hρ, hx, hR, hE =>
    have ih := fun r₀ hr₀ h => dprem_erase (els' := _) (hrows r₀ hr₀) (sg_bindVals hρ r₀) h hR hE
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterList (dls := dls.map fun p => (p.1, p.2.map eraseC)) (k := k) hit
      (evalDoms_erase H hρ hx.2 hdoms) hne (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [CodeErase.EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← CodeErase.EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ hx.1.1
  | _, _, ρ, _, .iterListN (eₙ := eₙ) (dls := dls) (kv := kv) (k := k) hdoms hn hk hdl hlen hrows,
      hρ, hx, hR, hE =>
    have ih := fun r₀ hr₀ h => dprem_erase (els' := _) (hrows r₀ hr₀) (sg_bindVals hρ r₀) h hR hE
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    have hxn : CodeErase.EraseAll.xExp grC gdC eₙ = true := by simpa [xIter] using hx.1.2
    refine .iterListN (dls := dls.map fun p => (p.1, p.2.map eraseC)) (kv := eraseC kv) (k := k)
      (evalDoms_erase H hρ hx.2 hdoms) (evalExp_erase H hρ hxn hn)
      (by rw [asNat?_eraseC]; exact hk) (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [CodeErase.EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← CodeErase.EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ hx.1.1

end

end

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
