module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.StateTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckGrow

/-!
# Round 7, moving derivations across erasure: the grow rules of `Step` (unrefined)

`ruleFwd_grow`, `ruleBwd_grow`: the rules `table.grow-succeed` and `memory.grow-succeed` of `Step`
commute with erasure (`RuleFwd`, `RuleBwd`), at round 6's primitives, for a swap set with the
evaluator-level hypotheses at `grE` and `grB`.

Their conclusion is `(l, (%;% ($W(z, y₂, y₃), r)))` (kernel check `xGrowOk_fixed`). Everything but
the call `$W(z, y₂, y₃)` passes the evaluator-level check, and the call commutes with erasure once
`z` is a state `(S; F)` whose store has no `EXPORTS` field (round 3's
`Round7.EraseAll.callDef_withTableinst_state`/`callDef_withMeminst_state`). The quantifier
`z : state` is typed, so `state_inv` gives exactly that. The mode analysis, the premises and the
quantifier typing go across as for the other rules of `Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DDerivesBQ DPremBQ QuantsP Hyps xPrem xExp xArgs
  eraseP grE gdE grB gdB InAI AIOn DefsG PremFactQ defsG_empty defsG_bindVals ai_eval_on
  aiOn_ruleK SG)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (premDetOk detFacts quantNames)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

variable {Q : Value → Prop}

/-! ## The shape of a grow rule -/

/-- The conclusion of a grow rule. -/
def growE (l : Exp) (w y₂ y₃ : IL.Id) (r : Exp) : Exp :=
  .tupE [l, .caseE "%;%" (.tupE [.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)],
    r])]

theorem growShape_inv {e : Exp} (h : growShape e = true) :
    ∃ l w y₂ y₃ r, e = growE l w y₂ y₃ r ∧ (w = "with_tableinst" ∨ w = "with_meminst") ∧
      xExp grB gdB l = true ∧ xExp grB gdB r = true := by
  unfold growShape at h
  split at h
  · rename_i l w y₂ y₃ r
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    exact ⟨l, w, y₂, y₃, r, rfl, h.1.1, h.1.2, h.2⟩
  · exact absurd h (by simp)

theorem hasStateZ_mem {qs : List Param} (h : hasStateZ qs = true) :
    Param.expP "z" (.varT "state" []) ∈ qs := by
  obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h
  split at hq'
  · exact hq
  · exact absurd hq' (by simp)

/-- What the kernel checks say about a grow rule. -/
structure GrowFacts (ps qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  params : ps = []
  alts : conclAlts e = [e]
  shape : growShape e = true
  zq : Param.expP "z" (.varT "state" []) ∈ qs
  prems : ∀ pr ∈ prems, (xPrem grB gdB pr = true ∧ noElseP pr = true) ∧
    varsIn (quantNames qs) (freePrem pr) = true
  closed : varsIn (quantNames qs) (freeExp e) = true
  quants : ∀ y t, Param.expP y t ∈ qs →
    xTy TypAgree.tyB t = true ∧ varsIn (quantNames qs) (freeTyp t) = true

theorem growFacts {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hrel : (utf8Env B).findRel? "Step" = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hnm : nm ∈ growNames) :
    GrowFacts ps qs e prems := by
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hF := detFacts step_reach hrel' hrule
  have hm := EraseAll.mem_rels_of_findRel' hrel'
  obtain ⟨d', hd', hm'⟩ := EraseAll.mem_relsOfDefs hm
  have hS := List.all_eq_true.1 (List.all_eq_true.1 xGrowOk_fixed d' hd') _ hm'
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at hS
  have hS' := hS _ hr
  have hnm' : growNames.contains nm = true := by simpa using hnm
  simp only [xGrowRule, hnm', Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨hno, hsh⟩, hz⟩, hprs⟩ := hS'
  have hreach' : Script.stepReach.contains (0, "Step") = true := List.contains_iff_mem.2 step_reach
  have hc := List.all_eq_true.1 closedRels_fixed _ hm
  simp only [hreach', Bool.not_true, Bool.false_or] at hc
  have hcl := List.all_eq_true.1 hc _ hr
  simp only [ruleClosed, Bool.and_eq_true, List.all_eq_true] at hcl
  have hq := List.all_eq_true.1 xRelQuants_fixed _ hm
  simp only [hreach', Bool.not_true, Bool.false_or, List.all_eq_true] at hq
  have hq' := hq _ hr
  simp only [List.all_eq_true] at hq'
  have halts : conclAlts e = [e] := by simp [conclAlts, hno]
  refine ⟨hF.params, halts, hsh, hasStateZ_mem hz, fun pr hpr => ⟨?_, hcl.1.2 pr hpr⟩,
    hcl.1.1 e (by simp [halts]), fun y ty hy => ⟨?_, ?_⟩⟩
  · simpa using hprs pr hpr
  · simpa using hq' _ hy
  · simpa using hcl.2 _ hy

/-! ## The call -/

theorem evalArg_var {n : Nat} {env : Env} {ρ : VarEnv} {y : IL.Id} {a : ArgV}
    (h : evalArg n env ρ (.expA (.varE y)) = .ok a) : ∃ v, ρ.findVal? y = some v ∧ a = .val v := by
  cases n with
  | zero => simp [evalArg] at h
  | succ n =>
    simp only [evalArg, Res.map_eq_ok] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨v, evalExp_varE_iff.1 ⟨n, hv⟩, rfl⟩

theorem evalArgs_vars3 {k : Nat} {env : Env} {ρ : VarEnv} {y₁ y₂ y₃ : IL.Id} {ws : List ArgV}
    (h : evalArgs k env ρ [.expA (.varE y₁), .expA (.varE y₂), .expA (.varE y₃)] = .ok ws) :
    ∃ v₁ v₂ v₃, ρ.findVal? y₁ = some v₁ ∧ ws = [.val v₁, .val v₂, .val v₃] := by
  cases k with
  | zero => simp [evalArgs] at h
  | succ k =>
    simp only [evalArgs, List.mapM_cons, List.mapM_nil, Res.bind_eq_ok, pure, Except.pure] at h
    obtain ⟨a₁, h₁, l₁, ⟨a₂, h₂, l₂, ⟨a₃, h₃, l₃, hl₃, hl₂⟩, hl₁⟩, hws⟩ := h
    obtain ⟨v₁, hv₁, rfl⟩ := evalArg_var h₁
    obtain ⟨v₂, -, rfl⟩ := evalArg_var h₂
    obtain ⟨v₃, -, rfl⟩ := evalArg_var h₃
    cases Except.ok.inj hl₃
    cases Except.ok.inj hl₂
    cases Except.ok.inj hl₁
    exact ⟨v₁, v₂, v₃, hv₁, (Except.ok.inj hws).symm⟩

theorem findDef_aiPart {ρ : VarEnv} (hd : ρ.defs = []) (x : IL.Id) :
    (aiPart Q ρ).findDef? x = none := by
  simp [aiPart, VarEnv.findDef?, hd]

section Call

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **The call `$W(z, y₂, y₃)` of a grow rule goes across erasure**, both ways, when `z` is bound
to a state whose store has no `EXPORTS` field. -/
theorem callW_er (HE : Hyps Q grE gdE (utf8Env (Round4Int.BI P hn host))) {w y₂ y₃ : IL.Id}
    (hw : w = "with_tableinst" ∨ w = "with_meminst") {gd : String → Bool} {ρ ρ' : VarEnv}
    (hR : ErRel Q gd (freeExp (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]))
      ρ ρ')
    (hd : ρ.defs = []) {S F : Value} (hz : ρ.findVal? "z" = some (stV S F))
    (hS : ∀ gs, S = .struct gs → hasExp gs = false) (hza : AllIn Q (stV S F)) :
    (∀ u, EvalExp (utf8Env (Round4Int.BI P hn host)) ρ
        (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) u →
      EvalExp (utf8Env (Round4Int.BI P hn host)) ρ'
        (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) (eraseV u) ∧
        AllIn Q u) ∧
    (∀ u', EvalExp (utf8Env (Round4Int.BI P hn host)) ρ'
        (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) u' →
      ∃ u, EvalExp (utf8Env (Round4Int.BI P hn host)) ρ
        (.callE w [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) u ∧
        eraseV u = u' ∧ AllIn Q u) := by
  have hD : DefsG gdE ρ := fun p hp => by rw [hd] at hp; cases hp
  have hsg : SG Q gdE (aiPart Q ρ) := sg_aiPart hD
  have hz₀ : (aiPart Q ρ).findVal? "z" = some (stV S F) := by
    have h := EraseAll.find?_filter_ai (Q := Q) (x := "z") ρ.vals
      (fun w' hw' => by
        have : ρ.findVal? "z" = some w' := hw'
        rw [hz] at this; cases this; exact hza)
    show Map.find? (ρ.vals.filter _) "z" = _
    rw [h]; exact hz
  have hl : xArgs grE gdE [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)] = true := by
    simp [xArgs, EraseAll.xArg, xExp]
  have hst : ∀ k ws, evalArgs k (utf8Env (Round4Int.BI P hn host)) (aiPart Q ρ)
      [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)] = .ok ws →
      ∃ S F X Y, ws = [.val (stV S F), .val X, .val Y] ∧
        ∀ gs, S = .struct gs → hasExp gs = false := by
    intro k ws hk
    obtain ⟨v₁, v₂, v₃, hv₁, rfl⟩ := evalArgs_vars3 hk
    rw [hz₀] at hv₁
    cases hv₁
    exact ⟨S, F, v₂, v₃, rfl, hS⟩
  have hER : ∀ n, EraseAll.ER eraseV (AllIn Q)
      (callDef n (utf8Env (Round4Int.BI P hn host)) (aiPart Q ρ) w
        [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)])
      (callDef n (utf8Env (Round4Int.BI P hn host)) (Erase.eraseScope (aiPart Q ρ)) w
        [.expA (.varE "z"), .expA (.varE y₂), .expA (.varE y₃)]) := by
    rcases hw with rfl | rfl
    · exact EraseAll.callDef_withTableinst_state P hn host HE hsg (findDef_aiPart hd _) hl hst
    · exact EraseAll.callDef_withMeminst_state P hn host HE hsg (findDef_aiPart hd _) hl hst
  refine ⟨fun u hu => ?_, fun u' hu' => ?_⟩
  · obtain ⟨n, hn'⟩ := evalExp_callE_iff.1 (hu.agreeOn hR.ai)
    refine ⟨?_, (hER n).2 u hn'⟩
    have h₂ := ((hER n).ok_iff).2 ⟨u, hn', rfl⟩
    exact (evalExp_callE_iff.2 ⟨n, h₂⟩).agreeOn hR.er.symm
  · obtain ⟨n, hn'⟩ := evalExp_callE_iff.1 (hu'.agreeOn hR.er)
    obtain ⟨u, hu, rfl⟩ := ((hER n).ok_iff).1 hn'
    exact ⟨u, (evalExp_callE_iff.2 ⟨n, hu⟩).agreeOn hR.ai.symm, rfl, (hER n).2 u hu⟩

end Call

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
