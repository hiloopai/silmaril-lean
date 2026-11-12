module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseRef.Base

/-!
# Round 9, RE: `refBwd`, `Ref_ok` backward across erasure of the store (unrefined)

By structural recursion on the derivation, together with `refPremBwd` on the `Ref_ok` premises.
See `Base` for the argument.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB DPremB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

theorem refConcl_inv {qs : List Param} {s : IL.Id} {c : Exp} (h : refConcl qs s c = true) :
    ∃ e₂ e₃, c = .tupE [.varE s, e₂, e₃] ∧ nxIn qs e₂ = true ∧ nxIn qs e₃ = true := by
  unfold refConcl at h
  split at h
  · rename_i s' e₂ e₃
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, h₂⟩, h₃⟩ := h
    exact ⟨e₂, e₃, rfl, h₂, h₃⟩
  · cases h

section Ref

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  {O : ElseI}
include hB H

set_option maxRecDepth 20000

mutual
/-- **`Ref_ok` backward across erasure of the store.** -/
theorem refBwd : ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {w : Value},
    DDerivesB (utf8Env B) O x op args w → x = "Ref_ok" → ∀ sv r t : Value,
    w = .tuple [eraseV sv, r, t] →
    HasTyp (utf8Env B) VarEnv.empty (.varT "store" []) sv →
    DDerivesB (utf8Env B) O x op args (.tuple [sv, r, t])
  | x, op, args, w, .rule (σ := σ) (ρ₀ := ρ₀) (qs := qs) (ps := ps) (prems := prems) (i := i)
      (e' := e') hrel hrule halt hps hq he hp, hx, sv, r, t, hw, hsv => by
    have hrec := fun pr (hpr : pr ∈ prems) (o : MixopS) (c : Exp)
      (h : pr = .rulePr "Ref_ok" [] o c) => refPremBwd (hp pr hpr) h
    subst hx
    subst hw
    have hD := NxFlow.flowSound B hB
    obtain ⟨hps0, hall⟩ := refRel_at hrel
    subst hps0
    obtain ⟨-, hρ⟩ := EraseDer.bindParams_nil_args hps
    subst hρ
    have hrr := hall _ (List.mem_of_getElem? hrule)
    simp only [refRule, List.all_eq_true] at hrr
    have hra := hrr e' halt
    split at hra
    case h_2 => cases hra
    rename_i s e₂ e₃
    simp only [Bool.and_eq_true, Bool.not_eq_true', refConcl, beq_self_eq_true, true_and,
      List.all_eq_true] at hra
    obtain ⟨⟨⟨⟨⟨hsq, hqn⟩, hqv⟩, hsn⟩, hn₂, hn₃⟩, hpp⟩ := hra
    have hsn' : s ∉ Round8.NxTyp.nxNames qs := fun hm => by
      rw [List.contains_iff_mem.2 hm] at hsn; cases hsn
    -- the erased side
    obtain ⟨n, hn⟩ := he
    obtain ⟨k, sv', r', t', rfl, hs', hr', ht', hw'⟩ := evalExp_triple' hn
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw'
    obtain ⟨rfl, rfl, rfl⟩ := hw'
    have hfs : (VarEnv.empty.bindVals σ).findVal? s = some (eraseV sv) := evalExp_varE hs'
    -- the new instance
    have hrd : reach 0 "Ref_ok" = true := by decide
    have hFj := NxRule.rFacts hrd hrel hrule
    have hzw : s ≠ "_" := fun h => hFj.wild (h ▸ typQ_mem hsq)
    have hfz : (VarEnv.empty.bindVals (σ ++ [(s, sv)])).findVal? s = some sv :=
      findVal_snoc_self hzw sv
    have hfo : ∀ y, y ≠ s → (VarEnv.empty.bindVals (σ ++ [(s, sv)])).findVal? y =
        (VarEnv.empty.bindVals σ).findVal? y := fun y hy => findVal_snoc_ne hy sv
    have hval : ∀ y ty, Param.expP y ty ∈ qs → y ≠ s → ∃ w,
        (VarEnv.empty.bindVals σ).findVal? y = some w ∧ nxB w = true := fun y ty hy hys =>
      NxSites.nxB_of_quantsOk (NxSites.typsNx_bindVals (NxSites.typsNx_empty _) σ) hq hy
        (quantsNxL_mem hqn hy (by simpa using hys))
    have hagr : Round8.NxTyp.Agr (Round8.NxTyp.nxNames qs) (VarEnv.empty.bindVals σ)
        (VarEnv.empty.bindVals (σ ++ [(s, sv)])) :=
      ⟨fun y hy => hfo y (fun h => hsn' (h ▸ hy)), rfl, rfl, rfl⟩
    have hqj : QuantsOk (utf8Env B) (VarEnv.empty.bindVals (σ ++ [(s, sv)])) qs := by
      intro y ty hy
      by_cases hys : y = s
      · subst hys
        have := typQ_type hsq hy
        subst this
        exact ⟨sv, hfz, hasTyp_varT_scope rfl rfl hsv⟩
      · obtain ⟨w, hw, hty⟩ := hq y ty hy
        obtain ⟨m, rfl⟩ := quantsVar_mem hqv hy
        exact ⟨w, (hfo y hys).trans hw, hasTyp_var_inst hty⟩
    have hag : ∀ st, EraseDer.varsIn (quantNames qs) st = true →
        VarEnv.AgreeOn st (eraseScope (VarEnv.empty.bindVals (σ ++ [(s, sv)])))
          (VarEnv.empty.bindVals σ) := by
      intro st hst
      refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
      rw [Erase.find?_eraseScope]
      by_cases hys : y = s
      · subst hys; rw [hfz, hfs]; rfl
      · obtain ⟨ty, hty⟩ := mem_quantNames (EraseDer.varsIn_mem hst y hy)
        obtain ⟨w, hw, hnw⟩ := hval y ty hty hys
        rw [hfo y hys, hw]
        simp [Swap.eraseV_of_nxB _ hnw]
    have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
        (qScope qs (VarEnv.empty.bindVals (σ ++ [(s, sv)]))) k :=
      fun k => NxClause.clauseErase B hB H _ k rfl rfl
    have hnxe : ∀ {k : Nat} {e : Exp} {u : Value}, nxIn qs e = true →
        evalExp k (utf8Env B) (VarEnv.empty.bindVals σ) e = .ok u →
        evalExp k (utf8Env B) (VarEnv.empty.bindVals (σ ++ [(s, sv)])) e = .ok u :=
      fun he hu => by rw [← evalExp_agreeOn (Round8.NxElse.agreeOn_of_agr hagr he)]; exact hu
    refine .rule (σ := σ ++ [(s, sv)]) hrel hrule halt hps hqj
      ⟨k + 2, evalExp_triple_mk (evalExp_varE_swap hs' hfz) (hnxe hn₂ hr') (hnxe hn₃ ht')⟩
      fun pr hpr => ?_
    have hppr := hpp pr hpr
    cases pr with
    | ifPr c =>
      simp only [refPrem] at hppr
      cases hp _ hpr with
      | ifPr h =>
        obtain ⟨n₀, hn₀⟩ := h
        rw [← evalExp_agreeOn (hag _ (closedX_parts hppr).1)] at hn₀
        exact .ifPr ⟨n₀, closedX_true hD H hqj hCE hppr hn₀⟩
    | rulePr y args o c =>
      cases args with
      | cons _ _ => simp [refPrem] at hppr
      | nil =>
      by_cases hy : y = "Ref_ok"
      · subst hy
        simp only [refPrem, beq_self_eq_true, ite_true] at hppr
        obtain ⟨e₂', e₃', rfl, h₂, h₃⟩ := refConcl_inv hppr
        obtain ⟨avs, w₀, hav, ⟨n₀, hn₀⟩, hf⟩ := hrec _ hpr _ _ rfl
        obtain ⟨k₀, sv₀, r₀, t₀, rfl, hs₀, hr₀, ht₀, rfl⟩ := evalExp_triple' hn₀
        rw [evalExp_varE hs₀] at hfs
        cases hfs
        exact .rulePr (ElseExp.evalArgs_nil hav)
          ⟨k₀ + 2, evalExp_triple_mk (evalExp_varE_swap hs₀ hfz) (hnxe h₂ hr₀) (hnxe h₃ ht₀)⟩
          (hf sv r₀ t₀ rfl hsv)
      · have hppr' : closedNx qs c = true := by
          simpa only [refPrem, beq_iff_eq, hy, ite_false] using hppr
        cases hp _ hpr with
        | rulePr hav hev hd =>
          obtain ⟨n₀, hn₀⟩ := hev
          have hcx : closedX qs c = true := by
            simp only [closedNx, Bool.and_eq_true] at hppr'; exact hppr'.1
          rw [← evalExp_agreeOn (hag _ (closedX_parts hcx).1)] at hn₀
          exact .rulePr (ElseExp.evalArgs_nil hav) ⟨n₀, closedNx_self hD H hqj hCE hppr' hn₀⟩ hd
    | elsePr => simp [refPrem] at hppr
    | letPr _ _ => simp [refPrem] at hppr
    | iterPr _ _ => simp [refPrem] at hppr
  termination_by structural _ _ _ _ hd => hd

/-- **A `Ref_ok` premise read backward.** -/
theorem refPremBwd : ∀ {els : Prop} {ρ : VarEnv} {pr : Prem},
    DPremB (utf8Env B) O els ρ pr → ∀ {o : MixopS} {c : Exp}, pr = .rulePr "Ref_ok" [] o c →
    ∃ avs w, EvalArgs (utf8Env B) ρ [] avs ∧ EvalExp (utf8Env B) ρ c w ∧
      ∀ sv r t : Value, w = .tuple [eraseV sv, r, t] →
        HasTyp (utf8Env B) VarEnv.empty (.varT "store" []) sv →
        DDerivesB (utf8Env B) O "Ref_ok" o avs (.tuple [sv, r, t])
  | _, _, _, .rulePr hav hev hd, _, _, h => by
    have hr := fun hx sv r t hw hs => refBwd hd hx sv r t hw hs
    cases h
    exact ⟨_, _, hav, hev, fun sv r t hw hs => hr rfl sv r t hw hs⟩
  | _, _, _, .ifPr _, _, _, h => by cases h
  | _, _, _, .elsePr _, _, _, h => by cases h
  | _, _, _, .letPr _ _, _, _, h => by cases h
  | _, _, _, .iterOptNone _ _ _, _, _, h => by cases h
  | _, _, _, .iterOptSome _ _ _ _, _, _, h => by cases h
  | _, _, _, .iterList _ _ _ _ _ _, _, _, h => by cases h
  | _, _, _, .iterListN _ _ _ _ _ _, _, _, h => by cases h
  termination_by structural _ _ _ hd => hd
end

end Ref

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef
