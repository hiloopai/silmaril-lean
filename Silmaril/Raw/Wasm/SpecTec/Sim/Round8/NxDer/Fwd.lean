module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxDer.CheckIter

/-!
# Round 8, derivations across erasure without a swap set: the forward direction (unrefined)

`dderivesB_fwd`: a `DDerivesB` derivation of a `grE` relation gives one of the erased value from
the erased arguments, provided the primitives conform and commute with erasure on `gdE`, and
every `otherwise` read on the original side is read on the erased side (`hO`).

The proof is by structural recursion on the derivation, as round 7's `EraseDer.dderivesB_fwd`,
with the swap set replaced as follows.

* At a rule instance the erased scope binds `σ` erased. The quantifiers stay typed by round 8's
  `NxTyp.typFwdN_utf8Env`; the conclusion goes across by round 7's `NxErase.erase_alt`, with
  clause bodies answered by round 8's `NxClause.clauseErase`.
* A top-level `if` premise goes across by `NxClause.ifPr_fwd`, binding sites included.
* Every other premise has no failing comparison site (`NxRule.badPr_zero`). It is read in a
  context `PCtx Γ ρq`: a conforming scope `ρq` (`NxFlow.ScopeVT`) whose calls conform and commute
  with erasure, and that agrees with the premise's scope on its free variables. At the top level
  `ρq` is the quantifier part `NxRule.qScope` of the instance's scope. Expressions go across by
  `NxErase.nAt` (`exp_fwd`, `args_fwd`, `doms_fwd`).
* An iterated premise iterates over a list (`iterRels_fixed`). Its rows extend `ρq` conformingly
  (`NxFlow.rowScope_list`, from the conformance of the domains, `NxFlow.expAt`).
* A relation premise goes across by the recursion.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0 premAuxR)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT NCalls nAt auxX premX)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp xPrem eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {B : Builtins}

/-! ## Scopes -/

theorem agreeOn_erase {s : Sets} {ρ₁ ρ₂ : VarEnv} (h : VarEnv.AgreeOn s ρ₁ ρ₂) :
    VarEnv.AgreeOn s (eraseScope ρ₁) (eraseScope ρ₂) :=
  ⟨fun x hx => by rw [Erase.find?_eraseScope, Erase.find?_eraseScope, h.1 x hx], h.2.1, h.2.2.1,
    h.2.2.2⟩

theorem eraseScope_inst (σ : List (IL.Id × Value)) :
    eraseScope (VarEnv.empty.bindVals σ) = VarEnv.empty.bindVals (σ.map eraseP) := by
  rw [EraseAll.eraseScope_bindVals]
  rfl

/-- **The context of a premise**: a conforming scope whose calls conform and whose clause bodies
commute with erasure at every fuel. -/
structure PCtx (B : Builtins) (Γ : List (String × AT)) (ρq : VarEnv) : Prop where
  vt : ScopeVT sigX Γ ρq
  nc : ∀ n, NCalls gdE sigX tsigFixed ctx0 (utf8Env B) ρq n

section Exp

variable (H : BIErase QT gdE (utf8Env B)) {Γ : List (String × AT)} {ρq ρ : VarEnv}
  (hc : PCtx B Γ ρq)
include H hc

/-- **An expression goes to the erased side** in a scope that agrees with a context on its free
variables. -/
theorem exp_fwd {e : Exp} {v : Value} (hag : VarEnv.AgreeOn (freeExp e) ρ ρq)
    (ht : tyOk sigX tsigFixed Γ e = true) (ha : auxE ctx0 e = true) (hX : auxX ctx0 e = true)
    (hb : badE sigX Γ e = 0) (hx : xExp grE gdE e = true) (h : EvalExp (utf8Env B) ρ e v) :
    EvalExp (utf8Env B) (eraseScope ρ) e (eraseV v) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hE := ((nAt (gr := grE) H n).exp sigX tsigFixed Γ ctx0 ρq e hc.vt (hc.nc n) ht ha hX hb
    hx).1
  rw [evalExp_agreeOn (agreeOn_erase hag), hE, ← evalExp_agreeOn hag, hn]
  rfl

/-- **Arguments go to the erased side.** -/
theorem args_fwd {xs : List Arg} {ws : List ArgV} (hag : VarEnv.AgreeOn (freeArgs xs) ρ ρq)
    (ht : tyOkA sigX tsigFixed Γ xs = true) (ha : auxA ctx0 xs = true)
    (hX : NxErase.auxXA ctx0 xs = true) (hb : badAs sigX Γ xs = 0)
    (hx : EraseAll.xArgs grE gdE xs = true) (h : EvalArgs (utf8Env B) ρ xs ws) :
    EvalArgs (utf8Env B) (eraseScope ρ) xs (ws.map eraseA) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hE := ((nAt (gr := grE) H n).args sigX tsigFixed Γ ctx0 ρq xs hc.vt (hc.nc n) ht ha hX hb
    hx).1
  rw [evalArgs_agreeOn (agreeOn_erase hag), hE, ← evalArgs_agreeOn hag, hn]
  rfl

/-- **Iteration domains go to the erased side.** -/
theorem doms_fwd {ds : List Dom} {xvs : List (IL.Id × Value)}
    (hag : VarEnv.AgreeOn (freeDoms ds) ρ ρq) (ht : tyOkD sigX tsigFixed Γ ds = true)
    (ha : auxD ctx0 ds = true) (hX : NxErase.auxXD ctx0 ds = true) (hb : badDs sigX Γ ds = 0)
    (hx : EraseAll.xDoms grE gdE ds = true) (h : EvalDoms (utf8Env B) ρ ds xvs) :
    EvalDoms (utf8Env B) (eraseScope ρ) ds (xvs.map eraseP) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hE := ((nAt (gr := grE) H n).doms sigX tsigFixed Γ ctx0 ρq ds hc.vt (hc.nc n) ht ha hX hb
    hx).1
  rw [evalDoms_agreeOn (agreeOn_erase hag), hE, ← evalDoms_agreeOn hag, hn]
  rfl

end Exp

/-- The rows of a list iteration extend a context. -/
theorem pCtx_row {Γ : List (String × AT)} {ρq : VarEnv} (hc : PCtx B Γ ρq) {ds : List Dom}
    {xvs : List (IL.Id × Value)} (hnd : nodupB (ds.map domVar) = true)
    (htd : tyOkD sigX tsigFixed Γ ds = true) (had : auxD ctx0 ds = true)
    (hd : EvalDoms (utf8Env B) ρq ds xvs) {dls : List (IL.Id × List Value)}
    (hl : domLists xvs = some dls) {k : Nat} (hlen : ∀ d ∈ dls, d.2.length = k)
    {r : List (IL.Id × Value)} (hr : r ∈ iterRows dls none k) :
    PCtx B (iterΓ sigX Γ .list ds) (ρq.bindVals r) := by
  obtain ⟨m, hm⟩ := hd
  have hE := (expAt (utf8Env B) m).doms sigX tsigFixed Γ ctx0 ρq ds xvs hc.vt (hc.nc m).callH
    htd had hm
  simp only [iterRows, List.mem_map, List.mem_range] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact ⟨rowScope_list hc.vt hnd hE (by simp [counterΓ]) hl hlen hi,
    fun n => (hc.nc n).bindVals _⟩

/-! ## The forward transfer -/

theorem listIter_of_rule {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : grE x = true) (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) : ∀ pr ∈ prems, listIter pr = true := by
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 iterRels_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simpa [List.all_eq_true] using h'


section Fwd

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  {O₁ O' : ElseI} (hO : ∀ x args i v, O₁ x args i v → O' x (args.map eraseA) i (eraseV v))
include hB H hO

set_option maxRecDepth 20000

mutual
/-- **A derivation of a checked relation goes to the erased side.** -/
theorem dderivesB_fwd :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, grE x = true →
      DDerivesB (utf8Env B) O₁ x op args v →
      DDerivesB (utf8Env B) O' x op (args.map eraseA) (eraseV v)
  | x, _, args, v, hx, .rule (σ := σ) (ρ₀ := ρ₀) (qs := qs) (ps := ps) (prems := prems) (i := i)
      hrel hrule halt hps hq he hp => by
    have hr : reach 0 x = true := List.contains_iff_mem.2 (EraseAll.reach_of_grE hx)
    have hF := NxRule.rFacts hr hrel hrule
    have hXF := EraseAll.xFacts hx hrel hrule
    have hL := listIter_of_rule hx hrel hrule
    obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
    have hq' : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs := hρ ▸ hq
    have heq : ρ₀.bindVals (σ.map eraseP) = eraseScope (ρ₀.bindVals σ) := by
      rw [hρ, eraseScope_inst]
    have hD := NxFlow.flowSound B hB
    have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
        (qScope qs (VarEnv.empty.bindVals σ)) k :=
      fun k => NxClause.clauseErase B hB H _ k rfl rfl
    have hC : PCtx B (quantsΓ qs) (qScope qs (ρ₀.bindVals σ)) := by
      rw [hρ]
      exact ⟨NxRule.scopeVT_qScope (NxRule.typsNx_inst σ) hq' hF.wild,
        fun n => ⟨NxRule.callH_nil hD rfl rfl n, hCE n, fun p hp => by
          simp [qScope, VarEnv.bindVals, VarEnv.empty, Map.empty] at hp⟩⟩
    have hX := NxErase.ruleX_at hr hrel (List.mem_of_getElem? hrule)
    simp only [NxErase.ruleX, Bool.and_eq_true, List.all_eq_true] at hX
    have hps' : bindParams VarEnv.empty ps (args.map eraseA) = some ρ₀ := by
      rw [hargs]; rw [hargs] at hps; exact hps
    refine .rule (σ := σ.map eraseP) hrel hrule halt hps' ?_ ?_ fun pr hpr => ?_
    · rw [hρ, ← eraseScope_inst]
      exact NxTyp.typFwdN_utf8Env (List.contains_iff_mem.2 (EraseAll.reach_of_grE hx)) hrel hrule
        hq'
    · obtain ⟨n, hn⟩ := he
      refine ⟨n, ?_⟩
      rw [hρ] at hn
      rw [hρ, ← eraseScope_inst,
        NxErase.erase_alt hD H hr hrel hrule hq' hCE halt (hXF.alts _ halt) n, hn]
      rfl
    · rw [heq]
      obtain ⟨hpt, hpa, hpc⟩ := hF.premsOk pr hpr
      by_cases hif : ∃ c, pr = .ifPr c
      · obtain ⟨c, rfl⟩ := hif
        have hxc : xExp grE gdE c = true := by simpa [xPrem] using hXF.prems _ hpr
        cases hp _ hpr with
        | ifPr h =>
          rw [hρ] at h ⊢
          exact .ifPr (NxClause.ifPr_fwd hD H hr hrel hrule hq' hCE hpr hxc h)
      · have hbs : bindSite sigX (quantsΓ qs) pr = false := by
          cases pr with
          | ifPr c => exact absurd ⟨c, rfl⟩ hif
          | _ => rfl
        exact dpremB_fwd hC (NxRule.agreeOn_qScope hpc) hpt hpa (hX.2 pr hpr)
          (NxRule.badPr_zero hr hrel hrule hpr hbs) (hXF.prems pr hpr) (hL pr hpr)
          (hO _ _ _ _) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A premise without failing sites goes to the erased side**, read in a context. -/
theorem dpremB_fwd :
    ∀ {els els' : Prop} {Γ : List (String × AT)} {ρq ρ : VarEnv} {pr : Prem}, PCtx B Γ ρq →
      VarEnv.AgreeOn (freePrem pr) ρ ρq → premTy sigX tsigFixed Γ pr = true →
      premAuxR pr = true → premX ctx0 pr = true → badPr sigX Γ pr = 0 →
      xPrem grE gdE pr = true → listIter pr = true → (els → els') →
      DPremB (utf8Env B) O₁ els ρ pr → DPremB (utf8Env B) O' els' (eraseScope ρ) pr
  | _, _, _, _, _, .ifPr e, hc, hag, ht, ha, hX, hb, hx, _, _, .ifPr h => by
    simp only [premTy] at ht
    simp only [premAuxR] at ha
    simp only [premX] at hX
    simp only [badPr] at hb
    simp only [xPrem] at hx
    exact .ifPr (exp_fwd H hc hag ht ha hX hb hx h)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels h)
  | _, _, _, _, _, _, _, _, _, _, _, hb, _, _, _, .letPr _ _ => by
    simp only [badPr] at hb
    omega
  | _, _, _, _, _, .rulePr y args op e, hc, hag, ht, ha, hX, hb, hx, _, _, .rulePr hav hev hd => by
    simp only [premTy, ckRulePr, Bool.and_eq_true] at ht
    simp only [premAuxR, Bool.and_eq_true] at ha
    simp only [premX, Bool.and_eq_true] at hX
    simp only [badPr] at hb
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .rulePr
      (args_fwd H hc (hag.mono (EraseDer.sub_rule_args y args op e)) ht.1.1 ha.1.2 hX.1
        (by omega) hx.1.2 hav)
      (exp_fwd H hc (hag.mono (EraseDer.sub_rule_exp y args op e)) ht.1.2 ha.2 hX.2 (by omega)
        hx.2 hev)
      (dderivesB_fwd hx.1.1 hd)
  | _, _, _, _, _, .iterPr _ (.mk _ _), _, _, _, _, _, _, _, hl, _, .iterOptNone _ _ _ => by
    simp [listIter] at hl
  | _, _, _, _, _, .iterPr _ (.mk _ _), _, _, _, _, _, _, _, hl, _, .iterOptSome _ _ _ _ => by
    simp [listIter] at hl
  | _, _, _, _, _, .iterPr _ (.mk _ _), _, _, _, _, _, _, _, hl, _, .iterListN _ _ _ _ _ _ => by
    simp [listIter] at hl
  | _, _, Γ, ρq, ρ, .iterPr pr (.mk it ds), hc, hag, ht, ha, hX, hb, hx, hl, hels,
      .iterList (xvs := xvs) (dls := dls) (k := k) hit hd hne hdl hlen hp => by
    have hit' : it = .list := by
      cases it <;> simp_all [listIter]
    subst hit'
    simp only [listIter] at hl
    simp only [premTy, Bool.and_eq_true] at ht
    simp only [premAuxR, Bool.and_eq_true] at ha
    simp only [premX, Bool.and_eq_true] at hX
    simp only [badPr] at hb
    simp only [xPrem, Bool.and_eq_true] at hx
    have hagd := hag.mono (EraseDer.sub_iter_doms pr .list ds)
    have hd' := doms_fwd H hc hagd ht.2 ha.2 hX.2 (by omega) hx.2 hd
    have hdq : EvalDoms (utf8Env B) ρq ds xvs := by
      obtain ⟨n, hn⟩ := hd
      exact ⟨n, by rw [← evalDoms_agreeOn hagd]; exact hn⟩
    have hdl' : domLists (xvs.map eraseP) = some (dls.map fun p => (p.1, p.2.map eraseV)) := by
      rw [EraseDer.domLists_erase, hdl]; rfl
    refine .iterList (Or.inl rfl) hd' hne hdl' (EraseDer.lens_erase hlen) fun r' hr' => ?_
    rw [EraseAll.iterRows_erase] at hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    rw [← EraseAll.eraseScope_bindVals]
    have hkeys : r.map Prod.fst = ds.map domVar ++ ([] : List IL.Id) := by
      rw [EraseDer.map_fst_row hlen hr, EraseDer.map_fst_domLists hdl,
        EraseDer.map_fst_EvalDoms hd]
      rfl
    have hag' : VarEnv.AgreeOn (freePrem pr) (ρ.bindVals r) (ρq.bindVals r) :=
      EvalFree.agreeOn_body hag
        (EraseDer.bound_sub_rowSet hkeys (EraseDer.boundIter_plain (.inr (.inl rfl))))
        (EraseDer.sub_iter_body pr _)
    exact dpremB_fwd (pCtx_row hc ha.1.1.2 ht.2 ha.2 hdq hdl hlen hr) hag' ht.1.1 ha.1.1.1
      hX.1.1 (by omega) hx.1.1 hl hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd => hd
end

end Fwd

end Silmaril.Wasm.SpecTec.Sim.Round8.NxDer
