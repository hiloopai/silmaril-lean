module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Fwd
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Back

/-!
# R3 for a linked component as an exporter

`toExpData_bwdF`: the data `toExpData lg d Ii` meets R3 in its corrected form
(`RefData.BwdF`) when the exporter's data `d` meets R1, R3 (`BwdF`), R5 and R6. A host-free run
of the core activation of export `w` (the importer's core export, in any frame) is:

* still running (live), or
* locked down with an empty control chain after an `internal` trap (R3's third case, its
  implication vacuous), or otherwise read back by `phase_backT` (`Back`):
  * the importer returned values: the run passes through the return of its flat results to the
    caller's continuation (R3's middle case, `EndsT` a return: `HoldX` at the grown footprint,
    as in R2), the round a `SessRound` of the linked session;
  * the importer trapped, or the round ended trapped: R3's third case, `HoldX` at the starting
    store with the trapped core store (`lready_trapW`, R5), changes inside the footprint.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN checkLower)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {lg : LinkedG} {d : lg.exp.RefData P} {Ii : SInst}

/-- **R3 for a linked component**: `toExpData lg d Ii` meets `RefData.BwdF`, from R1, R3, R5 and
R6 of the exporter's data `d`. -/
theorem toExpData_bwdF (hFr : d.Frame) (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded) :
    (toExpData lg d Ii).BwdF := by
  intro pl st w vs x hx hvs S Fc hH σ prof impl M th K segs rest hMS hlock hth tr m' r hh
  subst hMS
  obtain ⟨hw, hty⟩ := toComp_exports_get hx
  let j : Fin lg.imp.exports.length := ⟨w, hw⟩
  have hxty : x.ty = lg.imp.exports[j].ty := hty
  have hvs' : ValTy.checkList lg.imp.exports[j].ty.params vs = true := hxty ▸ hvs
  obtain ⟨F₀, g, tr', F, ρc, Oc, ST, hR, hsub⟩ := hH.inv
  have SI := ST.imp
  have hxm : lg.imp.exports[j] ∈ lg.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := SI.good.core _ hxm
  have hk : lg.imp.exports[j].core < lg.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : lg.imp.mod.exports[lg.imp.exports[j].core] = (nm, lg.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs lg.imp.exports[j].ty.params vs).map (·.type) =
      lg.imp.mod.exports[lg.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs'
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI SI.inst hk hxs
  have hft' : Ii.exports.get f.1 = fnOf lg.imp.exports[j].ty.flat := by rw [hft, hflat]
  have hck : checkLower lg.imp.exports[j].ty.params vs =
      some (lowerArgs lg.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs', ↓reduceIte]
  have ha : (toExpData lg d Ii).addr pl w = pl.s₀.funcs.length + Ii.addr f.1 := by
    have ha₀ : Ii.addrs.getD lg.imp.exports[j].core 0 = Ii.addr f.1 := by
      rw [← hf₁]
      rfl
    show expAddr lg Ii pl.s₀ w = _
    unfold expAddr
    rw [List.getElem?_eq_getElem hw]
    exact congrArg (pl.s₀.funcs.length + ·) ha₀
  -- the start of the importer's core activation
  obtain ⟨hI₀, hT₀⟩ := linv_readyW hR hsub ST.own (f := f) hf₂
  have SIu : ImpStatG P lg.imp Ii st.1 F₀ g tr' := ⟨SI.good, SI.inst, hR.wfI, SI.tramp, SI.inv⟩
  have hFG₀ : FrameG d pl.ple pl.ii th M.store := ⟨hlock, hth, hH.imp, ST.out, hH.exp⟩
  have hstart : (toExpData lg d Ii).startCfg pl w x vs M th K segs rest =
      coreCfg M th K segs rest (M.core,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr f.1)
          (lowerArgs lg.imp.exports[j].ty.params vs)) := by
    show { M with ctl := _ } = _
    rw [ha, hxty]
    rfl
  rw [hstart] at r ⊢
  have r' : Machine.Steps prof (fun _ _ => false) (DI P impl) _ tr m' := r
  -- still running
  by_cases hlive : Live m'
  · exact .inl hlive
  -- locked down after an `internal` trap
  by_cases hint : m'.store.lockdown = true ∧ m'.ctl = [] ∧
      ∃ msg, Label.trap (.internal msg) ∈ tr
  · obtain ⟨h₁, h₂, msg, hm⟩ := hint
    exact .inr (.inr ⟨h₁, h₂, fun hn => absurd hm (hn msg)⟩)
  have hni : m'.store.lockdown = true → m'.ctl = [] →
      ∀ msg, Label.trap (.internal msg) ∉ tr :=
    fun h₁ h₂ msg hm => hint ⟨h₁, h₂, msg, hm⟩
  obtain ⟨rs, dss, s₁, x', hrel, hexp, hend⟩ := phase_backT (prof := prof) (impl := impl) SIu
    ST.wire hFr hBw hB th K segs rest tr.length M st.2 F _ _ tr m' le_rfl hI₀ hT₀ hFG₀ r' hh
    hlive hni
  have hok : ∀ w' : Ii.F.Ar f, (⟨j, vs, f, rs, w', dss⟩ : LinkedG.SessRound lg Ii).Ok :=
    fun _ => ⟨_, hck, hf₁, hf₂, hrel⟩
  -- a trapped end, from the parts at the trapped core store
  have htrap : ∀ (w' : Ii.F.Ar f) (c : (E3 P).Store (CanonHost (E3 P))),
      Ii.Path P (.idle st.1) (LinkedG.SessRound.instMoves ⟨j, vs, f, rs, w', dss⟩) (.idle x'.1) →
      (LinkedG.SessRound.ans ⟨j, vs, f, rs, w', dss⟩ : Option Payload) = none →
      TrapAtG d pl.ple Ii pl.s₀ st.1 F₀ g pl.Oc₀ f M.store s₁ c x'.1 →
      TrapT d pl.ple pl.s₀ g pl.Oc₀ Fc M.core M.store s₁ c x'.1 →
      ∃ (s' : (lg.toExp Ii).St) (S' : RefStore (core3P P)) (F' : CoreFoot),
        (lg.toExp Ii).Step P st ⟨(w, .vals vs), none⟩ s' ∧ S'.core = c ∧
        S'.funcs = M.store.funcs ∧ (toExpData lg d Ii).Hold pl s' S' F' ∧
        Fc.Within (M.core : Store (CanonHost (core3P P))) c ∧
        Fc.Grows F' (M.core : Store (CanonHost (core3P P))) := by
    intro w' c hP hans hTA hTT
    obtain ⟨F', ρ', O', hR', hW', hU'⟩ := lready_trapW hRes hR.toG hTA hTT
    refine ⟨(x'.1, s₁), { M.ref with core := c }, growFoot Fc M.core c,
      ⟨⟨j, vs, f, rs, w', dss⟩, hok w', hP, hexp, ?_⟩, rfl, rfl,
      holdX_grow hH.bound ST hR' hW' hU' hH.imp hH.exp, hW', grows_growFoot _ _ _⟩
    unfold LinkedG.SessRound.toU
    rw [hans]
  rcases hend with ⟨tr₁, tr₂, C', S'', F', yc, l, m₁, etr, r₁, hnco, hx', r₂, hIc, hTc, hFGc,
      hXc, hpath⟩ | ⟨hlk, hct, hTA, hTT, hpath⟩
  · -- the importer's core activation exited
    have hS₀ : S''.funcs = M.store.funcs := callExt_funcs hXc
    obtain ⟨ρ₁, O₁, hL, -⟩ := hIc.rel
    obtain ⟨ts, hst', htt⟩ := linvG_typed SIu hIc
    rcases hx' with ⟨zs, hst, rfl, rfl⟩ | ⟨hst, rfl, rfl⟩ | ⟨h', ys', hc'⟩
    · -- the importer returned values: the middle case
      obtain ⟨cvs, hcode, hm⟩ := status_values hst
      have hc : (yc.2.config (Store.mapH g yc.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
        (config_code_mapH g yc.1 yc.2).trans hcode
      obtain ⟨vs', hv, hvm⟩ := values_back P hL hst' htt hc
      have hm' : (vs'.map (linkMap pl.s₀ ρ₁).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
          some zs := by
        rw [hvm]
        exact hm
      have hvs'' : vs' = cvs := (map_val_of_mapM _ hm').symm.trans hvm
      have hr : Silmaril.Wasm.Game.ResultAt x'.1 x'.2 (.values cvs) := hvs'' ▸ hv
      obtain ⟨w', hw', -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run SIu.wf
        (valEnv_throwsBelow Ii _) hIc.run hr
      have hP : Ii.Path P (.idle st.1)
          (LinkedG.SessRound.instMoves ⟨j, vs, f, rs, w', dss⟩) (.idle x'.1) :=
        .cons (.call st.1 f) (hpath [.inr (.ans f w')] (.idle x'.1)
          (fun _ _ hr' => .cons (.oret hr' hr hw') (.nil _)))
      have hzty : zs.map (·.type) = ValTy.flatList lg.imp.exports[j].ty.results :=
        results_typed hft' hw' hm
      have hR' : (LinkedG.SessRound.ans ⟨j, vs, f, rs, w', dss⟩ : Option Payload) =
          (liftArgs lg.imp.exports[j].ty.results zs).map .vals :=
        lifted_answer hw' hm
      have s₃ : Step prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest yc) .tau
          (retCfg { M with conts := C', store := S''.toCStore } th K segs rest yc zs) :=
        Step.coreReturned rfl hst
      have hret : retCfg { M with conts := C', store := S''.toCStore } th K segs rest yc zs =
          ExpSpec.RefData.retCfg' M S'' C' th K segs rest zs := by
        unfold retCfg
        rw [← hIc.core]
        rfl
      rw [hret] at s₃ r₂
      have hrun₃ : Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg M th K segs rest (M.core,
            Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr f.1)
              (lowerArgs lg.imp.exports[j].ty.params vs))) (tr₁ ++ [.tau])
          (ExpSpec.RefData.retCfg' M S'' C' th K segs rest zs) :=
        Adequacy.steps_append (hr := (linkHost impl).hr) (dispatch := (linkHost impl).dispatch)
          r₁ (.cons s₃ (.refl _))
      obtain ⟨ρ₂, O₂, hR₂, hW₂, hU₂⟩ := lready_afterW hR.toG hIc hTc
      have hout := ST.out
      have hii : S''.insts[pl.ii]? = M.store.insts[pl.ii]? := hXc.insts_out pl.ii hout
      have hH₂ : HoldX lg d Ii pl (x'.1, s₁) S'' (growFoot Fc M.core S''.core) := by
        refine holdX_grow hH.bound (hS₀ ▸ ST) hR₂ hW₂ hU₂ ?_ hFGc.exp
        rw [hii]
        exact hH.imp
      have hext : (toExpData lg d Ii).StoreExt pl M.ref S'' :=
        ⟨hXc.eq, hXc.insts_len, fun i hi => hXc.insts_out i (fun h => hi (.inl h)), fun _ => hii,
          hXc.subtasks, hXc.callers, hXc.tasks, hXc.threads⟩
      have hlS'' : S''.lockdown = false := hFGc.lock
      refine .inr (.inl ⟨tr₁ ++ [.tau], tr₂, _,
        (LinkedG.SessRound.ans ⟨j, vs, f, rs, w', dss⟩ : Option Payload), (x'.1, s₁),
        by rw [etr]; simp, hrun₃, r₂, ⟨⟨j, vs, f, rs, w', dss⟩, hok w', hP, hexp, rfl⟩,
        ⟨.inl ⟨S'', C', zs, growFoot Fc M.core S''.core, rfl, hxty ▸ hzty, ?_, hext, hH₂,
          hW₂, grows_growFoot _ _ _⟩, fun h => absurd (h.symm.trans hlS'') (by decide)⟩,
        List.cons_ne_nil _ _⟩)
      rw [hR', hxty]
      cases liftArgs lg.imp.exports[j].ty.results zs <;> rfl
    · -- the importer's core activation trapped
      have e₂ := steps_of_locked rfl rfl r₂
      subst e₂
      have hr : Silmaril.Wasm.Game.ResultAt x'.1 x'.2 .trap := by
        rcases status_trap hst with hc | ⟨a, hc⟩
        · exact trap_back P hL hst' htt ((config_code_mapH g yc.1 yc.2).trans hc)
        · exact (throwing_back P hL hst' htt ((config_code_mapH g yc.1 yc.2).trans hc)).elim
      obtain ⟨w', hw', -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run SIu.wf
        (valEnv_throwsBelow Ii _) hIc.run hr
      obtain ⟨s', S', F'', hs', hc', hf', hH', hW', hG'⟩ := htrap w' yc.1
        (.cons (.call st.1 f) (hpath [.inr (.ans f w')] (.idle x'.1)
          (fun _ _ hr' => .cons (.oret hr' hr hw') (.nil _))))
        (lifted_trap (x := lg.imp.exports[j]) (fun _ h => by cases h) hw')
        (trapAt_of_linv hIc hS₀) (trapT_of_linv hIc hTc hS₀)
      exact .inr (.inr ⟨rfl, rfl, fun _ => ⟨s', S', F'', hs', hc', hf', hH', hW', hG'⟩⟩)
    · exact absurd hc' (hnco h' ys')
  · -- a trapped end of the round
    obtain ⟨s', S', F'', hs', hc', hf', hH', hW', hG'⟩ := htrap .trap m'.core
      (.cons (.call st.1 f) hpath) rfl hTA hTT
    exact .inr (.inr ⟨hlk, hct, fun _ => ⟨s', S', F'', hs', hc', hf', hH', hW', hG'⟩⟩)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
