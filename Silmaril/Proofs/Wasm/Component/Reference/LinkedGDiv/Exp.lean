module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.CallBack
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Exp

/-!
# R7 for a linked component as an exporter

`toExpData_div`: the data `toExpData lg d Ii` of `LinkedGChain` meets R7 (`RefData.Div`) when the
exporter's data `d` meets R1, R2, R6 and R7, the divergence specification of `lg.toExp Ii` being
the linked `LinkedG.RoundDiv`. From `HoldX` the importer's core activation of export `j` starts
with `LInvG` and the tracked footprint (`linv_readyW`), in any frame:

* **forward**: a `RoundDiv` is the round's prefix (`roundsPre_fwdB`) and one of the three
  sources (`divB_coreG`, `divA_coreG`, `chatter_coreG`), the same as at a top-level call;
* **backward**: `ldiv_classifyG` from the start, with the footprint tracked; sources (i)-(iii)
  are a `RoundDiv` (the round's prefix the chain of served calls); in case (iv) the importer's
  activation exits after the chain: a trap does not diverge (`trapCfg`), a callout is excluded,
  and a return of values is R2's return (`EndsT`, as in `toExpData_bwdF`: `HoldX` at the grown
  footprint), the round a `SessRound`, from which the machine diverges.

`toExp_refAdeqUXD`: with `toExp_refAdeqUX`, a linked component meets `RefAdeqUXD`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
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

/-- **R7 for a linked component**: `toExpData lg d Ii` meets `RefData.Div`, from R1, R2, R6 and
R7 of the exporter's data `d`. -/
theorem toExpData_div (hFr : d.Frame) (hFw : d.Fwd) (hB : d.Bounded) (hDv : d.Div) :
    (toExpData lg d Ii).Div := by
  intro pl st w vs x hx hvs S Fc hH σ prof impl M th K segs rest hMS hlock hth
  subst hMS
  obtain ⟨hw, hty⟩ := toComp_exports_get hx
  obtain ⟨j, rfl⟩ : ∃ j : Fin lg.imp.exports.length, j.val = w := ⟨⟨w, hw⟩, rfl⟩
  have hxty : x.ty = lg.imp.exports[j].ty := hty
  have hvs' : ValTy.checkList lg.imp.exports[j].ty.params vs = true := hxty ▸ hvs
  obtain ⟨F₀, g, tr', F, ρc, Oc, ST, hR, hsub⟩ := hH.inv
  have SI := ST.imp
  have hxm : lg.imp.exports[j] ∈ lg.imp.exports := List.getElem_mem j.isLt
  have hck : checkLower lg.imp.exports[j].ty.params vs =
      some (lowerArgs lg.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs', ↓reduceIte]
  have SIu : ImpStatG P lg.imp Ii st.1 F₀ g tr' := ⟨SI.good, SI.inst, hR.wfI, SI.tramp, SI.inv⟩
  have hFG₀ : FrameG d pl.ple pl.ii th M.store := ⟨hlock, hth, hH.imp, ST.out, hH.exp⟩
  -- the start of the importer's core activation, for a core question `f` of export `j`
  have hstart : ∀ f : Ii.F.Op, f.1.val = lg.imp.exports[j].core →
      (toExpData lg d Ii).startCfg pl j.val x vs M th K segs rest =
        coreCfg M th K segs rest (M.core,
          Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr f.1)
            (lowerArgs lg.imp.exports[j].ty.params vs)) := by
    intro f hf₁
    have ha : (toExpData lg d Ii).addr pl j.val = pl.s₀.funcs.length + Ii.addr f.1 := by
      have ha₀ : Ii.addrs.getD lg.imp.exports[j].core 0 = Ii.addr f.1 := by
        rw [← hf₁]
        rfl
      show expAddr lg Ii pl.s₀ j.val = _
      unfold expAddr
      rw [List.getElem?_eq_getElem j.isLt]
      exact congrArg (pl.s₀.funcs.length + ·) ha₀
    show { M with ctl := _ } = _
    rw [ha, hxty]
    rfl
  constructor
  · -- forward: a round that never answers diverges
    rintro ⟨j', vs', hq, hd⟩
    obtain ⟨hj, hv⟩ := Prod.mk.inj hq
    cases Payload.vals.inj hv
    obtain rfl : j' = j := Fin.ext hj.symm
    obtain ⟨⟨dj, dvs, df, dcs, ddss⟩, sB, tB, π₁, hdj, hdv, hok, hpath, hexp, hsrc⟩ := hd
    dsimp only at hdj hdv
    subst hdj hdv
    obtain ⟨xs, hckl, hf₁, hf₂, hrel⟩ := hok
    dsimp only at hckl hf₁ hf₂ hrel
    rw [hck] at hckl
    cases Option.some.inj hckl
    obtain ⟨hI₀, -⟩ := linv_readyW hR hsub ST.own (f := df) hf₂
    rw [hstart df hf₁]
    have hpath' : Ii.Path P (.running df st.1 (Ii.initThread df)) (callMoves dcs)
        (.running df sB tB) := by
      have h : Ii.Path P (.idle st.1) (.inr (.ask df) :: callMoves dcs) (.running df sB tB) :=
        hpath
      cases h with
      | cons h₁ h₂ =>
        cases h₁
        exact h₂
    rcases roundsPre_fwdB (prof := prof) (impl := impl) SIu ST.wire hFr hFw hB th K segs rest
        dcs ddss M st.2 π₁ F _ _ sB tB hI₀ hFG₀ hrel hexp hpath' with
      ⟨trc, C', S'', F', yc, hrun, hnh, -, hIc, hFG'⟩ | hdm
    · refine steps_diverges hrun hnh ?_
      let M₁ : Machine.Config (E3 P) σ :=
        { M with conts := C', store := S''.toCStore, core := S''.core }
      show Machine.Diverges prof (fun _ _ => false) (DI P impl) (coreCfg M₁ th K segs rest yc)
      rcases hsrc with h | h | h
      · exact divB_coreG (M := M₁) SIu hIc h th K segs rest
      · exact divA_coreG (M := M₁) SIu ST.wire hFr hDv hIc th hFG' h K segs rest
      · exact chatter_coreG (M := M₁) SIu ST.wire hFr hFw hB hIc th hFG' h K segs rest
    · exfalso
      rcases hsrc with h | ⟨e, s', t', nm, ft, ws, w', h, _⟩ | ⟨q, c, ds, st', hq0, _, hc⟩
      · exact not_divB_doomed hdm h
      · exact doomed_no_ask hdm h
      · have h₀ := (hc 0).1
        rw [hq0] at h₀
        exact doomed_no_call hdm h₀
  · -- backward: classify the divergence
    intro hd
    obtain ⟨nm, hcore⟩ := SI.good.core _ hxm
    have hk : lg.imp.exports[j].core < lg.imp.mod.exports.length :=
      (List.getElem?_eq_some_iff.mp hcore).1
    have hflat : lg.imp.mod.exports[lg.imp.exports[j].core] =
        (nm, lg.imp.exports[j].ty.flat) := (List.getElem?_eq_some_iff.mp hcore).2
    have hxs : (lowerArgs lg.imp.exports[j].ty.params vs).map (·.type) =
        lg.imp.mod.exports[lg.imp.exports[j].core].2.params := by
      rw [hflat]
      exact lowerList_types _ _ hvs'
    obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI SI.inst hk hxs
    have hft' : Ii.exports.get f.1 = fnOf lg.imp.exports[j].ty.flat := by rw [hft, hflat]
    obtain ⟨hI₀, hT₀⟩ := linv_readyW hR hsub ST.own (f := f) hf₂
    rw [hstart f hf₁] at hd ⊢
    let z₀ : DStG P σ lg.exp := ⟨M.conts, M.ref, F, (M.core,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr f.1)
          (lowerArgs lg.imp.exports[j].ty.params vs)), (st.1, Ii.initThread f), st.2⟩
    have hz₀ : DInvG prof impl d pl.ple pl.ii Ii pl.s₀ st.1 F₀ g pl.Oc₀ f th K segs rest M Fc
        M.core z₀ :=
      ⟨hd, hI₀, hFG₀, callExt_refl _, hT₀⟩
    obtain ⟨cs, dss, z, trc, hpath, hrel, hexp, hz, hrun, hnh, hsrc⟩ :=
      ldiv_classifyG SIu ST.wire hFr hDv hB hz₀
    have hround : ∀ (src : Linked2.DivB P z.x.1 z.x.2 ∨ LinkedG.DivA P lg Ii f z.x.1 z.x.2 z.s ∨
        LinkedG.Chatter P lg Ii f z.x.1 z.x.2 z.s), (lg.toExp Ii).DivStep P st (j.val, .vals vs) :=
      fun src => ⟨j, vs, rfl, ⟨j, vs, f, cs, dss⟩, z.x.1, z.x.2, z.s, rfl, rfl,
        ⟨_, hck, hf₁, hf₂, hrel⟩, .cons (.call st.1 f) hpath, hexp, src⟩
    rcases hsrc with h | h | h | hX
    · exact .inl (hround (.inl h))
    · exact .inl (hround (.inr (.inl h)))
    · exact .inl (hround (.inr (.inr h)))
    -- (iv) the importer's activation exits after the chain of served calls
    right
    obtain ⟨y₁, x₁, lb, m₁, hy, hr₁, hIc, hTc, hnco, hx, d₁⟩ := hX
    have hXc : CallExt d pl.ple M.ref { z.S with core := y₁.1 } :=
      callExt_trans hz.ext (callExt_refl _)
    have hFGc : FrameG d pl.ple pl.ii th ({ z.S with core := y₁.1 } : RefStore (E3 P)).toCStore :=
      hz.frame
    have hS₀ : ({ z.S with core := y₁.1 } : RefStore (E3 P)).funcs = M.store.funcs :=
      callExt_funcs hXc
    obtain ⟨ρ₁, O₁, hL, -⟩ := hIc.rel
    obtain ⟨ts, hst', htt⟩ := linvG_typed SIu hIc
    rcases hx with ⟨zs, hst, rfl, rfl⟩ | ⟨-, -, rfl⟩ | ⟨h', ys', hc'⟩
    · -- the importer returned values: R2's return
      obtain ⟨cvs, hcode, hm⟩ := status_values hst
      have hc : (y₁.2.config (Store.mapH g y₁.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
        (config_code_mapH g y₁.1 y₁.2).trans hcode
      obtain ⟨vs', hv, hvm⟩ := values_back P hL hst' htt hc
      have hm' : (vs'.map (linkMap pl.s₀ ρ₁).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
          some zs := by
        rw [hvm]
        exact hm
      have hvs'' : vs' = cvs := (map_val_of_mapM _ hm').symm.trans hvm
      have hres : Silmaril.Wasm.Game.ResultAt x₁.1 x₁.2 (.values cvs) := hvs'' ▸ hv
      obtain ⟨w', hw', -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run SIu.wf
        (valEnv_throwsBelow Ii _) hIc.run hres
      have hP : Ii.Path P (.idle st.1)
          (LinkedG.SessRound.instMoves ⟨j, vs, f, cs, w', dss⟩) (.idle x₁.1) :=
        .cons (.call st.1 f) (path_append hpath (.cons (.oret hr₁ hres hw') (.nil _)))
      have hzty : zs.map (·.type) = ValTy.flatList lg.imp.exports[j].ty.results :=
        results_typed hft' hw' hm
      have hR' : (LinkedG.SessRound.ans ⟨j, vs, f, cs, w', dss⟩ : Option Payload) =
          (liftArgs lg.imp.exports[j].ty.results zs).map .vals :=
        lifted_answer hw' hm
      obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof)
        (hr := (linkHost impl).hr) (dispatch := (linkHost impl).dispatch)
        (B := { M with conts := z.C, store := z.S.toCStore, core := z.S.core }) (th := th) (K := K) (segs := segs)
        (rest := rest) hy
      have s₃ : Step prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg { M with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest y₁) .tau
          (retCfg { M with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest y₁ zs) :=
        Step.coreReturned rfl hst
      have hret : retCfg { M with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest y₁ zs =
          ExpSpec.RefData.retCfg' M { z.S with core := y₁.1 } z.C th K segs rest zs := rfl
      rw [hret] at s₃ d₁
      have hrun₃ : Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg M th K segs rest (M.core,
            Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr f.1)
              (lowerArgs lg.imp.exports[j].ty.params vs))) (trc ++ (tr₀ ++ [.tau]))
          (ExpSpec.RefData.retCfg' M { z.S with core := y₁.1 } z.C th K segs rest zs) :=
        Adequacy.steps_append (hr := (linkHost impl).hr) (dispatch := (linkHost impl).dispatch)
          hrun (Adequacy.steps_append r₀ (.cons s₃ (.refl _)))
      obtain ⟨ρ₂, O₂, hR₂, hW₂, hU₂⟩ := lready_afterW hR.toG hIc hTc
      have hout := ST.out
      have hii : ({ z.S with core := y₁.1 } : RefStore (E3 P)).insts[pl.ii]? =
          M.store.insts[pl.ii]? := hXc.insts_out pl.ii hout
      have hH₂ : HoldX lg d Ii pl (x₁.1, z.s) { z.S with core := y₁.1 }
          (growFoot Fc M.core y₁.1) := by
        refine holdX_grow hH.bound (hS₀ ▸ ST) hR₂ hW₂ hU₂ ?_ hFGc.exp
        rw [hii]
        exact hH.imp
      have hext : (toExpData lg d Ii).StoreExt pl M.ref { z.S with core := y₁.1 } :=
        ⟨hXc.eq, hXc.insts_len, fun i hi => hXc.insts_out i (fun h => hi (.inl h)), fun _ => hii,
          hXc.subtasks, hXc.callers, hXc.tasks, hXc.threads⟩
      have hlS'' : ({ z.S with core := y₁.1 } : RefStore (E3 P)).lockdown = false := hFGc.lock
      refine ⟨trc ++ (tr₀ ++ [.tau]), _,
        (LinkedG.SessRound.ans ⟨j, vs, f, cs, w', dss⟩ : Option Payload), (x₁.1, z.s),
        hrun₃, ?_, ⟨⟨j, vs, f, cs, w', dss⟩, ⟨_, hck, hf₁, hf₂, hrel⟩, hP, hexp, rfl⟩,
        ⟨.inl ⟨{ z.S with core := y₁.1 }, z.C, zs, growFoot Fc M.core y₁.1, rfl,
          hxty ▸ hzty, ?_, hext, hH₂, hW₂, grows_growFoot _ _ _⟩,
          fun h => absurd (h.symm.trans hlS'') (by decide)⟩, List.cons_ne_nil _ _, d₁⟩
      · intro ev hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hnh ev hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact (Quiet.of_core htr₀).1 ev hm
          · simp at hm
      · rw [hR', hxty]
        cases liftArgs lg.imp.exports[j].ty.results zs <;> rfl
    · exact absurd d₁ (not_diverges_trapCfg _)
    · exact absurd hc' (hnco h' ys')

/-- **A linked component is a reference exporter with divergence**: for an exporter meeting
`RefAdeqUXD` and a link meeting `LinkOk`, `lg.toExp Ii` meets `RefAdeqUXD`, with the data
`toExpData lg d Ii`. -/
theorem toExp_refAdeqUXD (P : Profile) (lg : LinkedG) (Ii : SInst) (he : lg.exp.RefAdeqUXD P)
    (hl : lg.LinkOk) (hI : lg.imp.mod.IsInst Ii) : (lg.toExp Ii).RefAdeqUXD P :=
  let ⟨d, hFr, hFw, hBw, hInit, hRes, hB, hDv⟩ := he
  ⟨toExpData lg d Ii, toExpData_frame hFr, toExpData_fwd hFr hFw hRes hB,
    toExpData_bwdF hFr hBw hRes hB, toExpData_initUX hInit hFr hB hl hI, toExpData_resume hRes,
    toExpData_bounded, toExpData_div hFr hFw hB hDv⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv
