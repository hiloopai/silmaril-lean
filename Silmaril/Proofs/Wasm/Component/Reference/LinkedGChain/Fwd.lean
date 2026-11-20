module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Data

/-!
# R2 for a linked component as an exporter

`toExpData_fwd`: the data `toExpData lg d Ii` of `Data` meets R2 (`RefData.Fwd`) when the
exporter's data `d` meets R1, R2, R5 and R6. A step of `lg.toExp Ii` is a round of the linked
session (`SessRound`); from `HoldX`, the core activation of export `w` (the importer's core
export, on the lowered arguments, in **any** frame) is the importer's export call
(`linv_readyW`), the round tracked (`rounds_fwdT` of `Track`) and its end:

* the importer returns values: one machine step returns its flat results to the caller's
  continuation; the results lift to the round's answer or not (`lifted_answer`); the store is a
  `CallExt` of the start (so a `StoreExt` of the linked component's block), and `HoldX` holds
  again at the grown footprint `growFoot Fc S.core S'.core` (`holdX_grow`);
* the importer traps, or the round ends trapped: a trapped configuration, `HoldX` at the
  starting store with the trapped core store (`lready_trapW`, R5).

The footprint grows by the addresses allocated during the call (`growFoot`); the tracked round
shows that the combined footprints along it lie under the starting footprint and the fresh
addresses, and that nothing else changed (`Within`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
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

/-! ## The grown footprint -/

section Grow

variable {H : Type}

/-- `Fc` with the structs and arrays allocated between `σ₀` and `σ'`. -/
def growFoot (Fc : CoreFoot) (σ₀ σ' : Store H) : CoreFoot :=
  ⟨Fc.gl, fun a => Fc.st a ∨ (σ₀.structs.length ≤ a ∧ a < σ'.structs.length),
    fun a => Fc.ar a ∨ (σ₀.arrays.length ≤ a ∧ a < σ'.arrays.length)⟩

theorem grows_growFoot (Fc : CoreFoot) (σ₀ σ' : Store H) : Fc.Grows (growFoot Fc σ₀ σ') σ₀ where
  gl _ := Iff.rfl
  st _ h := .inl h
  ar _ h := .inl h
  stNew _ h := h.imp_right fun h => h.1
  arNew _ h := h.imp_right fun h => h.1

theorem growFoot_bounded {Fc : CoreFoot} {σ₀ σ' : Store H} (hB : Fc.Bounded σ₀)
    (hs : σ₀.structs.length ≤ σ'.structs.length) (ha : σ₀.arrays.length ≤ σ'.arrays.length) :
    (growFoot Fc σ₀ σ').Bounded σ' where
  st a h := h.elim (fun h => lt_of_lt_of_le (hB.st a h) hs) fun h => h.2
  ar a h := h.elim (fun h => lt_of_lt_of_le (hB.ar a h) ha) fun h => h.2

theorem sub_growFoot {Fc G : CoreFoot} {σ₀ σ' : Store H} (hU : Under Fc σ₀ G)
    (hB : G.Bounded σ') : SubFoot G (growFoot Fc σ₀ σ') where
  gl a h := hU.gl a h
  st a h := (hU.st a h).imp_right fun h' => ⟨h', hB.st a h⟩
  ar a h := (hU.ar a h).imp_right fun h' => ⟨h', hB.ar a h⟩

theorem real_bounded {F : CoreFoot} {ρc : Ren} {Oc : Own} {p : Store Nat} {g : H → Nat}
    {σ : Store H} (hD : FootDisj F ρc Oc σ) (hR : PartRel ρc Oc p (Store.mapH g σ)) :
    (footUnion F (img ρc Oc)).Bounded σ where
  st a h := h.elim (hD.bound.st a) fun ⟨_, hb, e⟩ => e ▸ (hR.st_lt hb).2
  ar a h := h.elim (hD.bound.ar a) fun ⟨_, hb, e⟩ => e ▸ (hR.ar_lt hb).2

end Grow

variable {P : Profile} {lg : LinkedG} {d : lg.exp.RefData P} {Ii : SInst}

/-- **`HoldX` at the grown footprint**: the static facts at the functions of the start, the
invariant between calls at a witness whose combined footprint lies under `Fc` at `σ₀`, the
importer's instance and the export instances. -/
theorem holdX_grow {pl : ExpPl lg d} {st : Store Nat × lg.exp.St} {S' : RefStore (E3 P)}
    {Fc : CoreFoot} {σ₀ : Store (CanonHost (E3 P))} (hB : Fc.Bounded σ₀)
    {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
    {tr : Nat → CanonHost (E3 P)}
    (hS : StatB P lg d pl.ple pl.ii Ii pl.s₀ pl.ui F₀ g tr pl.Oc₀ S'.funcs (fun j => pl.fb + j))
    {F : CoreFoot} {ρc : Ren} {Oc : Own}
    (hR : LReadyW d pl.ple Ii pl.s₀ pl.ui F₀ g pl.Oc₀ S' st.2 st.1 F ρc Oc)
    (hW : Fc.Within σ₀ S'.core) (hU : Under Fc σ₀ (footUnion F (img ρc Oc)))
    (himp : ∃ ι : InstState, S'.insts[pl.ii]? = some ι ∧ ι.mayLeave = true)
    (hexp : ∀ w : Nat, (∃ xe, lg.exp.comp.exports[w]? = some xe) →
      ∃ ι : InstState, S'.insts[d.inst pl.ple w]? = some ι ∧ ThreadsOk ι) :
    HoldX lg d Ii pl st S' (growFoot Fc σ₀ S'.core) :=
  ⟨⟨F₀, g, tr, F, ρc, Oc, hS, hR, sub_growFoot hU (real_bounded hR.disj hR.rel)⟩,
    growFoot_bounded hB hW.structs_len hW.arrays_len, himp, hexp⟩

theorem noHI_cons_tau {σ : Type} {tr : List (Label (E3 P) σ)} (h : NoHI tr) :
    NoHI (tr ++ [.tau]) :=
  h.append ⟨fun _ hm => by simp at hm, fun _ hm => by simp at hm⟩

/-- **R2 for a linked component**: `toExpData lg d Ii` meets `RefData.Fwd`, from R1, R2, R5 and
R6 of the exporter's data `d`. -/
theorem toExpData_fwd (hFr : d.Frame) (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded) :
    (toExpData lg d Ii).Fwd := by
  intro pl st st' w vs R x hstep hx S Fc hH σ prof impl M th K segs rest hMS hlock hth
  obtain ⟨dr, hok, hpath, hexp, heq⟩ := hstep
  simp only [LinkedG.SessRound.toU, Sigma.mk.injEq, Prod.mk.injEq, Payload.vals.injEq,
    heq_eq_eq] at heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
  obtain ⟨hw, hty⟩ := toComp_exports_get hx
  subst hMS
  obtain ⟨F₀, g, tr, F, ρc, Oc, ST, hR, hsub⟩ := hH.inv
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList lg.imp.exports[dr.j].ty.params dr.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs lg.imp.exports[dr.j].ty.params dr.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have SI := ST.imp
  have hxm : lg.imp.exports[dr.j] ∈ lg.imp.exports := List.getElem_mem dr.j.isLt
  obtain ⟨nm, hcore⟩ := SI.good.core _ hxm
  have hflat : lg.imp.mod.exports[lg.imp.exports[dr.j].core]? =
      some (nm, lg.imp.exports[dr.j].ty.flat) := hcore
  have hft' : Ii.exports.get dr.f.1 = fnOf lg.imp.exports[dr.j].ty.flat := by
    have hlt : dr.f.1.val < lg.imp.mod.exports.length := by
      rw [hf₁]
      exact (List.getElem?_eq_some_iff.mp hflat).1
    have e₁ : Ii.exports.get dr.f.1 = fnOf (lg.imp.mod.exports[dr.f.1.val]'hlt).2 := by
      simp only [List.get_eq_getElem, SI.inst.2.2, List.getElem_map]
    rw [e₁]
    have e₂ : lg.imp.mod.exports[dr.f.1.val]'hlt = (nm, lg.imp.exports[dr.j].ty.flat) := by
      have := (List.getElem?_eq_some_iff.mp hflat).2
      simp only [← hf₁] at this
      exact this
    rw [e₂]
  have ha : (toExpData lg d Ii).addr pl dr.j.val = pl.s₀.funcs.length + Ii.addr dr.f.1 := by
    have ha₀ : Ii.addrs.getD lg.imp.exports[dr.j].core 0 = Ii.addr dr.f.1 := by
      rw [← hf₁]
      rfl
    show expAddr lg Ii pl.s₀ dr.j.val = _
    unfold expAddr
    rw [List.getElem?_eq_getElem dr.j.isLt]
    exact congrArg (pl.s₀.funcs.length + ·) ha₀
  have hxty : x.ty = lg.imp.exports[dr.j].ty := hty
  -- the start of the importer's core activation
  have hO := ST.own
  obtain ⟨hI₀, hT₀⟩ := linv_readyW hR hsub hO (f := dr.f) hf₂
  have SIu : ImpStatG P lg.imp Ii st.1 F₀ g tr := ⟨SI.good, SI.inst, hR.wfI, SI.tramp, SI.inv⟩
  have hFG₀ : FrameG d pl.ple pl.ii th M.store := ⟨hlock, hth, hH.imp, ST.out, hH.exp⟩
  have hpath' : Ii.Path P (.running dr.f st.1 (Ii.initThread dr.f))
      (callMoves dr.cs ++ [.inr (.ans dr.f dr.w)]) (.idle st'.1) := by
    have h : Ii.Path P (.idle st.1) (.inr (.ask dr.f) :: (callMoves dr.cs ++
        [.inr (.ans dr.f dr.w)])) (.idle st'.1) := hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  have hstart : (toExpData lg d Ii).startCfg pl dr.j.val x dr.vs M th K segs rest =
      coreCfg M th K segs rest (M.core,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr dr.f.1)
          (lowerArgs lg.imp.exports[dr.j].ty.params dr.vs)) := by
    show { M with ctl := _ } = _
    rw [ha, hxty]
    rfl
  rw [hstart]
  have hround := rounds_fwdT (prof := prof) (impl := impl) SIu ST.wire hFr hFw hB th K segs rest
    dr.cs dr.dss M st.2 st'.2 F _ _ st'.1 hI₀ hT₀ hFG₀ hrel hexp hpath'
  -- a trapped end
  have hfr : ∀ c, TrapEnd prof P impl (coreCfg M th K segs rest (M.core,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr dr.f.1)
          (lowerArgs lg.imp.exports[dr.j].ty.params dr.vs))) c →
      TrapAtG d pl.ple Ii pl.s₀ st.1 F₀ g pl.Oc₀ dr.f M.store st'.2 c st'.1 →
      TrapT d pl.ple pl.s₀ g pl.Oc₀ Fc M.core M.store st'.2 c st'.1 → dr.ans = none →
      ∃ (tr' : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ),
        Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg M th K segs rest (M.core,
            Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr dr.f.1)
              (lowerArgs lg.imp.exports[dr.j].ty.params dr.vs))) tr' m ∧
        (∀ ev, Label.host ev ∉ tr') ∧ (∀ msg, Label.trap (.internal msg) ∉ tr') ∧
        (toExpData lg d Ii).Ends pl x M.ref Fc M th K segs rest dr.ans st' m := by
    intro c hT hTA hTT hn
    obtain ⟨tr', m', hrun, hh, hi, hl, hc⟩ := hT
    obtain ⟨F', ρc', Oc', hR', hW', hU'⟩ := lready_trapW hRes hR.toG hTA hTT
    refine ⟨tr', m', hrun, hh, hi, .inr ⟨hn, hl, { M.store with core := c },
      growFoot Fc M.core c, hc.symm, rfl, ?_, hc ▸ hW', grows_growFoot _ _ _⟩⟩
    exact holdX_grow hH.bound ST hR' hW' hU' hH.imp hH.exp
  rcases hround with ⟨trc, C', S'', F', yc, t', r, hrun, hq, hIc, hTc, final, hwr, hFG', hX'⟩ |
    ⟨c, hT, hTA, hTT, hwr⟩
  · -- the importer's part finished
    have hS₀ : S''.funcs = M.store.funcs := callExt_funcs hX'
    obtain ⟨ρ₁, O₁, hLc, -⟩ := hIc.rel
    cases r with
    | throw b => exact (not_result_throw hLc final).elim
    | trap =>
      exact hfr _ (TrapEnd.stepsI hrun hq (coreTrap_end (status_of_trap g hLc final)))
        (trapAt_of_linv hIc hS₀) (trapT_of_linv hIc hTc hS₀)
        (lifted_trap (x := lg.imp.exports[dr.j]) (fun _ h => by cases h) hwr)
    | values cvs =>
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (Ii.exports.get dr.f.1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hwr
        dsimp only at hwr
        split_ifs at hwr with ht
        exact ht
      rw [hft'] at htyped
      obtain ⟨zs, hm⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hst := status_of_values g hLc final hm
      have hzty : zs.map (·.type) = ValTy.flatList lg.imp.exports[dr.j].ty.results :=
        results_typed hft' hwr hm
      have hR' : dr.ans = (liftArgs lg.imp.exports[dr.j].ty.results zs).map .vals :=
        lifted_answer hwr hm
      have s₃ : Step prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest yc) .tau
          (retCfg { M with conts := C', store := S''.toCStore } th K segs rest yc zs) :=
        Step.coreReturned rfl hst
      have hret : retCfg { M with conts := C', store := S''.toCStore } th K segs rest yc zs =
          ExpSpec.RefData.retCfg' M S'' C' th K segs rest zs := by
        unfold retCfg
        rw [← hIc.core]
        rfl
      rw [hret] at s₃
      obtain ⟨ρ₂, O₂, hR₂, hW₂, hU₂⟩ := lready_afterW hR.toG hIc hTc
      have hSf : S''.funcs = M.store.funcs := hS₀
      have hout := ST.out
      have hii : S''.insts[pl.ii]? = M.store.insts[pl.ii]? := hX'.insts_out pl.ii hout
      have hH₂ : HoldX lg d Ii pl st' S'' (growFoot Fc M.core S''.core) := by
        refine holdX_grow hH.bound (hSf ▸ ST) hR₂ hW₂ hU₂ ?_ hFG'.exp
        rw [hii]
        exact hH.imp
      have hext : (toExpData lg d Ii).StoreExt pl M.ref S'' :=
        ⟨hX'.eq, hX'.insts_len, fun i hi => hX'.insts_out i (fun h => hi (.inl h)), fun _ => hii,
          hX'.subtasks, hX'.callers, hX'.tasks, hX'.threads⟩
      have hrun₃ : Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (coreCfg M th K segs rest (M.core,
            Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (pl.s₀.funcs.length + Ii.addr dr.f.1)
              (lowerArgs lg.imp.exports[dr.j].ty.params dr.vs))) (trc ++ [.tau])
          (ExpSpec.RefData.retCfg' M S'' C' th K segs rest zs) :=
        Adequacy.steps_append (hr := (linkHost impl).hr) (dispatch := (linkHost impl).dispatch)
          hrun (.cons s₃ (.refl _))
      refine ⟨trc ++ [.tau], _, hrun₃,
        (noHI_cons_tau hq).1, (noHI_cons_tau hq).2, .inl ⟨S'', C', zs,
          growFoot Fc M.core S''.core, rfl, hxty ▸ hzty, ?_, hext, hH₂, hW₂,
          grows_growFoot _ _ _⟩⟩
      rw [hR', hxty]
      cases liftArgs lg.imp.exports[dr.j].ty.results zs <;> rfl
  · -- a trapped end of the round
    exact hfr c hT hTA hTT (lifted_trap (x := lg.imp.exports[dr.j]) (fun _ h => by cases h) hwr)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
