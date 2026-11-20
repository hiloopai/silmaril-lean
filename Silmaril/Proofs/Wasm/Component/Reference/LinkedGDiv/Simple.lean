module

public import Silmaril.Wasm.Component.Reference.LinkedGDiv.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.SimpleBwd
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.Back
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Simple
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.ReachL

/-!
# R7 for a simple exporter

`simple_div`: the data `simpleData` of a simple exporter meets `RefData.Div`. The exporter's
part of a call is the core activation of its export in the shared store (`startCfg` is a
`coreCfg`):

* **forward**: `DivAt` is an infinite host-free run of the exporter from its store; through the
  part's relation (`exp_invoke`) it is an infinite core run of the shared thread (`link_inf`),
  one machine step per core step (`coreCfg_diverges_of`);
* **backward**: a divergence of the core activation either stays in the core phase forever, an
  infinite core run read back as an infinite run of the exporter (`link_inf_back`), i.e.
  `DivAt`; or it leaves the core phase at `y` with a step to `m₁` from which the machine
  diverges (`coreCfg_diverges_step`). The exit is not a callout (`exp_back1`), not a core trap
  (`trapCfg` does not diverge), so it is a return of values (`Step.coreReturned`) at an end of R2
  for the step `ret` (results that lift) or `trap` (results that do not), as in `simple_bwd`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile}

/-- **R7 for a simple exporter.** -/
theorem simple_div {c : Simple} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I) :
    (simpleData P c I).Div := by
  intro pl s w vs x hx htyped S F hH σ prof impl M th K segs rest hM hlock _
  subst hM
  have hwx := List.getElem?_eq_some_iff.mp hx
  have hwl : w < c.exports.length := by
    have := hwx.1
    rwa [LinkedG.ofSimple_length] at this
  have hxty : x.ty = c.exports[w].ty := by
    rw [← hwx.2]
    exact LinkedG.ofSimple_ty c hwx.1 hwl
  have hxm : c.exports[w] ∈ c.exports := List.getElem_mem hwl
  have haddr : sAddr c I w = I.addrs.getD c.exports[w].core 0 := by
    simp [sAddr, List.getElem?_eq_getElem hwl]
  obtain ⟨ρ, O, hR, hO, rfl⟩ := hH.rel
  have hs := hostsSat_hIdx (P := P) M.core
  have hRg : PartRel ρ O s (Store.mapH (hIdx M.core) M.core) := partRel_mapH hR
  have hFg : FnPre ({} : Store Nat) (Store.mapH (hIdx M.core) M.core) s :=
    fnPre_mapH hH.free hH.fn
  have hOw : O.fn (I.addrs.getD c.exports[w].core 0) := hO ▸ owned_init hc hI _ hxm
  obtain ⟨nm, hcx⟩ := hc.core _ hxm
  have hk : c.exports[w].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have typed : ValTy.checkList c.exports[w].ty.params vs = true := hxty ▸ htyped
  have hstart : (simpleData P c I).startCfg pl w x vs M th K segs rest =
      coreCfg M th K segs rest (M.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[w].core 0) (lowerArgs c.exports[w].ty.params vs)) := by
    show { M with ctl := ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (sAddr c I w)
      (lowerArgs x.ty.params vs)) K, segs⟩ :: rest } = _
    rw [haddr, hxty]
    rfl
  have hL₀ := exp_invoke hRg hFg hOw (lowerArgs c.exports[w].ty.params vs)
  rw [hstart]
  constructor
  · -- forward: `DivAt` is an infinite core run of the shared thread
    rintro ⟨j, vs', hq, hdiv⟩
    simp only [Prod.mk.injEq, Payload.vals.injEq] at hq
    obtain ⟨hj, rfl⟩ := hq
    have hjw : c.exports[j] = c.exports[w] := by
      simp only [Fin.getElem_fin, ← hj]
    rw [hjw] at hdiv
    obtain ⟨g, hg0, hg⟩ := hdiv.run
    exact SessionDiv.coreCfg_diverges_of
      (LinkedSessionDiv.link_inf (hIdx M.core) (hInv M.core) hg hs (hg0 ▸ hL₀))
  · -- backward
    intro hd
    rcases LinkedSessionDivInv.coreCfg_diverges_step hd with hinf |
      ⟨y, lb, m₁, hy, hxit, -, d₁⟩
    · -- the core activation runs forever: `DivAt`
      left
      obtain ⟨ts, htyped', -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hH.wf
        (opAt hI hk (exp_hxs hcx typed hk))
      have hrun := LinkedSessionDivInv.link_inf_back (hIdx M.core) hinf hL₀
        hH.wf.storeOk htyped'
      exact ⟨⟨w, hwl⟩, vs, rfl, typed, hrun⟩
    · right
      obtain ⟨π', t', ρ', O', hL, hrel, hgr, htc, hfπ, hnco, hval, -⟩ :=
        exp_back1 hI ⟨nm, hcx⟩ typed hH.wf (hIdx M.core) hRg hFg hOw hy
      have hfe : (y.1 : Store (CanonHost (E3 P))).funcs = (M.core : Store _).funcs :=
        coreSteps_funcs hy
      have hW := within_of_touch' htc hfe
      have hG := grows_of_grow (grow_unmapH hgr)
      rcases hxit with ⟨zs, hzs, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h, ys, hco⟩
      · obtain ⟨hty, hret, hnl⟩ := hval zs hzs
        have hty' : zs.map (·.type) = ValTy.flatList x.ty.results := by rw [hxty]; exact hty
        obtain ⟨tr, htr, r⟩ := Adequacy.coreCfg_steps_of (prof := prof)
          (hr := (linkHost impl).hr) (dispatch := (linkHost impl).dispatch) (B := M) (th := th)
          (K := K) (segs := segs) (rest := rest) hy
        have s₄ : Step prof (linkHost impl).hr (linkHost impl).dispatch
            (coreCfg M th K segs rest y) .tau (retCfg M th K segs rest y zs) :=
          Step.coreReturned rfl hzs
        have r₁ := Adequacy.steps_append r (.cons s₄ (.refl _))
        have hq : Quiet (P := P) (σ := σ) (tr ++ [.tau]) := (Quiet.of_core htr).append Quiet.tau
        have hunl : (retCfg M th K segs rest y zs).store.lockdown = true →
            (retCfg M th K segs rest y zs).ctl = [] := fun hl =>
          absurd (hl.symm.trans hlock) (by decide)
        cases hus : liftArgs c.exports[w].ty.results zs with
        | some ws =>
          have hRA := hret ws hus
          have hH' := shold_after hH hO hL hrel hgr hfπ (RetAt.wellFormed hI ⟨nm, hcx⟩ hH.wf hRA)
          refine ⟨tr ++ [.tau], _, some (.vals ws), π', r₁, hq.1, .ret hwl hRA,
            ⟨.inl ⟨{ M.ref with core := y.1 }, M.conts, zs, img ρ' O', rfl, hty', ?_,
              storeExt_core c I pl M.ref y.1, hH', hW, hG⟩, hunl⟩,
            List.cons_ne_nil _ _, d₁⟩
          show liftArgs x.ty.results zs = some ws
          rw [hxty]
          exact hus
        | none =>
          have hT := hnl hus
          have hH' := shold_after hH hO hL hrel hgr hfπ (hT.wellFormed hI ⟨nm, hcx⟩ hH.wf)
          refine ⟨tr ++ [.tau], _, none, π', r₁, hq.1, .trap hwl hT,
            ⟨.inl ⟨{ M.ref with core := y.1 }, M.conts, zs, img ρ' O', rfl, hty', ?_,
              storeExt_core c I pl M.ref y.1, hH', hW, hG⟩, hunl⟩,
            List.cons_ne_nil _ _, d₁⟩
          show liftArgs x.ty.results zs = none
          rw [hxty]
          exact hus
      · exact absurd d₁ (not_diverges_trapCfg _)
      · exact (hnco h ys hco).elim

/-- **A simple exporter meets `RefAdeqUXD`**, with the data of `simple_refAdeqU`. -/
theorem simple_refAdeqUXD (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqUXD P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, LinkedGInv.simple_bwdF hc hI,
    LinkedGInst.initU_initUX (LinkedGInst.simple_initU hc hi hI hS hN), simple_resume c I,
    LinkedGImp.simple_bounded c I, simple_div hc hI⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv
