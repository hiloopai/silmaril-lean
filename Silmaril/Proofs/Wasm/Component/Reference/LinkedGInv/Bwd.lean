module

public import Silmaril.Wasm.Component.Reference.LinkedGInv.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Simple

/-!
# R3 with the trapped case corrected for the read-back

* `bwdF_bwdT`: `BwdF` implies the corrected R3 `BwdT` of `LinkedGRound`;
* `simple_bwdF`: a simple exporter meets `BwdF` (`simple_bwdT` of `LinkedGRound`, whose trapped
  case is `trapCfg` of the core activation, with the `Within`/`Grows` of its part's run);
* `simple_refAdeqF`, `refAdeqF_refAdeqS`: a simple exporter meets `RefAdeqF`, which implies
  `RefAdeqS`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile}

/-- `BwdF` implies the corrected R3. -/
theorem bwdF_bwdT {e : ExpSpec} {d : e.RefData P} (h : d.BwdF) : d.BwdT := by
  intro pl s w vs x hx hck S F hH σ prof impl M th K segs rest hM hl hi tr m' r hn
  rcases h pl s w vs x hx hck S F hH prof impl M th K segs rest hM hl hi tr m' r hn with
    h | h | ⟨h₁, -, h₂⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨h₁, fun hni => ?_⟩)
    obtain ⟨s', S', F', hs, hc, hf, hH', -, -⟩ := h₂ hni
    exact ⟨s', S', F', hs, hc, hf, hH'⟩

/-- **A simple exporter meets `BwdF`**: `simple_bwdT`, its trapped case `trapCfg` of its core
activation, changing the core store inside its part. -/
theorem simple_bwdF {c : Simple} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I) :
    (simpleData P c I).BwdF := by
  intro pl s w vs x hx htyped S F hH σ prof impl M th K segs rest hM hlock _ tr m' run _
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
  have hRg : PartRel ρ O s (Store.mapH (hIdx M.core) M.core) := partRel_mapH hR
  have hFg : FnPre ({} : Store Nat) (Store.mapH (hIdx M.core) M.core) s :=
    fnPre_mapH hH.free hH.fn
  have hOw : O.fn (I.addrs.getD c.exports[w].core 0) := hO ▸ owned_init hc hI _ hxm
  obtain ⟨nm, hcx⟩ := hc.core _ hxm
  have typed : ValTy.checkList c.exports[w].ty.params vs = true := hxty ▸ htyped
  have hstart : (simpleData P c I).startCfg pl w x vs M th K segs rest =
      coreCfg M th K segs rest (M.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[w].core 0) (lowerArgs c.exports[w].ty.params vs)) := by
    show { M with ctl := ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (sAddr c I w)
      (lowerArgs x.ty.params vs)) K, segs⟩ :: rest } = _
    rw [haddr, hxty]
    rfl
  rw [hstart] at run ⊢
  rcases coreCfg_steps_inv2 run with ⟨y, -, rfl⟩ |
      ⟨y, pre, l, m₁, tr₂, hy, hpre, rfl, hxit, st, r₂⟩
  · exact .inl ⟨List.cons_ne_nil _ _, hlock⟩
  obtain ⟨π', t', ρ', O', hL, hrel, hgr, htc, hfπ, hnco, hval, htrap⟩ :=
    exp_back1 hI ⟨nm, hcx⟩ typed hH.wf (hIdx M.core) hRg hFg hOw hy
  have hfe : (y.1 : Store (CanonHost (E3 P))).funcs = (M.core : Store _).funcs :=
    coreSteps_funcs hy
  have hW := within_of_touch' htc hfe
  have hG := grows_of_grow (grow_unmapH hgr)
  rcases hxit with ⟨zs, hzs, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩ | ⟨h, ys, hco⟩
  · obtain ⟨hty, hret, hnlift⟩ := hval zs hzs
    have hty' : zs.map (·.type) = ValTy.flatList x.ty.results := by rw [hxty]; exact hty
    have r₁ := Adequacy.steps_append hpre (.cons st (.refl _))
    cases hus : liftArgs c.exports[w].ty.results zs with
    | some ws =>
      have hRA := hret ws hus
      have hH' := shold_after hH hO hL hrel hgr hfπ (RetAt.wellFormed hI ⟨nm, hcx⟩ hH.wf hRA)
      refine .inr (.inl ⟨pre ++ [.tau], tr₂, _, some (.vals ws), π', by simp, r₁, r₂,
        .ret hwl hRA, ⟨.inl ⟨{ M.ref with core := y.1 }, M.conts, zs, img ρ' O', rfl, hty',
          ?_, storeExt_core c I pl M.ref y.1, hH', hW, hG⟩,
          fun h => absurd (hlock.symm.trans h) (by decide)⟩, List.cons_ne_nil _ _⟩)
      show liftArgs x.ty.results zs = some ws
      rw [hxty]
      exact hus
    | none =>
      have hT := hnlift hus
      have hH' := shold_after hH hO hL hrel hgr hfπ (hT.wellFormed hI ⟨nm, hcx⟩ hH.wf)
      refine .inr (.inl ⟨pre ++ [.tau], tr₂, _, none, π', by simp, r₁, r₂,
        .trap hwl hT, ⟨.inl ⟨{ M.ref with core := y.1 }, M.conts, zs, img ρ' O', rfl, hty',
          ?_, storeExt_core c I pl M.ref y.1, hH', hW, hG⟩,
          fun h => absurd (hlock.symm.trans h) (by decide)⟩, List.cons_ne_nil _ _⟩)
      show liftArgs x.ty.results zs = none
      rw [hxty]
      exact hus
  · have hT := htrap htr
    have hH' := shold_after hH hO hL hrel hgr hfπ (hT.wellFormed hI ⟨nm, hcx⟩ hH.wf)
    rw [steps_of_locked rfl rfl r₂]
    exact .inr (.inr ⟨rfl, rfl, fun _ => ⟨π', { M.ref with core := y.1 }, img ρ' O',
      .trap hwl hT, rfl, rfl, hH', hW, hG⟩⟩)
  · exact (hnco h ys hco).elim

/-- `RefAdeqF` implies `RefAdeqS`. -/
theorem refAdeqF_refAdeqS {e : ExpSpec} (h : e.RefAdeqF P) : e.RefAdeqS P := by
  obtain ⟨d, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨d, h₁, h₂, bwdF_bwdT h₃, h₄, h₅, h₆⟩

/-- **A simple exporter meets `RefAdeqF`.** -/
theorem simple_refAdeqF (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqF P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, simple_bwdF hc hI,
    LinkedGInit.simple_initS hc hi hI hS hN, simple_resume c I, LinkedGImp.simple_bounded c I⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
