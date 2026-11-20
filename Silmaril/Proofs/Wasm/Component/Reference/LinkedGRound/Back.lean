module

public import Silmaril.Wasm.Component.Reference.LinkedGRound.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.SimpleBwd
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Inv

/-!
# R3 through returns only

* `locked_modify_step`, `locked_core_step`: a locked-down configuration with a non-empty control
  chain still steps: a `modify` in focus may unlock the store, a running core activation in
  focus changes the core store. So a locked-down end of R2 with a non-empty control chain (which
  R3's middle case allows) says nothing about the rest of the run;
* `bwdT_bwd`: the corrected R3 implies R3;
* `endsT_unlocked`: in the corrected middle case the end is not locked down (a return);
* `simple_bwdT`: a simple exporter meets the corrected R3 (`simple_bwd`, whose middle case is
  a return); `simple_refAdeqT`: it meets `RefAdeqT` with the data of `simple_refAdeqB`;
* `refAdeqT_refAdeqB`: `RefAdeqT` implies `RefAdeqB`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

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

/-! ## Locked-down configurations with a non-empty control chain -/

section Locked

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- **A locked-down configuration may unlock**: a `modify` in focus applies its update, whatever
the lockdown flag. -/
theorem locked_modify_step (m : Machine.Config E σ) {th : Option ThreadId}
    {k : Unit → Canon.P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Canon.Eff E σ)
      (.modify fun s => { s with lockdown := false }) k), segs⟩ :: rest) :
    Step prof hr dispatch m .tau
      { m with
        store := { m.store with lockdown := false }
        ctl := ⟨th, .prog (k ()), segs⟩ :: rest } :=
  Step.modify hc

/-- **A locked-down configuration may change its core store**: an internal step of a running
core activation in focus, whatever the lockdown flag. -/
theorem locked_core_step (m : Machine.Config E σ) {th : Option ThreadId}
    {ct ct' : E.Thread (CanonHost E)} {c' : E.Store (CanonHost E)}
    {k : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .running) (hi : E.Internal (m.core, ct) (c', ct')) :
    Step prof hr dispatch m .core
      { m with core := c', ctl := ⟨th, .core ct' k, segs⟩ :: rest } :=
  Step.coreInternal hc (.inl hs) hi

end Locked

/-! ## The corrected R3 -/

variable {P : Profile}

/-- The corrected R3 implies R3. -/
theorem bwdT_bwd {e : ExpSpec} {d : e.RefData P} (h : d.BwdT) : d.Bwd := by
  intro pl s w vs x hx hck S F hH σ prof impl M th K segs rest hM hl hi tr m' r hn
  rcases h pl s w vs x hx hck S F hH prof impl M th K segs rest hM hl hi tr m' r hn with
    h | ⟨tr₁, tr₂, m, R, s', h₁, h₂, h₃, h₄, ⟨h₅, -⟩, h₆⟩ | h
  · exact .inl h
  · exact .inr (.inl ⟨tr₁, tr₂, m, R, s', h₁, h₂, h₃, h₄, h₅, h₆⟩)
  · exact .inr (.inr h)

/-- **The corrected middle case is a return**: its end is not locked down. -/
theorem endsT_unlocked {e : ExpSpec} {d : e.RefData P} {σ : Type} {pl : d.Pl} {x : Export}
    {S : RefStore (core3P P)} {F : CoreFoot} {M : Machine.Config (core3P P) σ}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
    {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)}
    {R : Option Payload} {s' : e.St} {m : Machine.Config (core3P P) σ}
    (h : d.EndsT pl x S F M th K segs rest R s' m) (hc : m.ctl ≠ []) :
    m.store.lockdown = false := by
  cases hb : m.store.lockdown with
  | false => rfl
  | true => exact absurd (h.2 hb) hc

/-- **A simple exporter meets the corrected R3** (`simple_bwd`, whose middle case is a
return). -/
theorem simple_bwdT {c : Simple} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I) :
    (simpleData P c I).BwdT := by
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
    exact .inr (.inr ⟨rfl, fun _ => ⟨π', { M.ref with core := y.1 }, img ρ' O', .trap hwl hT,
      rfl, rfl, hH'⟩⟩)
  · exact (hnco h ys hco).elim

/-- **A simple exporter meets R1, R2, the corrected R3, R4, R5 and R6.** -/
theorem simple_refAdeqT (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqT P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, simple_bwdT hc hI,
    simple_init hc hi hI hS hN, simple_resume c I, LinkedGImp.simple_bounded c I⟩

/-- `RefAdeqT` implies `RefAdeqB`. -/
theorem refAdeqT_refAdeqB {e : ExpSpec} (h : e.RefAdeqT P) : e.RefAdeqB P := by
  obtain ⟨d, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨d, h₁, h₂, bwdT_bwd h₃, h₄, h₅, h₆⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
