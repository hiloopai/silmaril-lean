module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Rounds

/-!
# The importer's invariant between calls, against an abstract exporter

`LReady` of `LinkNext` with the exporter's half of `Rel4` replaced by the exporter's relation
`d.Hold pl s S F` (as `LInvG` does along a call):

* `LReadyG d pl Ii s₀ ui F₀ g Oc₀ S s u`: between calls, at the component store `S`, the
  exporter's state `s` and the importer's store `u` (`ui` the importer's store after
  instantiation): the importer's image of `u` in `S.core` disjoint from an allocated footprint
  of the exporter's relation, its functions in `S.core`, `u` well formed and good;
* `linv_readyG`: `LInvG` at the importer's export call, from `LReadyG` (`linkSt_invoke`);
* `lready_afterG`: `LReadyG` at any point of a call started from `LReadyG` (the importer's
  typing along its run, `typing_after`);
* `lready_trapG`: after a trapped call, `LReadyG` at the earlier store with the trapped core
  store (`resumeCfg`), from `TrapAtG` and R5 (`RefData.Resume`);
* `lready_frame`: `LReadyG` is kept by a change of the component store outside the core store,
  the functions and the exporter's block (R1).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile}

/-- **The importer's invariant between calls** at the component store `S`, the exporter's
state `s` and the importer's store `u`. -/
structure LReadyG {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (Ii : SInst) (s₀ ui : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (S : RefStore (E3 P)) (s : e.St) (u : Store Nat) : Prop where
  rel : ∃ (F : CoreFoot) (ρc : Ren) (Oc : Own), PartRel ρc Oc (reloc s₀ u) (Store.mapH g S.core) ∧
    Oc.fn = Oc₀.fn ∧ Oc.gl = Oc₀.gl ∧ FootDisj F ρc Oc S.core ∧ d.Hold pl s S F
  fnC : FnPre s₀ (Store.mapH g S.core) u
  wfI : Ii.WellFormed u
  funcs : S.core.funcs = F₀
  ufuncs : u.funcs = ui.funcs
  good : SGoodSt (ownOf ui).fn u

section Ready

variable {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {Ii : SInst} {s₀ ui : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat} {Oc₀ : Own}

/-- **The invariant at the importer's export call**: the shared thread invokes the relocated
address of the export question `f` on flat arguments, the part its initial thread. -/
theorem linv_readyG {S : RefStore (E3 P)} {s : e.St} {u : Store Nat}
    (hR : LReadyG d pl Ii s₀ ui F₀ g Oc₀ S s u)
    (hO : ∀ a, a < ui.funcs.length → Oc₀.fn (s₀.funcs.length + a)) {f : Ii.F.Op}
    {xs : List Flat} (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat) :
    ∃ F : CoreFoot, LInvG d pl Ii s₀ u F₀ g Oc₀ f s S F
      (S.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1) xs)
      (u, Ii.initThread f) := by
  obtain ⟨F, ρc, Oc, hrc, hfn, hgl, hD, hH⟩ := hR.rel
  obtain ⟨fi, hfi, -⟩ := hR.wfI.export_type f.1
  have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
  have ha₀ : Ii.addr f.1 < ui.funcs.length := hR.ufuncs ▸ ha
  have hvs : ∀ v ∈ f.2.1, ∀ r, v ≠ .ref r := hxs ▸ ofFlat_scalar xs
  have hOc : Oc.fn (s₀.funcs.length + Ii.addr f.1) := by
    rw [hfn]
    exact hO _ ha₀
  have hg : SplitGood (Silmaril.Wasm.Execution.Core.invoke u (Ii.addr f.1) f.2.1) :=
    (sgood_invoke hR.good (show (ownOf ui).fn (Ii.addr f.1) from ha₀)
      (fun _ => goodVal_of_hasVal f.2.2)).splitGood
  have hL := linkSt_invoke hrc hR.fnC ha hOc hvs hg
  have hshared : (Store.mapH g S.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1) xs) =
      (Store.mapH g S.core, Silmaril.Wasm.SingleThreaded.Thread.pending
        (s₀.funcs.length + Ii.addr f.1) f.2.1) := by
    rw [hxs]
    rfl
  exact ⟨F, ⟨ρc, Oc, hshared ▸ hL, hfn, hgl, hD⟩, hH, rfl, hR.funcs, .refl⟩

/-- **The importer's typing along its run**: the store of any point of a run of the importer's
activation of `f` from a well-formed good store `u` is well formed, good, with the functions
of `u`. -/
theorem typing_after {u : Store Nat} (hwf : Ii.WellFormed u) (hgood : SGoodSt (ownOf ui).fn u)
    (hufun : u.funcs = ui.funcs) {f : Ii.F.Op} {x : Store Nat × STh}
    (hrun : Silmaril.Wasm.Game.SSteps P (valEnv Ii)
      (Silmaril.Wasm.Execution.Core.invoke u (Ii.addr f.1) f.2.1, ()) (x.2.config x.1, ())) :
    Ii.WellFormed x.1 ∧ x.1.funcs = ui.funcs ∧ SGoodSt (ownOf ui).fn x.1 := by
  have hx1 : (x.2.config x.1).store = x.1 := Silmaril.Wasm.SingleThreaded.Thread.config_store _ _
  obtain ⟨ts, hg₀⟩ := SEnvTyping.good_invoke hwf f
  have hg := SEnvTyping.good_ssteps (P := P) hwf (valEnv_throwsBelow Ii _)
    (x := (_, ())) (y := (x.2.config x.1, ())) hg₀ hrun
  have hs : Silmaril.Wasm.Execution.Core.StoreOk x.1 := by
    have h := Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk hg.ok
    rwa [hx1] at h
  have hfx : x.1.funcs = u.funcs := hx1 ▸ hg.inv.funcs
  obtain ⟨fi, hfi, -⟩ := hwf.export_type f.1
  have ha₀ : (ownOf ui).fn (Ii.addr f.1) := by
    have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
    show Ii.addr f.1 < ui.funcs.length
    exact hufun ▸ ha
  have hsg := sgood_ssteps (P := P) (x := (_, ())) (y := (x.2.config x.1, ())) hrun
    (sgood_invoke hgood ha₀ (fun _ => goodVal_of_hasVal f.2.2))
  exact ⟨wellFormed_of_funcs' hwf hs hfx, hfx.trans hufun, hx1 ▸ hsg.st⟩

/-- **The invariant between calls from the invariant along a call** started from `LReadyG` at
the importer's store `u`. -/
theorem lready_afterG {S S' : RefStore (E3 P)} {s s' : e.St} {u : Store Nat}
    (hR : LReadyG d pl Ii s₀ ui F₀ g Oc₀ S s u) {f : Ii.F.Op} {F : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u F₀ g Oc₀ f s' S' F y x) :
    LReadyG d pl Ii s₀ ui F₀ g Oc₀ S' s' x.1 := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD⟩ := hI.rel
  obtain ⟨hwf, hfx, hsg⟩ := typing_after hR.wfI hR.good hR.ufuncs hI.run
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  rw [← hI.core] at hR0 hD
  have hfn' : FnPre s₀ (Store.mapH g S'.core) x.1 := by
    rw [hI.core]
    exact hL.fn
  exact ⟨⟨F, ρc, Oc, hR0, hfn, hgl, hD, hI.hold⟩, hfn', hwf, hI.core ▸ hI.funcs, hfx, hsg⟩

/-- **The invariant between calls after a trapped call**, at the store `S₀` of the call's start
with the trapped core store `c` (as `resumeCfg` resumes), from R5. -/
theorem lready_trapG (hRes : d.Resume) {S₀ : RefStore (E3 P)} {s s₁ : e.St} {u u₁ : Store Nat}
    (hR : LReadyG d pl Ii s₀ ui F₀ g Oc₀ S₀ s u) {f : Ii.F.Op}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (hT : TrapAtG d pl Ii s₀ u F₀ g Oc₀ f S₀ s₁ c u₁) :
    LReadyG d pl Ii s₀ ui F₀ g Oc₀ { S₀ with core := c } s₁ u₁ := by
  obtain ⟨⟨S', F', hc, hf, hH', ρc, Oc, hrc, hfn, hgl, hD⟩, hfnC, hfun, t, hrun⟩ := hT
  obtain ⟨F₁, -, -, -, -, -, -, hH₀⟩ := hR.rel
  obtain ⟨hwf, hfx, hsg⟩ := typing_after (x := (u₁, t)) hR.wfI hR.good hR.ufuncs hrun
  have hH : d.Hold pl s₁ { S₀ with core := S'.core } F' := hRes pl s s₁ S₀ S' F₁ F' hH₀ hH' hf
  rw [hc] at hH
  exact ⟨⟨F', ρc, Oc, hrc, hfn, hgl, hD, hH⟩, hfnC, hwf, hfun, hfx, hsg⟩

/-- **The invariant between calls is kept by the importer's changes outside the core store**:
the same core store and functions, the exporter's instances unchanged (R1). -/
theorem lready_frame (hFr : d.Frame) {S S' : RefStore (E3 P)} {s : e.St} {u : Store Nat}
    (hR : LReadyG d pl Ii s₀ ui F₀ g Oc₀ S s u) (hc : S'.core = S.core)
    (hf : S'.funcs = S.funcs) (hb : ∀ i, d.block pl i → S'.insts[i]? = S.insts[i]?) :
    LReadyG d pl Ii s₀ ui F₀ g Oc₀ S' s u := by
  obtain ⟨F, ρc, Oc, hrc, hfn, hgl, hD, hH⟩ := hR.rel
  have hH' : d.Hold pl s S' F :=
    hFr.agree pl s S S' F hH (agree_of_eq F hc) (by rw [hf]) hb
  rw [← hc] at hrc hD
  exact ⟨⟨F, ρc, Oc, hrc, hfn, hgl, hD, hH'⟩, hc ▸ hR.fnC, hR.wfI, hc ▸ hR.funcs, hR.ufuncs,
    hR.good⟩

end Ready

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
