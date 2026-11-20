module

public import Silmaril.Wasm.Component.Reference.LinkedGRef.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Basic

/-!
# The reference data of a simple exporter

`Simple.expSpec c I` (a simple component at its core instance `I`) with the data `simpleData`:

* placements `Nat × List Nat`: the component instance of the exporter's `canon lift`s and the
  function ids of its exports; the core address of export `w` is `I.addrs.getD x.core 0`;
* `SHold`: the exporter's store `π` embeds into the shared core store (with host code renamed
  to `0`, `h0`) along a renaming `ρ` for an ownership `O` with the functions of `I.store`
  (`PartRel`, `FnPre`), its footprint the image of `O` (`img`); `π` is well formed, has the
  functions of `I.store`, all of them wasm functions; the function ids are the lifted exports.

Proved: R1 (`simple_frame`), R2 (`simple_fwd`, from `exp_fwd1`: `exp_fwd` without the
importer's part, and the machine's core steps), R5 (`simple_resume`). The host renaming is
immaterial for the exporter's part (`partRel_mapH`, `fnPre_mapH`); the runs use the renaming
`hIdx` of the shared store's host code by position, inverted by `hInv`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
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

/-! ## Host renamings -/

section Host

variable {H : Type}

/-- Host code renamed to `0`. -/
def h0 (H : Type) : H → Nat := fun _ => 0

theorem funcInst_mapH_wasm {g g' : H → Nat} {fi₀ : FuncInst H} {fi : FuncInst Nat}
    (h : FuncInst.mapH g fi₀ = fi) {c : Silmaril.Wasm.Func}
    (hc : fi.code = .wasm c) : FuncInst.mapH g' fi₀ = fi := by
  obtain ⟨t, m, code⟩ := fi₀
  cases code with
  | wasm f => rw [← h]; rfl
  | host x =>
    rw [← h] at hc
    cases hc

theorem funcs_mapH_get (g : H → Nat) (σ : Store H) (a : Nat) :
    (Store.mapH g σ).funcs[a]? = (σ.funcs[a]?).map (FuncInst.mapH g) := by
  simp [Store.mapH]

/-- **The host renaming is immaterial for a part's relation.** -/
theorem partRel_mapH {g g' : H → Nat} {ρ : Ren} {O : Own} {π : Store Nat} {σ : Store H}
    (h : PartRel ρ O π (Store.mapH g σ)) : PartRel ρ O π (Store.mapH g' σ) where
  fn a ha := by
    obtain ⟨fi, h1, fi', h2, h3, h4⟩ := h.fn a ha
    rw [funcs_mapH_get] at h2
    obtain ⟨fi₀, h5, rfl⟩ := Option.map_eq_some_iff.mp h2
    refine ⟨fi, h1, FuncInst.mapH g' fi₀, by rw [funcs_mapH_get, h5]; rfl, h3, fun c hc => ?_⟩
    obtain ⟨e, hm⟩ := h4 c hc
    exact ⟨funcInst_mapH_wasm e hc, hm⟩
  gl := h.gl
  st := h.st
  ar := h.ar
  stInj := h.stInj
  arInj := h.arInj

/-- The functions of `π` are wasm functions. -/
def HostFree (π : Store Nat) : Prop :=
  ∀ (a : Nat) (fi : FuncInst Nat), π.funcs[a]? = some fi → ∃ c, fi.code = .wasm c

/-- **The host renaming is immaterial for the function prefix of a host-free part.** -/
theorem fnPre_mapH {g g' : H → Nat} {π : Store Nat} {σ : Store H} (hp : HostFree π)
    (h : FnPre ({} : Store Nat) (Store.mapH g σ) π) : FnPre ({} : Store Nat) (Store.mapH g' σ) π := by
  intro a fi ha
  have ha' : π.funcs[a]? = some fi := by rwa [reloc_empty] at ha
  obtain ⟨c, hc⟩ := hp a fi ha'
  have h2 := h a fi ha
  rw [funcs_mapH_get] at h2 ⊢
  obtain ⟨fi₀, h5, e⟩ := Option.map_eq_some_iff.mp h2
  rw [h5]
  exact congrArg some (funcInst_mapH_wasm e hc)

end Host

/-! ## The renaming of the shared store's host code by position -/

section Idx

/-- The host code of the shared store, in function order. -/
def hostCodes (σ : Store (CanonHost (E3 P))) : List (CanonHost (E3 P)) :=
  σ.funcs.filterMap fun fi => match fi.code with
    | .host h => some h
    | .wasm _ => none

/-- Host code to its position in `hostCodes`. -/
def hIdx (σ : Store (CanonHost (E3 P))) (h : CanonHost (E3 P)) : Nat := (hostCodes σ).idxOf h

/-- Positions back to host code. -/
def hInv (σ : Store (CanonHost (E3 P))) (n : Nat) : CanonHost (E3 P) :=
  (hostCodes σ).getD n (.embedder "" ⟨[], []⟩)

theorem hostsSat_hIdx (σ : Store (CanonHost (E3 P))) :
    HostsSat (fun h => hInv σ (hIdx σ h) = h) σ := by
  intro a fi h ha hc
  have hm : h ∈ hostCodes σ := by
    refine List.mem_filterMap.mpr ⟨fi, List.mem_of_getElem? ha, ?_⟩
    rw [hc]
  unfold hInv hIdx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hm),
    Option.getD_some]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)

end Idx

/-! ## Footprints of a part -/

/-- The footprint of a part with renaming `ρ` and ownership `O`, in the shared store. -/
def img (ρ : Ren) (O : Own) : CoreFoot :=
  ⟨O.gl, fun b => ∃ a, O.st a ∧ ρ.st a = b, fun b => ∃ a, O.ar a ∧ ρ.ar a = b⟩

section Foot

variable {H : Type}

theorem within_of_touch {ρ : Ren} {O : Own} {σ σ' : Store H} (h : Touch ρ O σ σ') :
    (img ρ O).Within σ σ' where
  funcs := h.funcs
  globals a ha := h.globals a ha
  structs a ha hl := h.structs a (fun b hb e => ha ⟨b, hb, e⟩) hl
  arrays a ha hl := h.arrays a (fun b hb e => ha ⟨b, hb, e⟩) hl
  structs_len := h.structs_len
  arrays_len := h.arrays_len

theorem grows_of_grow {ρ ρ' : Ren} {O O' : Own} {σ : Store H} (h : Grow ρ O ρ' O' σ) :
    (img ρ O).Grows (img ρ' O') σ where
  gl a := by simp only [img, h.gl]
  st a := by
    rintro ⟨b, hb, rfl⟩
    exact ⟨b, (h.st b hb).1, (h.st b hb).2⟩
  ar a := by
    rintro ⟨b, hb, rfl⟩
    exact ⟨b, (h.ar b hb).1, (h.ar b hb).2⟩
  stNew a := by
    rintro ⟨b, hb, rfl⟩
    rcases h.stNew b hb with hb' | hb'
    · exact .inl ⟨b, hb', (h.st b hb').2.symm⟩
    · exact .inr hb'
  arNew a := by
    rintro ⟨b, hb, rfl⟩
    rcases h.arNew b hb with hb' | hb'
    · exact .inl ⟨b, hb', (h.ar b hb').2.symm⟩
    · exact .inr hb'

theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {a : Nat} {x : α}
    (hx : l[a]? = some x) : l'[a]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

/-- A part's relation survives a store agreeing on its footprint. -/
theorem partRel_agree {g : H → Nat} {ρ : Ren} {O : Own} {π : Store Nat} {σ σ' : Store H}
    (h : PartRel ρ O π (Store.mapH g σ)) (ha : (img ρ O).Agree σ σ') :
    PartRel ρ O π (Store.mapH g σ') where
  fn a hO := by
    obtain ⟨fi, h1, fi', h2, h3⟩ := h.fn a hO
    refine ⟨fi, h1, fi', ?_, h3⟩
    rw [funcs_mapH_get] at h2 ⊢
    obtain ⟨fi₀, h5, rfl⟩ := Option.map_eq_some_iff.mp h2
    rw [getElem?_of_prefix ha.funcs h5]
    rfl
  gl a hO := by
    obtain ⟨x, h1, h2, h3⟩ := h.gl a hO
    exact ⟨x, h1, (ha.globals a hO).trans h2, h3⟩
  st a hO := by
    obtain ⟨x, h1, h2, h3⟩ := h.st a hO
    exact ⟨x, h1, (ha.structs _ ⟨a, hO, rfl⟩).trans h2, h3⟩
  ar a hO := by
    obtain ⟨x, h1, h2, h3⟩ := h.ar a hO
    exact ⟨x, h1, (ha.arrays _ ⟨a, hO, rfl⟩).trans h2, h3⟩
  stInj := h.stInj
  arInj := h.arInj

theorem fnPre_prefix {g : H → Nat} {π : Store Nat} {σ σ' : Store H}
    (h : FnPre ({} : Store Nat) (Store.mapH g σ) π) (hp : σ.funcs <+: σ'.funcs) :
    FnPre ({} : Store Nat) (Store.mapH g σ') π := by
  intro a fi ha
  have h2 := h a fi ha
  rw [funcs_mapH_get] at h2 ⊢
  obtain ⟨fi₀, h5, rfl⟩ := Option.map_eq_some_iff.mp h2
  rw [getElem?_of_prefix hp h5]
  rfl

end Foot

/-! ## The data -/

/-- The core address of export `w`. -/
def sAddr (c : Simple) (I : SInst) (w : Nat) : Nat :=
  I.addrs.getD ((c.exports[w]?).elim 0 (·.core)) 0

/-- **The relation of a simple exporter**: at placement `pl` (instance, function ids), its store
`π`, the component store `S` and the footprint `F`. -/
structure SHold (P : Profile) (c : Simple) (I : SInst) (pl : Nat × List Nat) (π : Store Nat)
    (S : RefStore (E3 P)) (F : CoreFoot) : Prop where
  rel : ∃ (ρ : Ren) (O : Own), PartRel ρ O π (Store.mapH (h0 _) (S.core : Store (CanonHost (E3 P))))
    ∧ O.fn = (ownOf I.store).fn ∧ F = img ρ O
  fn : FnPre ({} : Store Nat) (Store.mapH (h0 _) (S.core : Store (CanonHost (E3 P)))) π
  wf : I.WellFormed π
  funcs : π.funcs = I.store.funcs
  free : HostFree π
  lifted : ∀ (w : Nat) (x : Export), (SimpleI.ofSimple c).toComp.exports[w]? = some x →
    ArenaField.funcs.get? S.toCStore ⟨pl.2.getD w 0⟩ =
      some (.lifted (sAddr c I w) (witFt x.ty) {} ⟨pl.1⟩)

/-- **The reference data of a simple exporter.** -/
def simpleData (P : Profile) (c : Simple) (I : SInst) : (Simple.expSpec c I).RefData P where
  Pl := Nat × List Nat
  addr _ w := sAddr c I w
  inst pl _ := pl.1
  fid pl w := pl.2.getD w 0
  block pl i := i = pl.1
  Hold pl π S F := SHold P c I pl π S F

/-! ## R1 and R5 -/

theorem funcs_get_prefix {S S' : CStore (E3 P)} (hp : S.funcs <+: S'.funcs) {f : FuncId}
    {x : CFuncInst (E3 P)} (h : ArenaField.funcs.get? S f = some x) :
    ArenaField.funcs.get? S' f = some x := by
  simp only [ArenaField.get?, ArenaField.funcs, Arena.get?_eq_getElem?] at h ⊢
  exact getElem?_of_prefix hp h

theorem simple_frame (c : Simple) (I : SInst) : (simpleData P c I).Frame where
  agree pl s S S' F h ha hf _ := by
    obtain ⟨ρ, O, hR, hO, rfl⟩ := h.rel
    exact ⟨⟨ρ, O, partRel_agree hR ha, hO, rfl⟩, fnPre_prefix h.fn ha.funcs, h.wf, h.funcs, h.free,
      fun w x hx => funcs_get_prefix hf (h.lifted w x hx)⟩
  threads pl s S F w ι t h _ :=
    ⟨h.rel, h.fn, h.wf, h.funcs, h.free, fun w x hx => h.lifted w x hx⟩
  lifted pl s S F w x h hx := ⟨h.lifted w x hx, rfl⟩

theorem simple_resume (c : Simple) (I : SInst) : (simpleData P c I).Resume := by
  intro pl s s' S₀ S' F₀ F' h₀ h' hf
  exact ⟨h'.rel, h'.fn, h'.wf, h'.funcs, h'.free,
    fun w x hx => h₀.lifted w x hx⟩

/-! ## R2 -/

/-- **`exp_fwd` without the importer's part**: a run of the exporter from its store `π` is a
core run of its activation in the shared store, the part's relation at the end. -/
theorem exp_fwd1 (g : CanonHost (E3 P) → Nat) (gi : Nat → CanonHost (E3 P))
    {σ : Store (CanonHost (E3 P))} (hs : HostsSat (fun h => gi (g h) = h) σ)
    {π : Store Nat} {ρ : Ren} {O : Own} (hR : PartRel ρ O π (Store.mapH g σ))
    (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π) {a : Nat} (hO : O.fn a) (xs : List Flat)
    {π' : Store Nat} {t' : STh}
    (run : Silmaril.Wasm.Game.Reach P (π, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)
      (π', t')) :
    ∃ (e : CoreSt (E3 P)) (ρ' : Ren) (O' : Own),
      Relation.ReflTransGen (CoreStep (E3 P))
        (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) e ∧
      LinkSt ({} : Store Nat) ρ' O' (π', t') (Store.mapH g e.1, e.2) ∧
      PartRel ρ' O' π' (Store.mapH g e.1) ∧ Grow ρ O ρ' O' (Store.mapH g σ) ∧
      Touch ρ O (Store.mapH g σ) (Store.mapH g e.1) ∧ e.1.funcs = σ.funcs := by
  have hL₀ := exp_invoke hR hF hO xs
  obtain ⟨e, ρ', O', hrun, hL, hgr, htc, hfe⟩ :=
    reach_link_fwd g gi run (y := (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)) hs hL₀
  have hrel : PartRel ρ' O' π' (Store.mapH g e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  exact ⟨e, ρ', O', hrun, hL, hrel, hgr, htc, hfe⟩

theorem grow_unmapH {H H' : Type} {g : H → H'} {ρ ρ' : Ren} {O O' : Own} {σ : Store H}
    (h : Grow ρ O ρ' O' (Store.mapH g σ)) : Grow ρ O ρ' O' σ :=
  ⟨h.fn, h.gl, h.st, h.ar, h.stNew, h.arNew⟩

theorem within_of_touch' {g : CanonHost (E3 P) → Nat} {ρ : Ren} {O : Own}
    {σ σ' : Store (CanonHost (E3 P))} (h : Touch ρ O (Store.mapH g σ) (Store.mapH g σ'))
    (hf : σ'.funcs = σ.funcs) : (img ρ O).Within σ σ' :=
  { within_of_touch h with funcs := hf }

/-- **The relation after a run of the exporter**, at the core store the run ends in. -/
theorem shold_after {c : Simple} {I : SInst} {pl : Nat × List Nat} {π π' : Store Nat}
    {S : RefStore (E3 P)} {ρ : Ren} {O : Own} (hH : SHold P c I pl π S (img ρ O))
    (hO : O.fn = (ownOf I.store).fn) {g : CanonHost (E3 P) → Nat} {e : CoreSt (E3 P)}
    {ρ' : Ren} {O' : Own} {t' : STh}
    (hL : LinkSt ({} : Store Nat) ρ' O' (π', t') (Store.mapH g e.1, e.2))
    (hrel : PartRel ρ' O' π' (Store.mapH g e.1)) (hgr : Grow ρ O ρ' O' (Store.mapH g S.core))
    (hf : π'.funcs = π.funcs) (hwf : I.WellFormed π') :
    SHold P c I pl π' { S with core := e.1 } (img ρ' O') := by
  have hfree : HostFree π' := fun a fi ha => hH.free a fi (by rw [← hf]; exact ha)
  exact ⟨⟨ρ', O', partRel_mapH hrel, hgr.fn.trans hO, rfl⟩, fnPre_mapH hfree hL.fn, hwf,
    hf.trans hH.funcs, hfree, fun w x hx => hH.lifted w x hx⟩

theorem storeExt_core (c : Simple) (I : SInst) (pl : Nat × List Nat) (S : RefStore (E3 P))
    (cs : (E3 P).Store (CanonHost (E3 P))) :
    (simpleData P c I).StoreExt pl S { S with core := cs } where
  eq := rfl
  insts_len := rfl
  insts_out _ _ := rfl
  insts_exp _ := rfl
  subtasks := List.prefix_refl _
  callers := List.prefix_refl _
  tasks := List.prefix_refl _
  threads := List.prefix_refl _

/-- **R2 for a simple exporter**: its returned and trapped calls are machine runs of its core
activation in the shared store (`exp_fwd1`, `coreCfg_steps_of`, `status_of_values`,
`status_of_trap`), as in `LInv.resume_fwd` and `LInv.expTrap_fwd` without the importer. -/
theorem simple_fwd {c : Simple} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I) :
    (simpleData P c I).Fwd := by
  intro pl s s' w vs R x hstep hx S F hH σ prof impl M th K segs rest hM _ _
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
  have hstart : (simpleData P c I).startCfg pl w x vs M th K segs rest =
      coreCfg M th K segs rest (M.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[w].core 0) (lowerArgs c.exports[w].ty.params vs)) := by
    show { M with ctl := ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (sAddr c I w)
      (lowerArgs x.ty.params vs)) K, segs⟩ :: rest } = _
    rw [haddr, hxty]
    rfl
  rw [hstart]
  cases hstep with
  | ret hj hRet =>
    obtain ⟨t', cvs, zs, run, final, hm, hus⟩ := hRet.run
    obtain ⟨e, ρ', O', hrun, hL, hrel, hgr, htc, hfe⟩ :=
      exp_fwd1 (hIdx M.core) (hInv M.core) hs hRg hFg hOw _ run
    have hst := status_of_values (hIdx M.core) hL final hm
    have hxs := exp_hxs hcx hRet.typed hk
    have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
        (Silmaril.Wasm.Execution.Core.invoke s (I.addrs.getD c.exports[w].core 0)
          ((lowerArgs c.exports[w].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))
        (t'.config s') :=
      internalP_steps (H := Nat) run
    have hty : zs.map (·.type) = ValTy.flatList x.ty.results := by
      have ht := run_typed_at hI hH.wf hk hxs steps final hm
      rw [(List.getElem?_eq_some_iff.mp hcx).2] at ht
      rw [hxty]
      exact ht
    obtain ⟨tr, htr, r⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := (linkHost impl).hr)
      (dispatch := (linkHost impl).dispatch) (B := M) (th := th) (K := K) (segs := segs)
      (rest := rest) hrun
    have s₄ : Step prof (linkHost impl).hr (linkHost impl).dispatch (coreCfg M th K segs rest e)
        .tau (retCfg M th K segs rest e zs) := Step.coreReturned rfl hst
    have hq : Quiet (P := P) (σ := σ) (tr ++ [.tau]) := (Quiet.of_core htr).append Quiet.tau
    refine ⟨tr ++ [.tau], _, Adequacy.steps_append r (.cons s₄ (.refl _)), hq.1,
      fun msg hm' => hq.2 _ hm', .inl ⟨{ M.ref with core := e.1 }, M.conts, zs, img ρ' O', rfl,
        hty, ?_, storeExt_core c I pl M.ref e.1,
        shold_after hH hO hL hrel hgr (reach_funcs' run)
          (RetAt.wellFormed hI ⟨nm, hcx⟩ hH.wf hRet),
        within_of_touch' htc hfe, grows_of_grow (grow_unmapH hgr)⟩⟩
    show liftArgs x.ty.results zs = some _
    rw [hxty]
    exact hus
  | trap hj hT =>
    obtain ⟨t', res, run, final, hout⟩ := hT.run
    obtain ⟨e, ρ', O', hrun, hL, hrel, hgr, htc, hfe⟩ :=
      exp_fwd1 (hIdx M.core) (hInv M.core) hs hRg hFg hOw _ run
    have hH' := shold_after hH hO hL hrel hgr (reach_funcs' run)
      (hT.wellFormed hI ⟨nm, hcx⟩ hH.wf)
    obtain ⟨tr, htr, r⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := (linkHost impl).hr)
      (dispatch := (linkHost impl).dispatch) (B := M) (th := th) (K := K) (segs := segs)
      (rest := rest) hrun
    cases res with
    | trap =>
      have hst := status_of_trap (hIdx M.core) hL final
      have s₄ : Step prof (linkHost impl).hr (linkHost impl).dispatch (coreCfg M th K segs rest e)
          (.trap .coreTrap) (StepDefs.trapCfg (coreCfg M th K segs rest e)) :=
        Step.coreTrap rfl hst
      refine ⟨tr ++ [.trap .coreTrap], _, Adequacy.steps_append r (.cons s₄ (.refl _)), ?_, ?_,
        .inr ⟨rfl, rfl, { M.ref with core := e.1 }, img ρ' O', rfl, rfl, hH',
          within_of_touch' htc hfe, grows_of_grow (grow_unmapH hgr)⟩⟩
      · intro ev hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact Adequacy.not_host_of_core htr ev hm'
        · simp at hm'
      · intro msg hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact Adequacy.not_trap_of_core htr _ hm'
        · simp at hm'
    | throw b => exact (not_result_throw hL final).elim
    | values cvs =>
      have hxs := exp_hxs hcx hT.typed hk
      have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
          (Silmaril.Wasm.Execution.Core.invoke s (I.addrs.getD c.exports[w].core 0)
            ((lowerArgs c.exports[w].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))
          (t'.config s') :=
        internalP_steps (H := Nat) run
      obtain ⟨w', hw'⟩ := answer_at hI hH.wf hk hxs steps (r := .values cvs) final
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (I.exports.get (opAt hI hk hxs).1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hw'
        dsimp only at hw'
        split_ifs at hw' with ht
        exact ht
      rw [opAt_type] at htyped
      obtain ⟨zs, hm⟩ : ∃ zs, cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs :=
        Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hty : zs.map (·.type) = ValTy.flatList x.ty.results := by
        have ht := run_typed_at hI hH.wf hk hxs steps final hm
        rw [(List.getElem?_eq_some_iff.mp hcx).2] at ht
        rw [hxty]
        exact ht
      have hn : liftArgs x.ty.results zs = none := by
        simp only [coreRes, hm, liftOutcome] at hout
        rw [hxty]
        revert hout
        cases liftArgs c.exports[w].ty.results zs with
        | none => intro _; rfl
        | some _ => intro h; cases h
      have hst := status_of_values (hIdx M.core) hL final hm
      have s₄ : Step prof (linkHost impl).hr (linkHost impl).dispatch (coreCfg M th K segs rest e)
          .tau (retCfg M th K segs rest e zs) := Step.coreReturned rfl hst
      have hq : Quiet (P := P) (σ := σ) (tr ++ [.tau]) := (Quiet.of_core htr).append Quiet.tau
      exact ⟨tr ++ [.tau], _, Adequacy.steps_append r (.cons s₄ (.refl _)), hq.1,
        fun msg hm' => hq.2 _ hm', .inl ⟨{ M.ref with core := e.1 }, M.conts, zs, img ρ' O',
          rfl, hty, hn, storeExt_core c I pl M.ref e.1, hH', within_of_touch' htc hfe,
          grows_of_grow (grow_unmapH hgr)⟩⟩

/-! ## The relation holds where `Linked2` starts its sessions -/

/-- The store of a simple instance is host free. -/
theorem hostFree_inst {c : Simple} {I : SInst} {cs : (E3 P).Store (CanonHost (E3 P))}
    {ci : (E3 P).Inst} (hF : CoreFacts (Pf := P) c I cs ci) : HostFree I.store := by
  intro a fi ha
  have hcse := hostsSat_cse hF
  rw [← hF.store] at ha
  have ha' : ((cs : Store (CanonHost (E3 P))).funcs[a]?).map (FuncInst.mapH (fun _ => 0)) =
      some fi :=
    (funcs_mapH_get (fun _ => 0) (cs : Store (CanonHost (E3 P))) a).symm.trans ha
  obtain ⟨fi₀, h5, rfl⟩ := Option.map_eq_some_iff.mp ha'
  obtain ⟨t, m, code⟩ := fi₀
  cases code with
  | wasm f => exact ⟨f, rfl⟩
  | host h => exact (hcse a _ h h5 rfl).elim

/-- **`SHold` at the start of `Linked2`'s sessions**: after every instantiation of `l.toRef`,
the exporter's instance store holds at placement `(1, [0, …))` (its `canon lift`s in instance
`1`, export `w` the function `w`), with the footprint of `rel4_init`'s exporter part. -/
theorem linked2_hold (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {I : SInst} (hI : l.exp.mod.IsInst I) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {m₀ : Machine.Config (core3P P) σ} {inst : InstId}
    {es : List (String × FuncId)}
    (hr : InstResult.instance m₀ inst es ∈
      instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef []) :
    ∃ F, SHold P l.exp I (1, List.range l.exp.exports.length) I.store m₀.ref F := by
  obtain ⟨hEg, hEi, hIg, hIi, har, hff, hW, hN, hn, hS⟩ := hl
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (σ := σ) hEg hEi hIg hIi
    har ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain rfl : I = Ie := NumModule.IsInst.unique hI hFe.isInst
  obtain ⟨Ii, hII⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hII
  have he : m₀ = afterLink P (reloc cse (Store.mapH Prod.fst r))
      (fun k => I.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀ := by
    have := hres prof (linkHost impl) h₀ _ hr
    simp only [InstResult.instance.injEq] at this
    exact this.1
  subst he
  have hg₀ : StoreGood I.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hII.1.choose_spec
  have hR := lready_init (P := P) (l := l) (Ie := I) (Ii := Ii) hg₀ hgu
    (linkStore_mapH hn hW hFe hrs hh) rfl hFe.isInst.1.choose_spec.ok hII.1.choose_spec.ok
  obtain ⟨ρp, Op, ρc, Oc, hR4⟩ := hR.rel
  have hfree := hostFree_inst hFe
  refine ⟨img ρp Op, ⟨ρp, Op, partRel_mapH hR4.rp, hR4.fnp, rfl⟩, fnPre_mapH hfree hR.fnE,
    hR.wfE, rfl, hfree, fun w x hx => ?_⟩
  have hwx := List.getElem?_eq_some_iff.mp hx
  have hwl : w < l.exp.exports.length := by
    have := hwx.1
    rwa [LinkedG.ofSimple_length] at this
  have hxty : x.ty = l.exp.exports[w].ty := by
    rw [← hwx.2]
    exact LinkedG.ofSimple_ty l.exp hwx.1 hwl
  have hlen : (liftedList (Pf := P) (fun k => I.addrs.getD k 0) ⟨1⟩ l.exp.exports).length =
      l.exp.exports.length := List.length_map _
  simp only [ArenaField.get?, ArenaField.funcs, Arena.get?_eq_getElem?, afterLink,
    Machine.Config.ref, Machine.Config.init, List.getD_eq_getElem?_getD, List.getElem?_range hwl, Option.getD_some]
  rw [List.getElem?_append_left (hlen ▸ hwl)]
  simp only [liftedList, List.getElem?_map, List.getElem?_eq_getElem hwl, Option.map_some,
    sAddr, Option.elim, hxty]
  rfl

/-! ## Packaged -/

/-- **A simple exporter meets R1, R2 and R5**, with data that holds where `Linked2` starts its
sessions, at placement instance `1` and function ids `0, 1, …`. -/
theorem simple_refFwd (P : Profile) {c : Simple} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) :
    ∃ d : (Simple.expSpec c I).RefData P, d.Frame ∧ d.Fwd ∧ d.Resume ∧
      ∀ (l : Linked2), l.exp = c → l.Adequate →
      ∀ (prof : ProfileKind) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
        (m₀ : Machine.Config (core3P P) σ) (inst : InstId) (es : List (String × FuncId)),
        InstResult.instance m₀ inst es ∈
          instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef [] →
        ∃ (pl : d.Pl) (F : CoreFoot), d.Hold pl I.store m₀.ref F ∧
          (∀ i, d.block pl i ↔ i = 1) ∧
          ∀ (w : Nat) (xe : SimpleExport), c.exports[w]? = some xe →
            d.addr pl w = I.addrs.getD xe.core 0 ∧ d.inst pl w = 1 ∧ d.fid pl w = w := by
  refine ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, simple_resume c I, ?_⟩
  intro l hlc hl prof σ impl h₀ m₀ inst es hr
  subst hlc
  obtain ⟨F, hF⟩ := linked2_hold P prof l hl hI impl h₀ hr
  refine ⟨(1, List.range l.exp.exports.length), F, hF, fun i => Iff.rfl, fun w xe hw => ?_⟩
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hw).1
  refine ⟨?_, rfl, ?_⟩
  · show sAddr l.exp I w = _
    simp [sAddr, hw]
  · show (List.range l.exp.exports.length).getD w 0 = w
    simp [List.getD_eq_getElem?_getD, List.getElem?_range hwl]

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
