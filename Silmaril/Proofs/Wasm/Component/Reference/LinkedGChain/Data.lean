module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Track
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Call

/-!
# The reference data of a linked component as an exporter

`toExpData lg d Ii`: reference data (`ExpSpec.RefData`) for `lg.toExp Ii`, from reference data
`d` of its exporter.

* **Placement** (`ExpPl`): the exporter's placement `ple`, the importer's component instance
  `ii`, the importer's relocation `s₀` (the shared functions below its own), its store `ui` after
  instantiation, its ownership `Oc₀` of functions and globals, and the function id `fb` of its
  first lifted export. Export `w` of the linked component is the `canon lift` of the importer's
  core export, at core address `s₀.funcs.length + Ii.addrs.getD core 0`, instance `ii`, function
  id `fb + w`; the block is the exporter's block and `ii`.
* **The relation** (`HoldX`): the importer's static facts `StatB` and its invariant between
  calls at an explicit witness (`LReadyW`: `LReadyG` of `LinkedGRound` with the exporter's
  footprint `F` and the importer's renaming and ownership `ρc, Oc` explicit), the combined
  footprint `F ∪ img ρc Oc` inside the linked component's footprint `Fc`, `Fc` allocated, the
  importer's instance allowed to leave and the export instances' thread tables reusable. The
  host-code renaming `g`, its inverse `tr` and the shared functions `F₀` are chosen
  existentially, so that they can be re-chosen when the functions grow (R1).

Proved here: R6 (`toExpData_bounded`), R5 (`toExpData_resume`), and R1's `threads` and `lifted`
(`toExpData_threads`, `toExpData_lifted`), with the witness-level forms of `linv_readyG`,
`lready_afterG` and `lready_trapG` (`linv_readyW`, `lready_afterW`, `lready_trapW`) that the
forward round (`Fwd`) uses.
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
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile}

/-- `F` is contained in `G`. -/
structure SubFoot (F G : CoreFoot) : Prop where
  gl : ∀ a, F.gl a → G.gl a
  st : ∀ a, F.st a → G.st a
  ar : ∀ a, F.ar a → G.ar a

/-- **`LReadyG` at an explicit witness**: the exporter's footprint `F`, the importer's renaming
`ρc` and ownership `Oc`. -/
structure LReadyW {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (Ii : SInst) (s₀ ui : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (S : RefStore (E3 P)) (s : e.St) (u : Store Nat) (F : CoreFoot) (ρc : Ren) (Oc : Own) :
    Prop where
  rel : PartRel ρc Oc (reloc s₀ u) (Store.mapH g S.core)
  fn : Oc.fn = Oc₀.fn
  gl : Oc.gl = Oc₀.gl
  disj : FootDisj F ρc Oc S.core
  hold : d.Hold pl s S F
  fnC : FnPre s₀ (Store.mapH g S.core) u
  wfI : Ii.WellFormed u
  funcs : S.core.funcs = F₀
  ufuncs : u.funcs = ui.funcs
  good : SGoodSt (ownOf ui).fn u

/-- **The placement of a linked component**: the exporter's placement, the importer's instance,
relocation, store after instantiation, ownership, and the function id of its first export. -/
structure ExpPl (lg : LinkedG) (d : lg.exp.RefData P) where
  /-- The exporter's placement. -/
  ple : d.Pl
  /-- The importer's component instance. -/
  ii : Nat
  /-- The importer's relocation (the shared functions below its own). -/
  s₀ : Store Nat
  /-- The importer's store after instantiation. -/
  ui : Store Nat
  /-- The importer's ownership (functions and globals). -/
  Oc₀ : Own
  /-- The function id of the first lifted export. -/
  fb : Nat

/-- **The relation of a linked component** at placement `pl`, its state `st` (the importer's
store and the exporter's state), the component store `S` and the footprint `Fc`. -/
structure HoldX (lg : LinkedG) (d : lg.exp.RefData P) (Ii : SInst) (pl : ExpPl lg d)
    (st : Store Nat × lg.exp.St) (S : RefStore (E3 P)) (Fc : CoreFoot) : Prop where
  inv : ∃ (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat)
      (tr : Nat → CanonHost (E3 P)) (F : CoreFoot) (ρc : Ren) (Oc : Own),
    StatB P lg d pl.ple pl.ii Ii pl.s₀ pl.ui F₀ g tr pl.Oc₀ S.funcs (fun j => pl.fb + j) ∧
    LReadyW d pl.ple Ii pl.s₀ pl.ui F₀ g pl.Oc₀ S st.2 st.1 F ρc Oc ∧
    SubFoot (footUnion F (img ρc Oc)) Fc
  bound : Fc.Bounded (S.core : Store (CanonHost (E3 P)))
  imp : ∃ ι : InstState, S.insts[pl.ii]? = some ι ∧ ι.mayLeave = true
  exp : ∀ w : Nat, (∃ xe, lg.exp.comp.exports[w]? = some xe) →
    ∃ ι : InstState, S.insts[d.inst pl.ple w]? = some ι ∧ ThreadsOk ι

/-- The core address of export `w` of the linked component. -/
def expAddr (lg : LinkedG) (Ii : SInst) (s₀ : Store Nat) (w : Nat) : Nat :=
  s₀.funcs.length + Ii.addrs.getD ((lg.imp.exports[w]?).elim 0 (·.core)) 0

/-- **The reference data of a linked component** at the importer's core instance `Ii`. -/
def toExpData (lg : LinkedG) (d : lg.exp.RefData P) (Ii : SInst) :
    (lg.toExp Ii).RefData P where
  Pl := ExpPl lg d
  addr pl w := expAddr lg Ii pl.s₀ w
  inst pl _ := pl.ii
  fid pl w := pl.fb + w
  block pl i := d.block pl.ple i ∨ i = pl.ii
  Hold pl st S Fc := HoldX lg d Ii pl st S Fc

/-! ## The witness-level invariant -/

section W

variable {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {Ii : SInst} {s₀ ui : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat} {Oc₀ : Own}

theorem LReadyW.toG {S : RefStore (E3 P)} {s : e.St} {u : Store Nat} {F : CoreFoot} {ρc : Ren}
    {Oc : Own} (h : LReadyW d pl Ii s₀ ui F₀ g Oc₀ S s u F ρc Oc) :
    LReadyG d pl Ii s₀ ui F₀ g Oc₀ S s u :=
  ⟨⟨F, ρc, Oc, h.rel, h.fn, h.gl, h.disj, h.hold⟩, h.fnC, h.wfI, h.funcs, h.ufuncs, h.good⟩

/-- **`linv_readyG` at a witness, tracked**: `LInvG` at the export call, and `RelT` from the
store there with any footprint containing the combined one. -/
theorem linv_readyW {S : RefStore (E3 P)} {s : e.St} {u : Store Nat} {F : CoreFoot} {ρc : Ren}
    {Oc : Own} (hR : LReadyW d pl Ii s₀ ui F₀ g Oc₀ S s u F ρc Oc) {Fc : CoreFoot}
    (hsub : SubFoot (footUnion F (img ρc Oc)) Fc)
    (hO : ∀ a, a < ui.funcs.length → Oc₀.fn (s₀.funcs.length + a)) {f : Ii.F.Op}
    {xs : List Flat} (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat) :
    LInvG d pl Ii s₀ u F₀ g Oc₀ f s S F
      (S.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1) xs)
      (u, Ii.initThread f) ∧
    RelT s₀ g Oc₀ Fc S.core F
      (S.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1) xs)
      (u, Ii.initThread f) := by
  obtain ⟨fi, hfi, -⟩ := hR.wfI.export_type f.1
  have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
  have ha₀ : Ii.addr f.1 < ui.funcs.length := hR.ufuncs ▸ ha
  have hvs : ∀ v ∈ f.2.1, ∀ r, v ≠ .ref r := hxs ▸ ofFlat_scalar xs
  have hOc : Oc.fn (s₀.funcs.length + Ii.addr f.1) := by
    rw [hR.fn]
    exact hO _ ha₀
  have hg : SplitGood (Silmaril.Wasm.Execution.Core.invoke u (Ii.addr f.1) f.2.1) :=
    (sgood_invoke hR.good (show (ownOf ui).fn (Ii.addr f.1) from ha₀)
      (fun _ => goodVal_of_hasVal f.2.2)).splitGood
  have hL := linkSt_invoke hR.rel hR.fnC ha hOc hvs hg
  have hshared : (Store.mapH g S.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1) xs) =
      (Store.mapH g S.core, Silmaril.Wasm.SingleThreaded.Thread.pending
        (s₀.funcs.length + Ii.addr f.1) f.2.1) := by
    rw [hxs]
    rfl
  refine ⟨⟨⟨ρc, Oc, hshared ▸ hL, hR.fn, hR.gl, hR.disj⟩, hR.hold, rfl, hR.funcs, .refl⟩,
    ρc, Oc, hshared ▸ hL, hR.fn, hR.gl, hR.disj, within_refl _ _, ?_⟩
  exact ⟨fun a h => hsub.gl a h, fun a h => .inl (hsub.st a h), fun a h => .inl (hsub.ar a h)⟩

/-- **`lready_afterG` at a witness, tracked**: from `LInvG` and `RelT` along a call started from
`LReadyG`, the invariant between calls at the witness of `RelT`. -/
theorem lready_afterW {S S' : RefStore (E3 P)} {s s' : e.St} {u : Store Nat}
    (hR : LReadyG d pl Ii s₀ ui F₀ g Oc₀ S s u) {f : Ii.F.Op} {F : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u F₀ g Oc₀ f s' S' F y x)
    {Fc : CoreFoot} {σ₀ : Store (CanonHost (E3 P))} (hT : RelT s₀ g Oc₀ Fc σ₀ F y x) :
    ∃ (ρc : Ren) (Oc : Own), LReadyW d pl Ii s₀ ui F₀ g Oc₀ S' s' x.1 F ρc Oc ∧
      Fc.Within σ₀ S'.core ∧ Under Fc σ₀ (footUnion F (img ρc Oc)) := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD, hW, hU⟩ := hT
  obtain ⟨hwf, hfx, hsg⟩ := typing_after hR.wfI hR.good hR.ufuncs hI.run
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  rw [← hI.core] at hR0 hD hW
  have hfn' : FnPre s₀ (Store.mapH g S'.core) x.1 := by
    rw [hI.core]
    exact hL.fn
  exact ⟨ρc, Oc, ⟨hR0, hfn, hgl, hD, hI.hold, hfn', hwf, hI.core ▸ hI.funcs, hfx, hsg⟩, hW, hU⟩

/-- **`lready_trapG` at a witness, tracked**: after a trapped call, the invariant between calls
at the earlier store with the trapped core store, at the witness of `TrapT` (R5). -/
theorem lready_trapW (hRes : d.Resume) {S₀ : RefStore (E3 P)} {s s₁ : e.St} {u u₁ : Store Nat}
    (hR : LReadyG d pl Ii s₀ ui F₀ g Oc₀ S₀ s u) {f : Ii.F.Op}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (hT : TrapAtG d pl Ii s₀ u F₀ g Oc₀ f S₀ s₁ c u₁) {Fc : CoreFoot}
    {σ₀ : Store (CanonHost (E3 P))} (hTT : TrapT d pl s₀ g Oc₀ Fc σ₀ S₀ s₁ c u₁) :
    ∃ (F' : CoreFoot) (ρc : Ren) (Oc : Own),
      LReadyW d pl Ii s₀ ui F₀ g Oc₀ { S₀ with core := c } s₁ u₁ F' ρc Oc ∧
      Fc.Within σ₀ c ∧ Under Fc σ₀ (footUnion F' (img ρc Oc)) := by
  obtain ⟨S', F', ρc, Oc, hc, hf, hH', hrc, hfn, hgl, hD, hW, hU⟩ := hTT
  obtain ⟨-, hfnC, hfun, t, hrun⟩ := hT
  obtain ⟨F₁, -, -, -, -, -, -, hH₀⟩ := hR.rel
  obtain ⟨hwf, hfx, hsg⟩ := typing_after (x := (u₁, t)) hR.wfI hR.good hR.ufuncs hrun
  have hH : d.Hold pl s₁ { S₀ with core := S'.core } F' := hRes pl s s₁ S₀ S' F₁ F' hH₀ hH' hf
  rw [hc] at hH
  exact ⟨F', ρc, Oc, ⟨hrc, hfn, hgl, hD, hH, hfnC, hwf, hfun, hfx, hsg⟩, hW, hU⟩

/-- **`LReadyW` is kept by a change outside the core store**, the functions and the exporter's
block (R1). -/
theorem LReadyW.frame (hFr : d.Frame) {S S' : RefStore (E3 P)} {s : e.St} {u : Store Nat}
    {F : CoreFoot} {ρc : Ren} {Oc : Own} (hR : LReadyW d pl Ii s₀ ui F₀ g Oc₀ S s u F ρc Oc)
    (hc : S'.core = S.core) (hf : S'.funcs = S.funcs)
    (hb : ∀ i, d.block pl i → S'.insts[i]? = S.insts[i]?) :
    LReadyW d pl Ii s₀ ui F₀ g Oc₀ S' s u F ρc Oc := by
  have hH' : d.Hold pl s S' F :=
    hFr.agree pl s S S' F hR.hold (agree_of_eq F hc) (by rw [hf]) hb
  have hrc := hR.rel
  have hD := hR.disj
  have hfC := hR.fnC
  have hfu := hR.funcs
  rw [← hc] at hrc hD hfC hfu
  exact ⟨hrc, hR.fn, hR.gl, hD, hH', hfC, hR.wfI, hfu, hR.ufuncs, hR.good⟩

end W

/-! ## R1 (threads, lifted), R5, R6 -/

section Data

variable {lg : LinkedG} {d : lg.exp.RefData P} {Ii : SInst}

theorem toComp_exports_get {w : Nat} {x : Export} (h : lg.toComp.exports[w]? = some x) :
    ∃ hw : w < lg.imp.exports.length, x.ty = lg.imp.exports[w].ty := by
  change (List.mapIdx _ lg.imp.exports)[w]? = some x at h
  rw [List.getElem?_mapIdx] at h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hw, rfl⟩ := List.getElem?_eq_some_iff.mp hy
  exact ⟨hw, rfl⟩

/-- **R6 for a linked component.** -/
theorem toExpData_bounded : (toExpData lg d Ii).Bounded :=
  fun _ _ _ _ h => h.bound

/-- **R5 for a linked component**, from the exporter's R5. -/
theorem toExpData_resume (hRes : d.Resume) : (toExpData lg d Ii).Resume := by
  intro pl st st' S₀ S' F₀c F'c h₀ h' hf
  obtain ⟨F₀, g, tr, F, ρc, Oc, hS, hR, hsub⟩ := h'.inv
  obtain ⟨_, _, _, F₁, _, _, _, hR₀, _⟩ := h₀.inv
  have hH : d.Hold pl.ple st'.2 { S₀ with core := S'.core } F :=
    hRes pl.ple st.2 st'.2 S₀ S' F₁ F hR₀.hold hR.hold hf
  refine ⟨⟨F₀, g, tr, F, ρc, Oc, ?_, ?_, hsub⟩, h'.bound, h₀.imp, h₀.exp⟩
  · show StatB P lg d pl.ple pl.ii Ii pl.s₀ pl.ui F₀ g tr pl.Oc₀ S₀.funcs _
    rw [← hf]
    exact hS
  · exact ⟨hR.rel, hR.fn, hR.gl, hR.disj, hH, hR.fnC, hR.wfI, hR.funcs, hR.ufuncs, hR.good⟩

/-- **R1's `threads` for a linked component**: the thread table of the importer's instance does
not matter. -/
theorem toExpData_threads (hFr : d.Frame) (pl : (toExpData lg d Ii).Pl)
    (st : (lg.toExp Ii).St) (S : RefStore (core3P P)) (Fc : CoreFoot) (w : Nat) (ι : InstState)
    (t : Silmaril.Wasm.Component.Runtime.Table ThreadId)
    (h : (toExpData lg d Ii).Hold pl st S Fc) (hι : S.insts[(toExpData lg d Ii).inst pl w]? = some ι) :
    (toExpData lg d Ii).Hold pl st
      { S with insts := S.insts.set ((toExpData lg d Ii).inst pl w) { ι with threads := t } } Fc := by
  change S.insts[pl.ii]? = some ι at hι
  change HoldX lg d Ii pl st { S with insts := S.insts.set pl.ii { ι with threads := t } } Fc
  obtain ⟨F₀, g, tr, F, ρc, Oc, hS, hR, hsub⟩ := h.inv
  have hout := hS.out
  have hR' := hR.frame hFr (S' := { S with insts := S.insts.set pl.ii { ι with threads := t } })
    rfl rfl (fun i hi => List.getElem?_set_ne (fun e : pl.ii = i => hout (by rw [e]; exact hi)))
  refine ⟨⟨F₀, g, tr, F, ρc, Oc, hS, hR', hsub⟩, h.bound, ?_, ?_⟩
  · obtain ⟨ι', hι', hl⟩ := h.imp
    rw [hι] at hι'
    cases hι'
    exact ⟨_, List.getElem?_set_self (lt_of_getElem? hι), hl⟩
  · intro w' hw'
    obtain ⟨xe, hxe⟩ := hw'
    obtain ⟨-, hblk⟩ := hFr.lifted pl.ple st.2 S F w' xe hR.hold hxe
    have hne : pl.ii ≠ d.inst pl.ple w' := fun e => hout (by rw [e]; exact hblk)
    obtain ⟨ι', h₁, h₂⟩ := h.exp w' ⟨xe, hxe⟩
    exact ⟨ι', (List.getElem?_set_ne hne).trans h₁, h₂⟩

/-- **R1's `lifted` for a linked component**: export `w` is the importer's lift of its core
export, at function id `fb + w`. -/
theorem toExpData_lifted (pl : (toExpData lg d Ii).Pl) (st : (lg.toExp Ii).St)
    (S : RefStore (core3P P)) (Fc : CoreFoot) (w : Nat) (x : Export)
    (h : (toExpData lg d Ii).Hold pl st S Fc) (hx : (lg.toExp Ii).comp.exports[w]? = some x) :
    ArenaField.funcs.get? S.toCStore ⟨(toExpData lg d Ii).fid pl w⟩ =
      some (.lifted ((toExpData lg d Ii).addr pl w) (witFt x.ty) {}
        ⟨(toExpData lg d Ii).inst pl w⟩) ∧
    (toExpData lg d Ii).block pl ((toExpData lg d Ii).inst pl w) := by
  obtain ⟨hw, hty⟩ := toComp_exports_get hx
  obtain ⟨F₀, g, tr, F, ρc, Oc, hS, -, -⟩ := h.inv
  refine ⟨?_, .inr rfl⟩
  have hl := hS.lifted ⟨w, hw⟩
  simp only [ArenaField.get?, ArenaField.funcs, Arena.get?_eq_getElem?]
  show S.funcs[pl.fb + w]? = some (.lifted (expAddr lg Ii pl.s₀ w) (witFt x.ty) {} ⟨pl.ii⟩)
  rw [hl, hty]
  simp only [expAddr, List.getElem?_eq_getElem hw, Option.elim_some]
  rfl

end Data

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
