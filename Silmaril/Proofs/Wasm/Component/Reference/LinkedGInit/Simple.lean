module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Back
public import Silmaril.Wasm.Component.Reference.LinkedG.Thms

/-!
# A simple exporter meets `InitS`; `Linked2` as an instance

* `initS_init`: `InitS` implies R4;
* `simple_initS`: a simple exporter's data meets `InitS` (`simple_init` of `LinkedGRef` with what
  the parent reads: the nested instantiation is a silent run, so it observes nothing and keeps the
  configuration's call records and the nesting depth; the instance's core store has no host
  functions (`hostsSat_cse`); the footprint's globals are the instance's; function ids
  `o + w` are distinct);
* `linked2_sess_specToRefG`: `Linked2`'s forward session theorem re-derived through `LinkedG`
  (`Linked2.toG`, `Linked2.sessSpec_toG_iff`, `Linked2.toG_toRef`) from `sess_specToRefB` with
  the simple exporter's data (`simple_frame`, `simple_fwd`, `simple_initS`, `simple_resume`,
  `simple_bounded`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile}

/-- **`InitS` implies R4.** -/
theorem initS_init {e : ExpSpec} {d : e.RefData P} (h : d.InitS) : d.Init := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, -, hc, hA⟩ := h prof impl M th outer k segs rest hcore hlock
  exact ⟨tr, m, pl, F, es, hs, hh, ht, hc, hA.lock, hA.ext, hA.hold, hA.block, hA.exports⟩

/-- **A simple exporter meets `InitS`**, under the hypotheses of `simple_init`. -/
theorem simple_initS {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (simpleData P c I).InitS := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨I', cs, ci, hF⟩ := coreFacts (Pf := P) hc hi
  obtain rfl : I = I' := NumModule.IsInst.unique hI hF.isInst
  obtain ⟨es, hes, htE, hrun⟩ := instantiateCall_simpleO (σ := σ) hF outer M hcore
  obtain ⟨tr, a, m', hsteps, hhost, htrap, -, ho, ha, hm'⟩ :=
    Reach.call (prof := prof) (hr := (linkHost impl).hr) (D := (linkHost impl).dispatch)
      (th := th) (c := .instantiate ⟨c.toRef, outer⟩ []) hrun hlock k segs rest
  subst ha hm'
  have hg : StoreGood I.store := storeGood_inst hS hI.1.choose_spec
  have hcs : Store.mapH (h0 _) (cs : Store (CanonHost (E3 P))) = I.store := hF.store
  let o := M.store.funcs.length
  let kk := M.store.insts.length
  have hfuncs : (nestCfg cs M (fun j => I.addrs.getD j 0) c).store.funcs =
      M.store.funcs ++ liftedList (fun j => I.addrs.getD j 0) ⟨kk⟩ c.exports := rfl
  have hinsts : (nestCfg cs M (fun j => I.addrs.getD j 0) c).store.insts =
      M.store.insts ++ [({ } : InstState)] := by
    simp [nestCfg, nestStore, liftStore, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc,
      ArenaField.insts]
  have hlenE : ∀ {w : Nat} {x : Export}, (SimpleI.ofSimple c).toComp.exports[w]? = some x →
      w < c.exports.length := fun hx => by
    have := (List.getElem?_eq_some_iff.mp hx).1
    rwa [LinkedG.ofSimple_length] at this
  refine ⟨tr, _, simplePl c kk o, img Ren.id (ownOf I.store), es, hsteps, hhost, htrap, ho, rfl,
    ⟨hlock, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [nestCfg, nestStore, liftStore, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc,
        ArenaField.insts]
  · refine ⟨⟨Ren.id, ownOf I.store, ?_, rfl, rfl⟩, ?_, hI.1.choose_spec.ok, rfl,
      hostFree_inst hF, fun w x hx => ?_⟩
    · show PartRel Ren.id (ownOf I.store) I.store
        (Store.mapH (h0 _) (cs : Store (CanonHost (E3 P))))
      rw [hcs]
      exact hg.partRel
    · show FnPre ({} : Store Nat) (Store.mapH (h0 _) (cs : Store (CanonHost (E3 P)))) I.store
      rw [hcs]
      exact fnPre_self _
    · have hwx := List.getElem?_eq_some_iff.mp hx
      have hwl : w < c.exports.length := hlenE hx
      have hxty : x.ty = c.exports[w].ty := by
        rw [← hwx.2]
        exact LinkedG.ofSimple_ty c hwx.1 hwl
      rw [simplePl_fid c kk o hwl]
      simp only [ArenaField.get?, ArenaField.funcs, Arena.get?_eq_getElem?,
        Machine.Config.ref_toCStore, hfuncs]
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      simp only [liftedList, List.getElem?_map, List.getElem?_eq_getElem hwl, Option.map_some,
        sAddr, Option.elim, hxty]
      rfl
  · intro i hi'
    have e : i = kk := hi'
    subst e
    rw [hinsts, List.length_append]
    exact ⟨le_refl _, Nat.lt_succ_self _⟩
  · intro w x hx
    have hwx := List.getElem?_eq_some_iff.mp hx
    have hwl : w < c.exports.length := hlenE hx
    have hname : x.name = c.exports[w].name := by
      rw [← hwx.2]
      exact exports_name_ofSimple c hwx.1 hwl
    refine ⟨?_, ({ } : InstState), ?_, rfl⟩
    · show List.lookup x.name es = some (.func ⟨(simplePl c kk o).2.getD w 0⟩)
      rw [simplePl_fid c kk o hwl, hname]
      exact lookup_funcExportL htE hes hc.names w hwl (hN _ (List.getElem_mem hwl))
    · show (nestCfg cs M (fun j => I.addrs.getD j 0) c).store.insts[kk]? = some ({ } : InstState)
      rw [hinsts]
      exact List.getElem?_concat_length
  · simp [nestCfg, nestStore, liftStore, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc,
      ArenaField.insts]
  · intro a fi h ha hc'
    exact hostsSat_cse hF a fi h ha hc'
  · intro a ha
    have h₁ : a < I.store.globals.length := ha
    rw [← hcs] at h₁
    exact h₁
  · intro w w' x x' hx hx' e
    have hw := hlenE hx
    have hw' := hlenE hx'
    have e' : (simplePl c kk o).2.getD w 0 = (simplePl c kk o).2.getD w' 0 := e
    rw [simplePl_fid c kk o hw, simplePl_fid c kk o hw'] at e'
    omega

/-- **`Linked2`'s forward session theorem through `LinkedG`**: under `Linked2.Adequate`, every
`Linked2.SessSpec` session from the instances' stores is a session behaviour of `l.toRef`, from
`sess_specToRefB` at `Linked2.toG l Ie` with the simple exporter's data. -/
theorem linked2_sess_specToRefG (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List IVal)} {Ie Ii : SInst}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) {outs : List (Option (List IVal))}
    {u' π' : Store Nat} (hspec : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls := by
  have hspec' : (l.toG Ie).SessSpec P Ii Ii.store Ie.store calls outs u' π' :=
    Linked2.sessSpec_toG_iff.2 hspec
  have h := sess_specToRefB (lg := l.toG Ie) P prof (d := simpleData P l.exp Ie)
    (initS_initSX (simple_initS hl.expGood hl.expInst hIe hl.splitOk.exp hl.namesOk.exp))
    (simple_frame l.exp Ie) (simple_fwd hl.expGood hIe) (simple_resume l.exp Ie)
    (simple_bounded l.exp Ie) (Linked2.toG_wireTy hl.wireTy Ie) hl.wireNodup hl.impGood
    hl.impInst hl.impArity hl.impFloatFree hl.splitOk.imp hl.namesOk.imp impl h₀ hIi hspec'
  unfold LinkedG.sessObs at h
  rw [Linked2.toG_toRef] at h
  exact h

/-! ## Packaged -/

theorem refAdeqS_refAdeqT {e : ExpSpec} (h : e.RefAdeqS P) : e.RefAdeqT P := by
  obtain ⟨d, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact ⟨d, h₁, h₂, h₃, initS_init h₄, h₅, h₆⟩

/-- **A simple exporter meets `RefAdeqS`.** -/
theorem simple_refAdeqS (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqS P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, LinkedGRound.simple_bwdT hc hI,
    simple_initS hc hi hI hS hN, simple_resume c I, simple_bounded c I⟩

/-- `sess_specToRefB` from `RefAdeqS`. -/
theorem sess_specToRefS (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqS P) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin lg.imp.exports.length × List IVal)} {Ii : SInst}
    (hI : lg.imp.mod.IsInst Ii) {outs : List (Option (List IVal))} {u' : Store Nat}
    {s' : lg.exp.St} (hspec : LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s') :
    refOuts outs ∈ LinkedG.sessObs prof lg impl h₀ calls := by
  obtain ⟨d, hFr, hFw, -, hInit, hRes, hB⟩ := he
  exact sess_specToRefB P prof (initS_initSX hInit) hFr hFw hRes hB hW hn hIg hIi hIa hff hS hNI impl h₀ hI hspec

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
