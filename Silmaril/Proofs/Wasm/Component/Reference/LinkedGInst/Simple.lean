module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Sess

/-!
# A simple exporter meets `InitU`; `Linked2` as an instance

* `simple_initU`: a simple exporter's data meets `InitU` (`simple_initS` of `LinkedGInit`, the
  nested instantiation a big-step run, hence a live run, keeping the waiting threads);
* `simple_refAdeqU`: a simple exporter meets `RefAdeqU`;
* `linked2_sessObs_eqU`, `linked2_sessAdequacy_fullU`: `Linked2.sessObs_eq` and
  `Linked2.sessAdequacy_full` re-derived through `LinkedG` (`Linked2.toG`, `Linked2.toG_toRef`,
  `Linked2.sessSpec_toG_iff`, `Linked2.sessMoves_toG_iff`) from `sessObs_eqU` and
  `sessAdequacy_fullU` with the simple exporter's data.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
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

/-- **A simple exporter meets `InitU`**, under the hypotheses of `simple_init`: `simple_initS`
with the live run of `ReachL.call`. -/
theorem simple_initU {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (simpleData P c I).InitU := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨I', cs, ci, hF⟩ := coreFacts (Pf := P) hc hi
  obtain rfl : I = I' := NumModule.IsInst.unique hI hF.isInst
  obtain ⟨es, hes, htE, hrun⟩ := instantiateCall_simpleO (σ := σ) hF outer M hcore
  obtain ⟨tr, a, m', hsteps, hhost, htrap, -, ho, ha, hm'⟩ :=
    ReachL.call (prof := prof) (hr := (linkHost impl).hr) (D := (linkHost impl).dispatch)
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
  refine ⟨tr, _, simplePl c kk o, img Ren.id (ownOf I.store), es, lrun_liveDet hsteps, hhost, htrap, ho, rfl,
    ⟨hlock, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · rfl

/-- **A simple exporter meets `RefAdeqU`.** -/
theorem simple_refAdeqU (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqU P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, LinkedGInv.simple_bwdF hc hI,
    simple_initU hc hi hI hS hN, simple_resume c I, simple_bounded c I⟩

/-- `Linked2.sessObs` is `LinkedG.sessObs` of `Linked2.toG`. -/
theorem linked2_sessObs_toG (prof : ProfileKind) (l : Linked2) (Ie : SInst) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal)) :
    LinkedG.sessObs prof (l.toG Ie) impl h₀ calls = Linked2.sessObs prof l impl h₀ calls := by
  unfold LinkedG.sessObs Linked2.sessObs
  rw [Linked2.toG_toRef]

/-- **`Linked2.sessObs_eq` through `LinkedG`**. -/
theorem linked2_sessObs_eqU (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {Ie Ii : SInst} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' π' : Store Nat),
        Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' ∧ o = refOuts outs} := by
  have h := sessObs_eqU (lg := l.toG Ie) P prof
    (refAdeqU_refAdeqUX (simple_refAdeqU P hl.expGood hl.expInst hIe hl.splitOk.exp
      hl.namesOk.exp))
    (Linked2.toG_wireTy hl.wireTy Ie) hl.wireNodup hl.impGood hl.impInst hl.impArity
    hl.impFloatFree hl.splitOk.imp hl.namesOk.imp impl h₀ calls ht hIi
  rw [linked2_sessObs_toG] at h
  rw [h]
  ext o
  exact ⟨fun ⟨outs, u', π', hs, e⟩ => ⟨outs, u', π', Linked2.sessSpec_toG_iff.1 hs, e⟩,
    fun ⟨outs, u', π', hs, e⟩ => ⟨outs, u', π', Linked2.sessSpec_toG_iff.2 hs, e⟩⟩

/-- **`Linked2.sessAdequacy_full` through `LinkedG`**. -/
theorem linked2_sessAdequacy_fullU (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)} := by
  obtain ⟨Ie, cs, ci, hF⟩ := coreFacts (Pf := P) hl.expGood hl.expInst
  have h := sessAdequacy_fullU (lg := l.toG Ie) P prof
    (refAdeqU_refAdeqUX (simple_refAdeqU P hl.expGood hl.expInst hF.isInst hl.splitOk.exp
      hl.namesOk.exp))
    (Linked2.toG_adeq P hl hF.isInst)
    (Linked2.toG_wireTy hl.wireTy Ie) hl.wireNodup hl.impGood hl.impInst hl.impArity
    hl.impFloatFree hl.splitOk.imp hl.namesOk.imp impl h₀ calls ht
  rw [linked2_sessObs_toG] at h
  rw [h]
  ext o
  exact ⟨fun ⟨outs, e, hlen, hm⟩ =>
      ⟨outs, e, hlen, (Linked2.sessMoves_toG_iff P l Ie calls outs).1 hm⟩,
    fun ⟨outs, e, hlen, hm⟩ =>
      ⟨outs, e, hlen, (Linked2.sessMoves_toG_iff P l Ie calls outs).2 hm⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
