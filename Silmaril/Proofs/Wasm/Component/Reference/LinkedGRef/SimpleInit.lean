module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.SimpleBwd
public import Silmaril.Proofs.Wasm.Component.Reference.InstLink
public import Silmaril.Proofs.Wasm.Component.Reference.StartInst
public import Silmaril.Proofs.Wasm.Component.Reference.SplitInit

/-!
# R4 for a simple exporter: nested instantiation at a general placement

`simple_init`: `simpleData` meets `RefData.Init`. The nested instantiation of `c.toRef`
(`Call.instantiate ⟨c.toRef, outer⟩ []`, any enclosing frames `outer`) from a configuration with
an empty core store (any component instances and component functions before it) allocates the
next component instance `k = M.store.insts.length`, instantiates the core module and lifts
export `w` into component function `o + w` (`o = M.store.funcs.length`):

* `toRefDefs_runO`, `instantiateCall_simpleO`: `toRefDefs_run` and `instantiateCall_simple'` with
  `o` component functions before the child (`exportsDefs_runO`);
* `instantiate_steps`: the late-bound call in the parent's program is a machine run with `tau`
  and observation labels only, ending in the parent's continuation;
* `simple_init`: R4, at the placement `(k, [o, o + 1, …])`, the relation holding with the
  identity renaming and the ownership of the instance store (`StoreGood.partRel`);
* `simple_refFwdBwd`, `simple_refAdeq`: R1, R2, R3, R5 (with the `Linked2` start), and R1–R5.

Beyond `Simple.Good` and `IsInst`, R4 uses `Simple.Inst` (the core export names, for
`CoreFacts`), `Linked2.ModSplitOk` (the split fragment, for `StoreGood`) and export names that
are not generated type names (`tag "t" n`), as `Linked2.NamesOk` does: the export map of
`c.toRef` holds the type exports `tag "t" n` too, and the name of an export equal to one of them
could be found as that type.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The nested instantiation after `o` component functions -/

section Offset

variable {Pf : Profile} {σ : Type} {R : Recurse (core3P Pf) σ}
  {inst : InstId} {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-- **The definitions of `c.toRef` run silently** from a store with the empty core store
(`toRefDefs_run` without `funcs = []`): export `k` is the lifted function `o + k`. -/
theorem toRefDefs_runO {c : Simple} {I : SInst}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.core = (core3P Pf).empty _) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {} c.toRef) cfg sc'
        { cfg with core := cs, store :=
            liftStore cfg.store (liftedList (fun k => I.addrs.getD k 0) inst c.exports) } ∧
      funcExports sc'.exports =
        c.exports.mapIdx (fun k x => (x.name, ⟨cfg.store.funcs.length + 0 + k⟩)) := by
  have hp : (core3P Pf).prepare? cfg.core c.mod.mod [] = some (cs, ci, none) := by
    rw [hcore]
    exact hF.prepare
  have h₁ := instDef_coreModule (R := R) (inst := inst) (outer := outer) (args := args) {}
    c.mod.mod
  have h₂ := instDef_coreInstance (R := R) (inst := inst) (outer := outer) (args := args)
    { frame := { (Frame.empty : Frame (core3P Pf)) with coreModules := [] ++ [c.mod.mod] },
      exports := [] } cfg rfl hF.imports hp
  have hinv : ExpInv ((core3P Pf).exports ci) 0 (coreFrame c.mod.mod ((core3P Pf).exports ci)) :=
    ⟨rfl, rfl, rfl⟩
  have hs : cfg.store.funcs.length = cfg.store.funcs.length + 0 := rfl
  obtain ⟨sc', hr, hx⟩ := exportsDefs_runO (R := R) (inst := inst) (outer := outer)
    (args := args) c.mod cfg.store.funcs.length (fun k => I.addrs.getD k 0) c.exports 0
    { frame := coreFrame c.mod.mod ((core3P Pf).exports ci), exports := [] }
    { cfg with core := cs } hinv hs hF.lookup
  refine ⟨sc', ?_, hx⟩
  unfold Simple.toRef
  exact TRuns.foldlM_append (TRuns.foldlM_cons (TRuns.of_eq cfg h₁)
    (TRuns.foldlM_cons h₂ (TRuns.foldlM_nil _ _))) hr

/-- **The nested instantiation of an import-free simple component** after `o` component
functions (`instantiateCall_simple'` without `funcs = []`): the export map of functions and
generated type names, export `k` the lifted function `o + k`. -/
theorem instantiateCall_simpleO {c : Simple} {I : SInst}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (outer : List (Frame (core3P Pf)))
    (cfg : Machine.Config (core3P Pf) σ) (hcore : cfg.core = (core3P Pf).empty _) :
    ∃ es, funcExports es =
        c.exports.mapIdx (fun k x => (x.name, ⟨cfg.store.funcs.length + k⟩)) ∧ TagOrFunc es ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ [] : P (core3P Pf) σ (Ret (core3P Pf))) cfg
        (.items es)
        (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := by
  obtain ⟨sc', hr, hx⟩ := toRefDefs_runO (R := callRecurse)
    (inst := nextInst cfg.store) (outer := outer)
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore
  have hmap : funcExports sc'.exports =
      c.exports.mapIdx (fun k x => (x.name, ⟨cfg.store.funcs.length + k⟩)) := by
    rw [hx]
    simp only [Nat.add_zero]
    rfl
  have ht : TagOrFunc sc'.exports :=
    SRuns.rets (Q := fun sc : Scope (core3P Pf) => TagOrFunc sc.exports) hr
      (foldlM_rets (E := core3P Pf) (R := callRecurse) (inst := nextInst cfg.store) (outer := outer)
        (args := []) c.toRef {} (expName_toRef c) TagOrFunc.nil)
  refine ⟨sc'.exports, hmap, ht, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  have hr' : TRuns (List.foldlM (instantiateDef callRecurse (nextInst cfg.store) outer []) {}
      c.toRef) { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } sc'
      (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := hr
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr' (TRuns.pure _ _))

end Offset

/-! ## The late-bound call on the machine -/

variable {P : Profile}

/-- **A late-bound instantiation call in the parent's program is a machine run**: a silent
run of the dispatcher's program of `Call.instantiate cl vs`, in focus as `callRet … >>= k` on
thread `th`, is a machine run with `tau` and observation labels only, to `k` of its items. -/
theorem instantiate_steps {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
    {M m' : Machine.Config (core3P P) σ} {th : Option ThreadId} {cl : Closure (core3P P)}
    {vs : Exports (core3P P)} {es : List (String × ItemVal (core3P P))}
    {k : Ret (core3P P) → Canon.P (core3P P) σ (Ret (core3P P))}
    {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)}
    (h : TRuns (instantiateCallProg cl vs : Canon.P (core3P P) σ (Ret (core3P P))) M (.items es) m')
    (hl : M.store.lockdown = false) :
    ∃ tr : List (Label (core3P P) σ),
      Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
        { M with ctl := ⟨th, .prog (callRet (.instantiate cl vs) >>= k), segs⟩ :: rest } tr
        { m' with ctl := ⟨th, .prog (k (.items es)), segs⟩ :: rest } ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) := by
  obtain ⟨tr, hr, hq⟩ := SRuns.runsQ (dispatch := (linkHost impl).dispatch) h th
  have hc : RunsQ (linkHost impl).dispatch th
      (callRet (.instantiate cl vs) : Canon.P (core3P P) σ (Ret (core3P P))) M
      (.tau :: (tr ++ [.tau])) (.items es) m' := by
    unfold callRet perform Prog.lift
    exact RunsQ.call hr (RunsQ.pure _ _)
  have hq' : SRuns.Quiet (.tau :: (tr ++ [.tau]) : List (Label (core3P P) σ)) := by
    intro l hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact .inl rfl
    rcases List.mem_append.1 hl' with hl' | hl'
    · exact hq l hl'
    · rw [List.mem_singleton.1 hl']
      exact .inl rfl
  refine ⟨_, (hc.lrun (prof := prof) (hr := (linkHost impl).hr) hl k segs rest).steps, ?_, ?_⟩
  · intro ev hm
    rcases hq' _ hm with e | ⟨o, e⟩ <;> cases e
  · intro r hm
    rcases hq' _ hm with e | ⟨o, e⟩ <;> cases e

/-! ## R4 -/

theorem fnPre_self (π : Store Nat) : FnPre ({} : Store Nat) π π := by
  intro a fi ha
  rwa [reloc_empty] at ha

theorem exports_name_ofSimple (c : Simple) {w : Nat}
    (h₁ : w < (SimpleI.ofSimple c).toComp.exports.length) (h₂ : w < c.exports.length) :
    (SimpleI.ofSimple c).toComp.exports[w].name = c.exports[w].name := by
  simp [SimpleI.ofSimple, SimpleI.toComp]

/-- The placement of a simple exporter instantiated at component instance `k` after `o`
component functions. -/
def simplePl (c : Simple) (k o : Nat) : Nat × List Nat := (k, List.range' o c.exports.length)

theorem simplePl_fid (c : Simple) (k o : Nat) {w : Nat} (hw : w < c.exports.length) :
    (simplePl c k o).2.getD w 0 = o + w := by
  simp [simplePl, List.getD_eq_getElem?_getD, List.getElem?_range' hw]

/-- **R4 for a simple exporter**: its nested instantiation (any enclosing frames, from any
configuration with an empty core store) runs, without host events or traps, to its exports:
the relation holds at the placement `simplePl c k o` (component instance
`k = M.store.insts.length`, function ids `o + w` for `o = M.store.funcs.length`), whose
instance is new, export `w` named as in the IR component and bound to function `o + w`, the
instance's thread table empty. -/
theorem simple_init {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (simpleData P c I).Init := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨I', cs, ci, hF⟩ := coreFacts (Pf := P) hc hi
  obtain rfl : I = I' := NumModule.IsInst.unique hI hF.isInst
  obtain ⟨es, hes, htE, hrun⟩ := instantiateCall_simpleO (σ := σ) hF outer M hcore
  obtain ⟨tr, hsteps, hhost, htrap⟩ := instantiate_steps (th := th) (k := k) (segs := segs)
    (rest := rest) prof impl hrun hlock
  have hg : StoreGood I.store := storeGood_inst hS hI.1.choose_spec
  have hcs : Store.mapH (h0 _) (cs : Store (CanonHost (E3 P))) = I.store := hF.store
  let o := M.store.funcs.length
  let kk := M.store.insts.length
  have hfuncs : (nestCfg cs M (fun j => I.addrs.getD j 0) c).store.funcs =
      M.store.funcs ++ liftedList (fun j => I.addrs.getD j 0) ⟨kk⟩ c.exports := rfl
  have hinsts : (nestCfg cs M (fun j => I.addrs.getD j 0) c).store.insts = M.store.insts ++ [({ } : InstState)] := by
    simp [nestCfg, nestStore, liftStore, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc,
      ArenaField.insts]
  have hcore' : (nestCfg cs M (fun j => I.addrs.getD j 0) c).core = cs := rfl
  refine ⟨tr, _, simplePl c kk o, img Ren.id (ownOf I.store), es, hsteps, hhost, htrap, rfl, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact hlock
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
      have hwl : w < c.exports.length := by
        have := hwx.1
        rwa [LinkedG.ofSimple_length] at this
      have hxty : x.ty = c.exports[w].ty := by
        rw [← hwx.2]
        exact LinkedG.ofSimple_ty c hwx.1 hwl
      have hlen : (liftedList (Pf := P) (fun j => I.addrs.getD j 0) ⟨kk⟩ c.exports).length =
          c.exports.length := List.length_map _
      rw [simplePl_fid c kk o hwl]
      simp only [ArenaField.get?, ArenaField.funcs, Arena.get?_eq_getElem?, Machine.Config.ref_toCStore,
        hfuncs]
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
    have hwl : w < c.exports.length := by
      have := hwx.1
      rwa [LinkedG.ofSimple_length] at this
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

/-! ## Packaged -/

/-- **A simple exporter meets R1, R2, R3 and R5**, with data that holds where `Linked2` starts
its sessions (`simple_refFwd` with R3). -/
theorem simple_refFwdBwd (P : Profile) {c : Simple} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) :
    ∃ d : (Simple.expSpec c I).RefData P, d.Frame ∧ d.Fwd ∧ d.Bwd ∧ d.Resume ∧
      ∀ (l : Linked2), l.exp = c → l.Adequate →
      ∀ (prof : ProfileKind) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
        (m₀ : Machine.Config (core3P P) σ) (inst : InstId) (es : List (String × FuncId)),
        InstResult.instance m₀ inst es ∈
          instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef [] →
        ∃ (pl : d.Pl) (F : CoreFoot), d.Hold pl I.store m₀.ref F ∧
          (∀ i, d.block pl i ↔ i = 1) ∧
          ∀ (w : Nat) (xe : SimpleExport), c.exports[w]? = some xe →
            d.addr pl w = I.addrs.getD xe.core 0 ∧ d.inst pl w = 1 ∧ d.fid pl w = w := by
  refine ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, simple_bwd hc hI,
    simple_resume c I, ?_⟩
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

/-- **A simple exporter meets the reference interface** (R1–R5), in the split fragment, with
export names that are not generated type names. -/
theorem simple_refAdeq (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeq P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, simple_bwd hc hI,
    simple_init hc hi hI hS hN, simple_resume c I⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
