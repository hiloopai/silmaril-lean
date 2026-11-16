module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.InstReloc
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs

/-!
# The instantiation of `HLinked2.toRef`

The parent `l.toRef` of a linked component with host imports (`HLinked2.Defs`) is instantiated
from the host functions of `l.host` (`hostConfig`), import `k` bound to host function `k`
(`importArgs`). This is `InstLink`'s instantiation of `Linked2.toRef` with the host prefix:

* the parent's import definitions push the host functions `0, …, k - 1` (`importsDefs_run`,
  `k = host.length`), and the root pre-checks pass (`argsCompleteH`, `precheckH`);
* the exporter is instantiated after them (`instantiateCall_simpleO` at `o = k`): its export
  `i` is the lifted function `k + i`;
* the aliases of its wired exports, then the importer's nested instantiation over the shared
  store (`instantiateCall_simpleI'`) with import `n` bound to `l.fid n`: the exporter's lifted
  function `k + wire[n]` for a wired import, host function `n - wire.length` otherwise
  (`importsBoundH`);
* the aliases of the importer's exports and the exports: export `i` is the importer's lifted
  function `k + exp.exports.length + i` (`HLinked2.exportMap`).

`instBehavioursH_toRef`: the only result of instantiating `l.toRef` is the instance at
`afterLinkH`. `coreFactsH_of_inst`: the importer's core facts in the shared store, for the
relocation `l.fid` (an instance of `coreFactsL_of_inst`, which is generic in the lowered
callees). `instBehavioursH_inst` assembles both from `Inst` of the children, and
`hlinked2_instantiates` from `HLinked2.Adequate`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

variable {Pf : Profile} {σ : Type}

/-! ## The layout -/

theorem wire_le {l : HLinked2} (hW : l.WireTy) : l.wire.length ≤ l.imp.imports.length :=
  hW.shape.2

theorem imports_length {l : HLinked2} (hW : l.WireTy) :
    l.imp.imports.length = l.wire.length + l.host.length := by
  have h := congrArg List.length hW.shape.1
  rw [List.length_drop] at h
  have := hW.shape.2
  omega

/-- Host import `i` is the importer's import `wire.length + i`. -/
theorem host_getElem {l : HLinked2} (hW : l.WireTy) (i : Nat) (hi : i < l.host.length) :
    l.host[i] = l.imp.imports[l.wire.length + i]'(by rw [imports_length hW]; omega) := by
  have e := hW.shape.1
  have hi' : i < (l.imp.imports.drop l.wire.length).length := by rw [e]; exact hi
  have h : (l.imp.imports.drop l.wire.length)[i]'hi' = l.imp.imports[l.wire.length + i]'(by
      rw [imports_length hW]; omega) := List.getElem_drop ..
  exact (List.getElem_of_eq e hi').symm.trans h

/-- The host import names are distinct when the importer's are. -/
theorem host_nodup {l : HLinked2} (hW : l.WireTy) (hn : (l.imp.imports.map (·.1)).Nodup) :
    (l.host.map (·.1)).Nodup := by
  rw [← hW.shape.1, List.map_drop]
  exact hn.sublist (List.drop_sublist _ _)

/-- The instantiation arguments of the importer in the parent: import `n` bound to `l.fid n`. -/
noncomputable def linkArgsH (l : HLinked2) : Exports (core3P Pf) :=
  l.imp.imports.mapIdx fun n p => (p.1, .func (l.fid n))

/-! ## The definitions of the parent -/

/-- `l.toRef` after its import definitions. -/
def tailH (l : HLinked2) : List (Syntax.Definition Silmaril.Wasm.Module) :=
  [.component l.exp.toRef, .component l.imp.toRef, .instance_ (.instantiate 0 [])] ++
    (l.wire.map fun w => .alias (.export_ 0 (l.toL2.expName w) .func)) ++
    [.instance_ (.instantiate 1 (l.imp.imports.mapIdx fun n p =>
      (p.1, ⟨.func, l.importFid n⟩)))] ++
    (l.imp.exports.map fun x => .alias (.export_ 1 x.name .func)) ++
    (l.imp.exports.mapIdx fun i x =>
      .export_ { name := x.name } ⟨.func, l.host.length + l.wire.length + i⟩ none)

theorem toRef_eqH (l : HLinked2) : l.toRef = (SimpleI.importsDefs l.host 0).1 ++ tailH l := by
  simp only [HLinked2.toRef, tailH, List.append_assoc]

theorem noImport_tailH (l : HLinked2) : NoImport (tailH l) := by
  intro d hd n x e
  simp only [tailH, List.mem_append, List.mem_cons, List.mem_map, List.mem_mapIdx,
    List.not_mem_nil, or_false] at hd
  rcases hd with ((((rfl | rfl | rfl) | ⟨_, -, rfl⟩) | rfl) | ⟨_, -, rfl⟩) | ⟨_, _, rfl⟩ <;>
    cases e

theorem funcExports_append' (a b : Exports (core3P Pf)) :
    funcExports (a ++ b) = funcExports a ++ funcExports b := by
  simp only [funcExports, List.filterMap_append]

section Link

variable {D : Call (core3P Pf) → P (core3P Pf) σ (Ret (core3P Pf))}

/-- **The definitions of `l.toRef` run** from a store with the root instance, the empty core
store and the host functions of `l.host`: the host imports, the closures, the exporter's nested
instantiation (instance `1`, after the host functions), the aliases of the wired exports, the
importer's nested instantiation (instance `2`) with import `n` bound to `l.fid n`, the aliases
of the importer's exports and the exports. -/
theorem toRefH_run {l : HLinked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.toL2.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.fid addrI csi cii)
    (cfg : Machine.Config (core3P Pf) σ) (hcore : cfg.core = (core3P Pf).empty _)
    (hfuncs : cfg.store.funcs = hostList 0 l.host) (hinsts : cfg.store.insts = [{}]) :
    ∃ sc', ORuns D (List.foldlM (instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ []
        (importArgs l.host)) {} l.toRef) cfg [] sc'
        { cfg with core := csi, store :=
            linkStore cse csi (fun k => Ie.addrs.getD k 0) addrI l.toL2 cfg.store } ∧
      funcExports sc'.exports = l.exportMap := by
  have hHn := host_nodup hW hIn
  have hlenI := imports_length hW
  -- the host imports
  obtain ⟨scA, rA, ⟨newA, hfA⟩, -, hxA⟩ := importsDefs_run (R := (callRecurse :
      Recurse (core3P Pf) σ)) (inst := ⟨0⟩) (outer := []) (args := importArgs l.host)
    l.host 0 {} cfg fun j hj =>
      ⟨by rw [Nat.zero_add]; exact importArgs_lookup hHn j hj,
       by rw [Nat.zero_add]; exact hostList_get hfuncs j hj⟩
  have hxA' : funcExports scA.exports = [] := hxA
  have hcA : scA.frame.components = [] := by rw [hfA]; rfl
  have hiA : scA.frame.instances = [] := by rw [hfA]; rfl
  have hfA' : scA.frame.funcs = (List.range' 0 l.host.length).map FuncId.mk := by
    rw [hfA]; exact List.nil_append _
  -- the closures
  let clE : Closure (core3P Pf) := ⟨l.exp.toRef, [scA.frame]⟩
  let sc₁ : Scope (core3P Pf) :=
    { scA with frame := { scA.frame with components := scA.frame.components ++ [clE] } }
  let clI : Closure (core3P Pf) := ⟨l.imp.toRef, [sc₁.frame]⟩
  let sc₂ : Scope (core3P Pf) :=
    { sc₁ with frame := { sc₁.frame with components := sc₁.frame.components ++ [clI] } }
  have r₁ : instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] (importArgs l.host) scA
      (.component l.exp.toRef) = Pure.pure sc₁ := instDef_component _ _
  have r₂ : instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] (importArgs l.host) sc₁
      (.component l.imp.toRef) = Pure.pure sc₂ := instDef_component _ _
  -- the exporter
  have hfl : cfg.store.funcs.length = l.host.length := by rw [hfuncs, hostList_length]
  obtain ⟨esE, hxE, htE, hrE⟩ := instantiateCall_simpleO (σ := σ) hFe [scA.frame] cfg hcore hfl
  let cfgE := nestCfg cse cfg (fun k => Ie.addrs.getD k 0) l.exp
  let sc₃ : Scope (core3P Pf) :=
    { sc₂ with frame := { sc₂.frame with instances := sc₂.frame.instances ++ [esE] } }
  have hc₂ : sc₂.frame.component? 0 = some clE := by
    show (scA.frame.components ++ [clE] ++ [clI])[0]? = _
    rw [hcA]; rfl
  have r₃ : ORuns D (instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ []
      (importArgs l.host) sc₂ (.instance_ (.instantiate 0 []))) cfg [] sc₃ cfgE := by
    rw [instDef_instantiate sc₂ (cl := clE) (vs := []) hc₂ rfl]
    exact ORuns.bind_nil (ORuns.callItems (by rw [hD]; exact SRuns.oruns hrE))
      (SRuns.oruns (TRuns.pure _ _))
  -- the aliases of the wired exports
  let fsE : List FuncId := l.wire.map fun w => ⟨l.host.length + w⟩
  have hFA : List.Forall₂ (fun n f => lookupExport? esE n = some (.func f))
      (l.wire.map l.toL2.expName) fsE := by
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun w hw => ?_))
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hw
    obtain ⟨x, hx, -⟩ := hW.ty k w hk
    have hw' : w < l.exp.exports.length := (List.getElem?_eq_some_iff.1 hx).1
    have hn : l.toL2.expName w = l.exp.exports[w].name := by
      simp [Linked2.expName, List.getElem?_eq_getElem hw']
    rw [hn, lookup_funcExportL htE hxE hEg.names w hw' (hN.exp _ (List.getElem_mem hw'))]
  have eA : (l.wire.map fun w => (.alias (.export_ 0 (l.toL2.expName w) .func) :
      Syntax.Definition Silmaril.Wasm.Module)) =
      (l.wire.map l.toL2.expName).map fun n => .alias (.export_ 0 n .func) := by
    rw [List.map_map]
    rfl
  have hi₃ : sc₃.frame.instance? 0 = some esE := by
    show (scA.frame.instances ++ [esE])[0]? = _
    rw [hiA]; rfl
  have rA' := aliases_run (R := (callRecurse : Recurse (core3P Pf) σ)) (inst := ⟨0⟩) (outer := [])
    (args := importArgs l.host) (i := 0) hFA sc₃ cfgE hi₃
  let sc₄ : Scope (core3P Pf) := { sc₃ with frame := { sc₃.frame with funcs := sc₃.frame.funcs ++ fsE } }
  -- the importer
  have hf₄ : sc₄.frame.funcs = (List.range' 0 l.host.length).map FuncId.mk ++ fsE := by
    show scA.frame.funcs ++ fsE = _
    rw [hfA']
  have hv : ((l.imp.imports.mapIdx fun n p =>
      (p.1, (⟨.func, l.importFid n⟩ : Syntax.SortIdx Syntax.Sort_)))).mapM
      (fun x => (x.1, ·) <$> itemAt? sc₄.frame x.2) = some (linkArgsH l) := by
    refine mapM_eq_some_of_getElem (by simp [linkArgsH]) fun i hi => ?_
    have hi' : i < l.imp.imports.length := by simpa using hi
    have hfi : sc₄.frame.funcs[l.importFid i]? = some (l.fid i) := by
      rw [hf₄]
      by_cases hiw : i < l.wire.length
      · simp only [HLinked2.importFid, HLinked2.fid, hiw, ite_true]
        rw [List.getElem?_append_right (by simp), List.length_map, List.length_range',
          Nat.add_sub_cancel_left]
        simp [fsE, List.getElem?_eq_getElem hiw]
      · simp only [HLinked2.importFid, HLinked2.fid, hiw, ite_false]
        have hlt : i - l.wire.length < l.host.length := by omega
        rw [List.getElem?_append_left (by simpa using hlt)]
        simp [hlt]
    simp only [List.getElem_mapIdx, linkArgsH, itemAt?, Frame.get?, Frame.func?, hfi,
      Option.map_some, Option.bind_some, Function.comp_apply, Entry.toItem?]
    rfl
  have hn2 : nextInst cfgE.store = ⟨2⟩ := linkStoreE_nextInst cse _ l.toL2 hinsts
  have hfb : cfgE.store.funcs.length = l.host.length + l.exp.exports.length := by
    show (cfg.store.funcs ++ liftedList _ _ l.exp.exports).length = _
    simp [hfuncs, liftedList, hostList_length]
  have hb : ImportsBound l.imp (linkArgsH l) l.fid cfgE.store := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have h := lookup_mapIdx_val (·.1) (fun k => (ItemVal.func (l.fid k) : ItemVal (core3P Pf)))
        0 l.imp.imports j hj hIn
      simp only [Nat.zero_add] at h
      exact h
    · show ∃ fi, (cfg.store.funcs ++ liftedList _ _ l.exp.exports)[(l.fid j).idx]? = some fi ∧ _
      rw [hfuncs]
      by_cases hjw : j < l.wire.length
      · obtain ⟨x, hx, hty⟩ := hW.ty j l.wire[j] (List.getElem?_eq_getElem hjw)
        have hw' : l.wire[j] < l.exp.exports.length := (List.getElem?_eq_some_iff.1 hx).1
        have hxw : l.exp.exports[l.wire[j]] = x := (List.getElem?_eq_some_iff.1 hx).2
        have hty' : l.imp.imports[j].2 = x.ty := by
          simpa [List.getElem?_eq_getElem hj] using hty
        refine ⟨.lifted (Ie.addrs.getD x.core 0) (liftedFt x) {} (nextInst cfg.store), ?_, ?_⟩
        · simp only [HLinked2.fid, hjw, ite_true, getD_lt hjw]
          rw [List.getElem?_append_right (by simp [hostList_length]), hostList_length,
            Nat.add_sub_cancel_left]
          simp only [liftedList, List.getElem?_map, List.getElem?_eq_getElem hw', hxw,
            Option.map_some]
        · show liftedFt x = witFt l.imp.imports[j].2
          rw [hty']
          rfl
      · have hlt : j - l.wire.length < l.host.length := by omega
        refine ⟨.host (witFt l.host[j - l.wire.length].2) ⟨0 + (j - l.wire.length)⟩, ?_, ?_⟩
        · simp only [HLinked2.fid, hjw, ite_false]
          rw [List.getElem?_append_left (by simpa [hostList_length] using hlt)]
          simp only [hostList, List.getElem?_mapIdx, List.getElem?_eq_getElem hlt,
            Option.map_some]
        · show witFt l.host[j - l.wire.length].2 = witFt l.imp.imports[j].2
          rw [host_getElem hW _ hlt]
          congr 3
          omega
  obtain ⟨esI, hxI, htI, hrI⟩ := instantiateCall_simpleI' (σ := σ) hIg hIa [sc₁.frame]
    (linkArgsH l) cfgE (hn2 ▸ hFi) rfl hfb hb
  rw [hn2] at hrI
  let cfgI : Machine.Config (core3P Pf) σ :=
    { cfg with core := csi, store := linkStore cse csi (fun k => Ie.addrs.getD k 0) addrI l.toL2 cfg.store }
  let sc₅ : Scope (core3P Pf) :=
    { sc₄ with frame := { sc₄.frame with instances := sc₄.frame.instances ++ [esI] } }
  have hc₄ : sc₄.frame.component? 1 = some clI := by
    show (scA.frame.components ++ [clE] ++ [clI])[1]? = _
    rw [hcA]; rfl
  have r₅ : ORuns D (instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ []
      (importArgs l.host) sc₄
      (.instance_ (.instantiate 1 (l.imp.imports.mapIdx fun n p => (p.1, ⟨.func, l.importFid n⟩)))))
      cfgE [] sc₅ cfgI := by
    rw [instDef_instantiate sc₄ (cl := clI) hc₄ hv]
    exact ORuns.bind_nil (ORuns.callItems (by rw [hD]; exact SRuns.oruns hrI))
      (SRuns.oruns (TRuns.pure _ _))
  -- the aliases of the importer's exports
  let fsI : List FuncId := (List.range l.imp.exports.length).map fun i =>
    ⟨l.host.length + l.exp.exports.length + i⟩
  have hFB : List.Forall₂ (fun n f => lookupExport? esI n = some (.func f))
      (l.imp.exports.map (·.name)) fsI := by
    refine List.forall₂_iff_get.2 ⟨by simp [fsI], fun i h₁ h₂ => ?_⟩
    have hi : i < l.imp.exports.length := by simpa using h₁
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, fsI]
    exact lookup_funcExportL htI hxI hIg.names i hi (hN.imp _ (List.getElem_mem hi))
  have eB : (l.imp.exports.map fun x => (.alias (.export_ 1 x.name .func) :
      Syntax.Definition Silmaril.Wasm.Module)) =
      (l.imp.exports.map (·.name)).map fun n => .alias (.export_ 1 n .func) := by
    rw [List.map_map]
    rfl
  have hi₅ : sc₅.frame.instance? 1 = some esI := by
    show (scA.frame.instances ++ [esE] ++ [esI])[1]? = _
    rw [hiA]; rfl
  have rB := aliases_run (R := (callRecurse : Recurse (core3P Pf) σ)) (inst := ⟨0⟩) (outer := [])
    (args := importArgs l.host) (i := 1) hFB sc₅ cfgI hi₅
  -- the exports
  obtain ⟨scF, rC, hxC⟩ := exportsP_run (R := (callRecurse : Recurse (core3P Pf) σ))
    (inst := ⟨0⟩) (outer := []) (args := importArgs l.host) l.imp.exports
    (l.host.length + l.wire.length) (l.host.length + l.exp.exports.length)
    { sc₅ with frame := { sc₅.frame with funcs := sc₅.frame.funcs ++ fsI } } cfgI
    (fun j hj => by
      show (sc₄.frame.funcs ++ fsI)[l.host.length + l.wire.length + j]? = _
      have e : l.host.length + l.wire.length + j -
          ((List.range' 0 l.host.length).map FuncId.mk).length = fsE.length + j := by
        simp [fsE]; omega
      rw [hf₄, List.append_assoc, List.getElem?_append_right (by simp; omega), e,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      simp [fsI, hj])
  refine ⟨scF, ?_, ?_⟩
  · rw [toRef_eqH]
    unfold tailH
    rw [eA, eB]
    have hn₀ : ({} : Scope (core3P Pf)).frame.types.length = 0 := rfl
    rw [hn₀] at rA
    exact ORuns.foldlM_append (os₁ := []) (os₂ := []) (SRuns.oruns rA)
      (ORuns.foldlM_append (os₁ := []) (os₂ := []) (ORuns.foldlM_append (os₁ := [])
      (os₂ := []) (ORuns.foldlM_append (os₁ := []) (os₂ := [])
      (ORuns.foldlM_append (os₁ := []) (os₂ := [])
        (ORuns.foldlM_cons (os₁ := []) (os₂ := []) (SRuns.oruns (TRuns.of_eq cfg r₁))
          (ORuns.foldlM_cons (os₁ := []) (os₂ := []) (SRuns.oruns (TRuns.of_eq cfg r₂))
            (ORuns.foldlM_cons (os₁ := []) (os₂ := []) r₃
              (SRuns.oruns (TRuns.foldlM_nil _ _)))))
        (SRuns.oruns rA'))
      (ORuns.foldlM_cons (os₁ := []) (os₂ := []) r₅ (SRuns.oruns (TRuns.foldlM_nil _ _))))
      (SRuns.oruns rB)) (SRuns.oruns rC))
  · rw [hxC, funcExports_append']
    show funcExports scA.exports ++ _ = _
    rw [hxA', List.nil_append]
    exact funcExports_mapIdx_func _ _

/-! ## The root instantiation -/

/-- Every import of `l.toRef` is supplied by `importArgs`. -/
theorem argsCompleteH {l : HLinked2} (hHn : (l.host.map (·.1)).Nodup) :
    argsComplete l.toRef (importArgs l.host : Exports (core3P Pf)) = true := by
  have hn := noImport_tailH l
  have hnames : importNames l.toRef = l.host.map (·.1) := by
    have h₁ := importNames_importsDefs Pf l.host 0
    have h₂ := importNames_nil hn
    rw [toRef_eqH]
    simp only [importNames, List.filterMap_append] at h₁ h₂ ⊢
    rw [h₁, h₂, List.append_nil]
  rw [argsComplete, hnames, List.all_eq_true]
  intro n hn'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  rw [importArgs_lookup hHn j hj]
  rfl

/-- **The import pre-check of `l.toRef` passes** in a store holding the host functions of the
host imports. -/
theorem precheckH {l : HLinked2} (hHn : (l.host.map (·.1)).Nodup) (s : CStore (core3P Pf))
    (hs : s.funcs = hostList 0 l.host) :
    precheckImports s (importArgs l.host) Frame.empty l.toRef = .ok () := by
  obtain ⟨f', hP⟩ := importsDefs_pre (s := s) (args := importArgs l.host) l.host 0
    Frame.empty fun j hj =>
      ⟨by rw [Nat.zero_add]; exact importArgs_lookup hHn j hj,
       by rw [Nat.zero_add]; exact hostList_get hs j hj⟩
  rw [toRef_eqH]
  exact (hP.1 _).trans (precheckImports_ok s _ f' _ (noImport_tailH l))

variable {D : Call (core3P Pf) → P (core3P Pf) σ (Ret (core3P Pf))}

/-- **Root instantiation of `l.toRef` runs** with late-bound calls: the root checks pass, the
root instance `0` is allocated and the definitions run (`toRefH_run`). -/
theorem rootCallH_run {l : HLinked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.toL2.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.fid addrI csi cii)
    (cfg : Machine.Config (core3P Pf) σ) (hcore : cfg.core = (core3P Pf).empty _)
    (hfuncs : cfg.store.funcs = hostList 0 l.host) (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = l.exportMap ∧
      ORuns D (instantiateRootCall l.toRef (importArgs l.host) : P (core3P Pf) σ _) cfg []
        (⟨0⟩, es)
        { cfg with core := csi, store :=
            rootStoreL cse csi (fun k => Ie.addrs.getD k 0) addrI l.toL2 cfg.store } := by
  have hHn := host_nodup hW hIn
  obtain ⟨sc', hr, hx⟩ := toRefH_run hD hEg hFe hIg hIa hIn hW hN hFi
    { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore hfuncs
    (by simp [ArenaOps.allocSt, ArenaField.alloc, ArenaField.insts, Arena.alloc, hinsts])
  have hac : argsComplete l.toRef (importArgs l.host : Exports (core3P Pf)) = true :=
    argsCompleteH hHn
  have hpre : precheckImports cfg.store (importArgs l.host) Frame.empty l.toRef = .ok () :=
    precheckH hHn cfg.store hfuncs
  have hid : (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  refine ⟨sc'.exports, hx, ?_⟩
  unfold instantiateRootCall instantiateRoot
  refine ORuns.bind_nil (SRuns.oruns (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg))
    (ORuns.bind_nil (SRuns.oruns (TRuns.getStore cfg)) ?_)
  refine ORuns.bind_nil (SRuns.oruns (checkImport_run hpre cfg))
    (ORuns.bind_nil (SRuns.oruns (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg)) ?_)
  rw [hid]
  unfold instantiateComponent
  exact ORuns.bind_nil (ORuns.bind_nil (f := fun sc => Pure.pure sc.exports) hr
    (SRuns.oruns (TRuns.pure _ _))) (SRuns.oruns (TRuns.pure _ _))

/-- The configuration of the host functions of `l.host` (`hostConfig`), its store written out. -/
noncomputable def initH (l : HLinked2) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  Config.init { (CStore.empty : CStore (core3P Pf)) with funcs := hostList 0 l.host } h₀

theorem hostConfig_eqH (l : HLinked2) (h₀ : σ) :
    (LinkedSession.hostConfig l.host h₀ : Machine.Config (core3P Pf) σ) = initH l h₀ := by
  simp only [LinkedSession.hostConfig, initH, hostFuncs_eq]
  rfl

/-- **The configuration after instantiating `l.toRef`**: the host in control (in host state
`h`), the shared core store `csi`, three component instances (the root, the exporter, the
importer), the host functions, then the exporter's lifted functions, then the importer's. -/
noncomputable def afterLinkH (P : Profile) (csi : (core3P P).Store (CanonHost (core3P P)))
    (addrE addrI : Nat → Nat) (l : HLinked2) (h : σ) : Machine.Config (core3P P) σ :=
  { Config.init
    { insts := [{}, {}, {}],
      funcs := hostList 0 l.host ++ liftedList addrE ⟨1⟩ l.exp.exports ++
        liftedList addrI ⟨2⟩ l.imp.exports } h with
    core := csi }

/-- **The instantiation program of `l.toRef` runs** from the host functions' configuration to
`afterLinkH`, observing the root instance `0` and the export map `l.exportMap`. -/
theorem instProgH_run {l : HLinked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.toL2.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.fid addrI csi cii) (h₀ : σ) :
    ORuns D (instantiateProg l.toRef (importArgs l.host) : P (core3P Pf) σ (Ret (core3P Pf)))
      (initH l h₀) [instantiatedObs ⟨0⟩ l.exportMap] .unit
      (afterLinkH Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) := by
  obtain ⟨es, hes, hr⟩ := rootCallH_run hD hEg hFe hIg hIa hIn hW hN hFi
    { (initH l h₀ : Machine.Config (core3P Pf) σ) with
      store := DispatchSt.incNestingSt (initH l h₀ : Machine.Config (core3P Pf) σ).store }
    rfl rfl rfl
  unfold instantiateProg
  refine ORuns.bind_nil (SRuns.oruns
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _)) ?_
  refine ORuns.bind_nil hr ?_
  dsimp only
  rw [hes]
  exact SRuns.oruns (SRuns.bind (os₁ := [])
    (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _) (.emit (.pure _ _)))

/-! ## The machine runs of the instantiation -/

variable {prof : ProfileKind} {hr : HostReady σ}

/-- The configuration after the instantiation host event. -/
noncomputable def instStartH (l : HLinked2) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  { (initH l h₀ : Machine.Config (core3P Pf) σ) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg l.toRef (importArgs l.host)))] }

/-- **The instantiation is one live run** from the host event to `afterLinkH`. -/
theorem instH_lrun {l : HLinked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.toL2.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.fid addrI csi cii) (h₀ : σ) :
    ∃ tr, traceObs tr = [instantiatedObs ⟨0⟩ l.exportMap] ∧
      LRun prof hr D (instStartH l h₀) tr
        (afterLinkH Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) := by
  obtain ⟨tr, r, o⟩ := instProgH_run hD hEg hFe hIg hIa hIn hW hN hFi h₀
  have d := r.lrun (prof := prof) (hr := hr) rfl (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterLinkH Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀ with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterLinkH Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  exact ⟨tr ++ [.tau], by rw [traceObs_append, o]; rfl,
    d.trans (.cons ⟨List.cons_ne_nil _ _, rfl⟩ s (.refl _))⟩

/-- **The results of instantiating `l.toRef`** from the host functions of `l.host`, under any
host: the only one is the instance at `afterLinkH` with root instance `0` and the export map
`l.exportMap` (given the importer's core instantiation in the shared core store for `l.fid`). -/
theorem instBehavioursH_toRef {l : HLinked2} (hEg : l.exp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} {cse : (core3P Pf).Store (CanonHost (core3P Pf))}
    {cie : (core3P Pf).Inst} (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good)
    (hIa : l.imp.Arity) (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy)
    (hN : l.toL2.NamesOk) {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))}
    {cii : (core3P Pf).Inst} (hFi : CoreFactsL l.imp cse ⟨2⟩ l.fid addrI csi cii)
    (prof : ProfileKind) (h : Host (core3P Pf) σ) (h₀ : σ) :
    ∀ r ∈ instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host),
      r = .instance (afterLinkH Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) ⟨0⟩
        l.exportMap := by
  obtain ⟨trD, ho, d⟩ := instH_lrun (prof := prof) (hr := h.hr) (D := h.dispatch)
    (fun _ _ => rfl) hEg hFe hIg hIa hIn hW hN hFi h₀
  intro r hr
  rw [hostConfig_eqH] at hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc', -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartH l h₀ := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := lrun_end d rfl (he ▸ hs₁) hn (.inl hc')
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, l.exportMap) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), l.exportMap) :=
      Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartH l h₀ := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := lrun_end d rfl (he ▸ hs₁) hn (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStartH l h₀ := hostRun_inv s₁
    exact absurd (d.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

/-- **The instance at `afterLinkH` is a result of instantiating `l.toRef`**, under any host. -/
theorem instH_mem {l : HLinked2} (hEg : l.exp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} {cse : (core3P Pf).Store (CanonHost (core3P Pf))}
    {cie : (core3P Pf).Inst} (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good)
    (hIa : l.imp.Arity) (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy)
    (hN : l.toL2.NamesOk) {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))}
    {cii : (core3P Pf).Inst} (hFi : CoreFactsL l.imp cse ⟨2⟩ l.fid addrI csi cii)
    (prof : ProfileKind) (h : Host (core3P Pf) σ) (h₀ : σ) :
    InstResult.instance (afterLinkH Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) ⟨0⟩
      l.exportMap ∈ instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) := by
  obtain ⟨trD, ho, d⟩ := instH_lrun (prof := prof) (hr := h.hr) (D := h.dispatch)
    (fun _ _ => rfl) hEg hFe hIg hIa hIn hW hN hFi h₀
  rw [hostConfig_eqH]
  refine ⟨trD, .cons (Step.hostRun ⟨rfl, rfl, rfl⟩) d.steps, Adequacy.LRun.no_host d, rfl, rfl,
    ?_⟩
  rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]

end Link

/-! ## The importer's core facts for the relocation `l.fid` -/

/-- **The core facts of the importer in the shared store for `l.fid`** (`coreFactsL_of_inst`
at the lowered callees `l.fid`): trampoline `k` lowers the exporter's lifted function
`k₀ + wire[k]` for a wired import and the host function `k - wire.length` for a host import
(`k₀ = host.length`). -/
theorem coreFactsH_of_inst {l : HLinked2} (hc : l.imp.Good) (hi : l.imp.Inst)
    (hseg : l.imp.mod.mod.data = [] ∧ l.imp.mod.mod.elems = []) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : l.imp.mod.IsInst I) (cs₀ : (core3P Pf).Store (CanonHost (core3P Pf))) :
    ∃ (r : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3P Pf) × Nat)) (ci : (core3P Pf).Inst),
      Store.mapH Prod.snd r = I.store ∧
      HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
        h = (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r ∧
      CoreFactsL l.imp cs₀ ⟨2⟩ l.fid
        (addrL (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length I)
        (reloc cs₀ (Store.mapH Prod.fst r)) ci :=
  coreFactsL_of_inst hc hi hseg hI cs₀ ⟨2⟩ l.fid

/-- **The results of instantiating `l.toRef`, from `Inst` of both children**, under any host:
for an importer module without data and element segments, there are the exporter's game
instance `Ie` and core store `cse` (`CoreFacts`), and for every game instance `Ii` of the
importer module a store `r` (second projection `Ii.store`, host code the trampolines of `l.fid`
paired with their import index) such that the instance at `afterLinkH` over the core store
`reloc cse (r.mapH Prod.fst)` is a result of instantiating `l.toRef`, and the only one. -/
theorem instBehavioursH_inst {l : HLinked2} (hEg : l.exp.Good) (hEi : l.exp.Inst)
    (hIg : l.imp.Good) (hIi : l.imp.Inst) (hIa : l.imp.Arity)
    (hseg : l.imp.mod.mod.data = [] ∧ l.imp.mod.mod.elems = []) (hW : l.WireTy)
    (hN : l.toL2.NamesOk) :
    ∃ (Ie : Silmaril.Wasm.Game.ScalarInstance) (cse : (core3P Pf).Store (CanonHost (core3P Pf)))
      (cie : (core3P Pf).Inst), CoreFacts l.exp Ie cse cie ∧
      ∀ (Ii : Silmaril.Wasm.Game.ScalarInstance), l.imp.mod.IsInst Ii →
      ∃ r : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3P Pf) × Nat),
        Store.mapH Prod.snd r = Ii.store ∧
        HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
          h = (.lowered (l.fid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r ∧
        ∀ (prof : ProfileKind) (h : Host (core3P Pf) σ) (h₀ : σ),
        let m := afterLinkH Pf (reloc cse (Store.mapH Prod.fst r))
          (fun k => Ie.addrs.getD k 0)
          (addrL (cse : Silmaril.Wasm.Execution.Core.Store _).funcs.length Ii) l h₀
        InstResult.instance m ⟨0⟩ l.exportMap ∈
            instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
          ∀ res ∈ instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host),
            res = .instance m ⟨0⟩ l.exportMap := by
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := Pf) hEg hEi
  refine ⟨Ie, cse, cie, hFe, fun Ii hI => ?_⟩
  obtain ⟨r, cii, hrs, hh, hFi⟩ := coreFactsH_of_inst hIg hIi hseg hI cse
  exact ⟨r, hrs, hh, fun prof h h₀ =>
    ⟨instH_mem hEg hFe hIg hIa hIi.importNames hW hN hFi prof h h₀,
     instBehavioursH_toRef hEg hFe hIg hIa hIi.importNames hW hN hFi prof h h₀⟩⟩

/-- **`l.toRef` instantiates, uniquely, for adequate parts** (under any host, from the host
functions of `l.host`): there is a configuration `m`, with the host in control in the initial
host state, such that the instance at `m` with root instance `0` and the export map
`l.exportMap` is the only result of instantiating `l.toRef`. -/
theorem hlinked2_instantiates (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) (h : Host (core3P P) σ) (h₀ : σ) :
    ∃ m : Machine.Config (core3P P) σ, m.ctl = [] ∧ m.host = h₀ ∧
      InstResult.instance m ⟨0⟩ l.exportMap ∈
        instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      ∀ r ∈ instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host),
        r = .instance m ⟨0⟩ l.exportMap := by
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursH_inst (Pf := P) (σ := σ) hl.expGood
    hl.expInst hl.impGood hl.impInst hl.impArity ⟨hl.splitOk.imp.data, hl.splitOk.imp.elems⟩
    hl.wireTy hl.namesOk
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨r, -, -, hres⟩ := hall Ii hIi
  obtain ⟨hm, hu⟩ := hres prof h h₀
  exact ⟨_, rfl, rfl, hm, hu⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
