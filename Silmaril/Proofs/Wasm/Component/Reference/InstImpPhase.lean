module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpRun
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation phase of `SimpleI.toRef`

Instantiating `c.toRef` from the store of host functions of the imports (`hostFuncs`) with the
root arguments `importArgs` is a silent deterministic run (`SRuns`) of the instantiation
program: the root checks pass (every import is supplied, `argsComplete`; the import pre-check
passes, `importsDefs_pre`), the root instance `0` is allocated, and the definitions run
(`toRefDefsI_run`: imports, core module, `canon lower`s, the inline core instance, the core
instantiation, the exports). With the host event before and the end of the host frame after,
every machine run of the instantiation follows it, which proves `instPhaseI`: the only result
is the instance at `afterInst P cs (c.afterFuncs P addr)` with export `i` at function `n + i`
(`exportMapI`), where the core store `cs` renames to the instance's store under `trampIdx` and
has only trampoline host code (`SimpleI.TrampOk`) — the configuration `callPhaseI` starts from.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)
open Silmaril.Wasm.Numerics (Profile)

/-- The function exports of the root instance of `c.toRef`: export `i` is function `n + i`,
after the `n` imported functions. -/
def exportMapI (c : SimpleI) : List (String × FuncId) :=
  c.exports.mapIdx fun i x => (x.name, ⟨c.imports.length + i⟩)

variable {Pf : Profile} {σ : Type}

/-! ## The initial store and the root arguments -/

theorem hostFuncs_eq : ∀ (k : Nat) (ims : Iface) (s : CStore (core3P Pf)),
    hostFuncs k ims s = { s with funcs := s.funcs ++ hostList k ims }
  | _, [], s => by simp only [hostFuncs, hostList, List.mapIdx_nil, List.append_nil]
  | k, p :: ps, s => by
    have hl : hostList (Pf := Pf) k (p :: ps) =
        .host (witFt p.2) ⟨k⟩ :: hostList (k + 1) ps := by
      simp only [hostList, List.mapIdx_cons, Nat.add_zero, Nat.add_right_comm k, Nat.add_assoc]
    rw [hostFuncs, hostFuncs_eq (k + 1) ps, hl]
    simp only [ArenaField.alloc, ArenaField.funcs, Arena.alloc, List.append_assoc,
      List.singleton_append]

theorem hostList_length (k : Nat) (ims : Iface) : (hostList (Pf := Pf) k ims).length = ims.length :=
  List.length_mapIdx

theorem hostList_get {s : CStore (core3P Pf)} {ims : Iface} (hs : s.funcs = hostList 0 ims)
    (j : Nat) (hj : j < ims.length) :
    ArenaField.funcs.get? s ⟨j⟩ = some (.host (witFt ims[j].2) ⟨j⟩) := by
  show s.funcs[j]? = _
  rw [hs, hostList, List.getElem?_mapIdx, List.getElem?_eq_getElem hj, Nat.zero_add]
  rfl

theorem importArgs_lookup {ims : Iface} (hnd : (ims.map (·.1)).Nodup) (j : Nat)
    (hj : j < ims.length) :
    (importArgs ims : Exports (core3P Pf)).lookup ims[j].1 = some (.func ⟨j⟩) := by
  have h := lookup_mapIdx_val (·.1) (fun i => (ItemVal.func ⟨i⟩ : ItemVal (core3P Pf))) 0 ims j hj
    hnd
  simp only [Nat.zero_add] at h
  exact h

/-! ## Names of the emitted definitions -/

theorem emitTys_noImport (ts : List ValTy) (n : Nat) :
    NoImport (emitTys (M := (core3P Pf).Module) ts n).2.1 := by
  have h := emitTys_run (E := core3P Pf) (σ := Unit) (R := callRecurse) (inst := ⟨0⟩)
    (outer := []) (args := []) ts
    { frame := { (Frame.empty : Frame (core3P Pf)) with
      types := List.replicate n (.val (.prim .bool)) } }
  simp only [List.length_replicate] at h
  obtain ⟨_, hP, -⟩ := h
  exact hP.2.2.2.2

theorem importNames_importDefs (Pf : Profile) (p : String × FuncTy) (n : Nat) :
    importNames (SimpleI.importDefs p n).1 = [p.1] := by
  have h₁ : importNames (emitTys (M := Silmaril.Wasm.Module) p.2.params n).2.1 = [] :=
    importNames_nil (emitTys_noImport (Pf := Pf) p.2.params n)
  have h₂ : importNames (emitTys (M := Silmaril.Wasm.Module) p.2.results
      (emitTys (M := Silmaril.Wasm.Module) p.2.params n).2.2).2.1 = [] :=
    importNames_nil (emitTys_noImport (Pf := Pf) p.2.results _)
  simp only [importNames] at h₁ h₂
  simp only [SimpleI.importDefs, importNames, List.filterMap_append, h₁, h₂]
  rfl

theorem importNames_importsDefs (Pf : Profile) : ∀ (ims : Iface) (n : Nat),
    importNames (SimpleI.importsDefs ims n).1 = ims.map (·.1)
  | [], _ => rfl
  | p :: ps, n => by
    rw [importsDefs_cons]
    have h₁ := importNames_importDefs Pf p n
    have h₂ := importNames_importsDefs Pf ps (SimpleI.importDefs p n).2
    simp only [importNames, List.filterMap_append] at h₁ h₂ ⊢
    rw [h₁, h₂]
    rfl

/-! ## The definitions -/

/-- `c.toRef` as its import definitions followed by the rest. -/
theorem toRef_eq (c : SimpleI) :
    c.toRef = (SimpleI.importsDefs c.imports 0).1 ++
      ([.coreModule c.mod.mod] ++ (c.imports.mapIdx fun k _ => .canon (.lower k [])) ++
        [.coreInstance (.exports (c.mod.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩))),
         .coreInstance (.instantiate 0 [("env", 0)])] ++
        SimpleI.exportsDefsAt c.mod.exports 1 c.imports.length 0 c.exports
          (SimpleI.importsDefs c.imports 0).2) := by
  simp only [SimpleI.toRef, List.append_assoc]

theorem noImport_mid (c : SimpleI) :
    NoImport ([.coreModule c.mod.mod] ++
      (c.imports.mapIdx fun k _ => (.canon (.lower k []) : Syntax.Definition Silmaril.Wasm.Module)) ++
      [.coreInstance (.exports (c.mod.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩))),
       .coreInstance (.instantiate 0 [("env", 0)])]) := by
  intro d hd n x e
  simp only [List.mem_append, List.mem_cons, List.mem_mapIdx,
    List.not_mem_nil, or_false] at hd
  rcases hd with (rfl | ⟨k, -, rfl⟩) | rfl | rfl <;> cases e

section Run

variable {R : Recurse (core3P Pf) σ} {outer : List (Frame (core3P Pf))}

/-- The import arities of `c`. -/
theorem arity_imports {c : SimpleI} (har : c.Arity) :
    ∀ p ∈ c.imports, (ValTy.flatList p.2.params).length ≤ 16 ∧
      (ValTy.flatList p.2.results).length ≤ 1 ∧ p.2.results.length ≤ 1 :=
  har.2

/-- **The definitions of `c.toRef` run silently** from a store with the empty core store and
the host functions of the imports: the imports, the core module, the trampolines, the two core
instances and the lifted functions of the exports. -/
theorem toRefDefsI_run {c : SimpleI} (hc : c.Good) (hi : c.Inst) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hF : CoreFactsI c I cs ci) (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = hostList 0 c.imports) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R ⟨0⟩ outer (importArgs c.imports)) {} c.toRef)
        cfg sc'
        { cfg with store :=
            liftStore cs cfg.store (liftedList (fun k => I.addrs.getD k 0) ⟨0⟩ c.exports) } ∧
      funcExports sc'.exports = exportMapI c := by
  have hget : ∀ j (hj : j < c.imports.length), ArenaField.funcs.get? cfg.store ⟨j⟩ =
      some (.host (witFt c.imports[j].2) ⟨j⟩) := hostList_get hfuncs
  -- the imports
  obtain ⟨scA, rA, ⟨newA, hfA⟩, hlA, hxA⟩ := importsDefs_run (R := R) (inst := ⟨0⟩)
    (outer := outer) c.imports 0 {} cfg fun j hj =>
      ⟨by rw [Nat.zero_add]; exact importArgs_lookup hi.importNames j hj,
       by rw [Nat.zero_add]; exact hget j hj⟩
  have hlenm : c.mod.imports.length = c.imports.length := by rw [hc.imports, List.length_map]
  -- the core module
  have rB := instDef_coreModule (R := R) (inst := ⟨0⟩) (outer := outer)
    (args := importArgs c.imports) scA c.mod.mod
  -- the trampolines
  have hfB : ∀ j < c.imports.length,
      ({ scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module) } :
        Frame (core3P Pf)).funcs[j]? = some ⟨j⟩ := by
    intro j hj
    show scA.frame.funcs[j]? = _
    rw [hfA]
    simp [hj, Frame.empty]
  have rC := lowers_run (R := R) (outer := outer) (args := importArgs c.imports) (arity_imports har)
    c.imports.length 0
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module) } }
    cfg (Nat.zero_add _) hfB (by rw [hcore]; rfl) hget
  -- the inline core instance
  have hcfC : (scA.frame.coreFuncs ++ addrList Pf (List.range' 0 c.imports.length)) =
      List.range c.mod.imports.length := by
    rw [hfA, hlenm, List.range_eq_range']
    rfl
  have rD := coreExports_run (R := R) (inst := ⟨0⟩) (outer := outer)
    (args := importArgs c.imports)
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
                                         coreFuncs := scA.frame.coreFuncs ++
                                           addrList Pf (List.range' 0 c.imports.length) } }
    { cfg with store := { cfg.store with core := trampStore Pf c.imports } } c.mod.imports hcfC
  -- the core instantiation
  have hmE : (scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module)) = ([c.mod.mod] : List (core3P Pf).Module) := by rw [hfA]; rfl
  have hciE : (scA.frame.coreInstances ++
      ([envExports c.mod.imports] : List (List (String × (core3P Pf).ExternVal))))[0]? =
      some (envExports c.mod.imports) := by rw [hfA]; rfl
  have rE := instantiateEnv_run (R := R) (inst := ⟨0⟩) (outer := outer)
    (args := importArgs c.imports)
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
                                         coreFuncs := scA.frame.coreFuncs ++
                                           addrList Pf (List.range' 0 c.imports.length),
                                         coreInstances := scA.frame.coreInstances ++
                                           ([envExports c.mod.imports] :
                                             List (List (String × (core3P Pf).ExternVal))) } }
    { cfg with store := { cfg.store with core := trampStore Pf c.imports } } hmE
    (hF.imports _ hciE) hF.prepare
  -- the exports
  have hinv : ExpInvAt ((core3P Pf).exports ci) 1 c.imports.length 0
      ({ scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
                        coreFuncs := scA.frame.coreFuncs ++
                          addrList Pf (List.range' 0 c.imports.length),
                        coreInstances := scA.frame.coreInstances ++
                          ([envExports c.mod.imports] :
                            List (List (String × (core3P Pf).ExternVal))) ++
                          [(core3P Pf).exports ci] } : Frame (core3P Pf)) := by
    refine ⟨?_, ?_, ?_⟩
    · show (scA.frame.coreInstances ++ _ ++ _)[1]? = _
      rw [hfA]
      rfl
    · show (scA.frame.coreFuncs ++ addrList Pf (List.range' 0 c.imports.length)).length = _
      rw [hfA]
      show (addrList Pf (List.range' 0 c.imports.length)).length = c.imports.length + 0
      exact List.length_range'
    · show scA.frame.funcs.length = _
      rw [hfA]
      simp [Frame.empty]
  have hs : (setCoreSt cs { cfg.store with core := trampStore Pf c.imports }).funcs.length =
      c.imports.length + 0 := by
    show cfg.store.funcs.length = _
    rw [hfuncs, hostList_length, Nat.add_zero]
  obtain ⟨scF, rF, hxF, -⟩ := exportsDefsAt_run (R := R) (inst := ⟨0⟩) (outer := outer)
    (args := importArgs c.imports) c.mod.exports 1 c.imports.length
    (fun k => I.addrs.getD k 0) c.exports 0
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
                                         coreFuncs := scA.frame.coreFuncs ++
                                           addrList Pf (List.range' 0 c.imports.length),
                                         coreInstances := scA.frame.coreInstances ++
                                           ([envExports c.mod.imports] :
                                             List (List (String × (core3P Pf).ExternVal))) ++
                                           [(core3P Pf).exports ci] } }
    { cfg with store := setCoreSt cs { cfg.store with core := trampStore Pf c.imports } }
    hinv hs (fun x hx => hF.lookup x hx)
  have hlA' : scA.frame.types.length = (SimpleI.importsDefs c.imports 0).2 := hlA
  rw [hlA'] at rF
  refine ⟨scF, ?_, ?_⟩
  · rw [← lowers_eq] at rC
    rw [toRef_eq]
    exact TRuns.foldlM_append rA (TRuns.foldlM_append (TRuns.foldlM_append (TRuns.foldlM_append
      (TRuns.foldlM_cons (TRuns.of_eq cfg rB) (TRuns.foldlM_nil _ _)) rC)
      (TRuns.foldlM_cons rD (TRuns.foldlM_cons rE (TRuns.foldlM_nil _ _)))) rF)
  · have hx₀ : funcExports scA.exports = [] := hxA
    rw [hxF]
    show funcExports scA.exports ++ _ = _
    rw [hx₀, List.nil_append, exportMapI]
    simp only [Nat.add_zero]

end Run

/-- The export definitions are no imports. -/
theorem exportDefsAt_noImport (Pf : Profile) (names : CoreIface) (ix base i : Nat) (x : SimpleExport)
    (n : Nat) :
    NoImport (SimpleI.exportDefsAt names ix base i x n :
      List (Syntax.Definition (core3P Pf).Module) × Nat).1 := by
  rw [exportDefsAt_eq]
  exact ((emitTys_noImport (Pf := Pf) x.ty.params n).append (emitTys_noImport (Pf := Pf) _ _)).append
    (noImport_tail _ _ _ _ _ (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun _ _ e => by cases e))

theorem exportsDefsAt_noImport (Pf : Profile) (names : CoreIface) (ix base : Nat) :
    ∀ (i : Nat) (xs : List SimpleExport) (n : Nat),
      NoImport (SimpleI.exportsDefsAt names ix base i xs n :
        List (Syntax.Definition (core3P Pf).Module))
  | _, [], _ => fun _ h => by cases h
  | i, x :: xs, n => by
    rw [exportsDefsAt_cons]
    exact (exportDefsAt_noImport Pf names ix base i x n).append
      (exportsDefsAt_noImport Pf names ix base (i + 1) xs _)

/-- The definitions of `c.toRef` after its imports are no imports. -/
theorem toRefTail_noImport (Pf : Profile) (c : SimpleI) :
    NoImport (([.coreModule c.mod.mod] ++
      (c.imports.mapIdx fun k _ => (.canon (.lower k []) : Syntax.Definition Silmaril.Wasm.Module)) ++
      [.coreInstance (.exports (c.mod.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩))),
       .coreInstance (.instantiate 0 [("env", 0)])] ++
      SimpleI.exportsDefsAt c.mod.exports 1 c.imports.length 0 c.exports
        (SimpleI.importsDefs c.imports 0).2 : List (Syntax.Definition Silmaril.Wasm.Module))) :=
  (noImport_mid c).append (exportsDefsAt_noImport Pf _ _ _ _ _ _)

/-! ## Root instantiation -/

section Root

/-- Every import of `c.toRef` is supplied by `importArgs`. -/
theorem argsComplete_toRef {c : SimpleI} (hi : c.Inst) :
    argsComplete c.toRef (importArgs c.imports : Exports (core3P Pf)) = true := by
  have hn := toRefTail_noImport Pf c
  have hnames : importNames c.toRef = c.imports.map (·.1) := by
    have h₁ := importNames_importsDefs Pf c.imports 0
    have h₂ := importNames_nil hn
    rw [toRef_eq]
    simp only [importNames, List.filterMap_append] at h₁ h₂ ⊢
    rw [h₁, h₂, List.append_nil]
  rw [argsComplete, hnames, List.all_eq_true]
  intro n hn'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  rw [importArgs_lookup hi.importNames j hj]
  rfl

/-- **The import pre-check of `c.toRef` passes** in a store holding the host functions of the
imports. -/
theorem precheck_toRef {c : SimpleI} (hi : c.Inst) (s : CStore (core3P Pf))
    (hs : s.funcs = hostList 0 c.imports) :
    precheckImports s (importArgs c.imports) Frame.empty c.toRef = .ok () := by
  have hn := toRefTail_noImport Pf c
  obtain ⟨f', hP⟩ := importsDefs_pre (s := s) (args := importArgs c.imports) c.imports 0
    Frame.empty fun j hj =>
      ⟨by rw [Nat.zero_add]; exact importArgs_lookup hi.importNames j hj,
       by rw [Nat.zero_add]; exact hostList_get hs j hj⟩
  rw [toRef_eq]
  exact (hP.1 _).trans (precheckImports_ok s _ f' _ hn)

end Root

/-! ## The instantiation program and its machine runs -/

section Prog

/-- The store after root instantiation of `c.toRef`: instance `0`, the core store and the
lifted functions after the host functions. -/
noncomputable def instStoreI (cs : (core3P Pf).Store (CanonHost (core3P Pf)))
    (s : CStore (core3P Pf)) (addr : Nat → Nat) (c : SimpleI) : CStore (core3P Pf) :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr ⟨0⟩ c.exports)

/-- **Root instantiation of `c.toRef` runs silently**: the root checks pass, instance `0` is
allocated, and the definitions run (`toRefDefsI_run`). -/
theorem rootCallI_run {c : SimpleI} (hc : c.Good) (hi : c.Inst) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hF : CoreFactsI c I cs ci) (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = hostList 0 c.imports)
    (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = exportMapI c ∧
      TRuns (instantiateRootCall c.toRef (importArgs c.imports) : P (core3P Pf) σ _) cfg (⟨0⟩, es)
        { cfg with store := instStoreI cs cfg.store (fun k => I.addrs.getD k 0) c } := by
  obtain ⟨sc', hr, hx⟩ := toRefDefsI_run (R := callRecurse) (outer := []) hc hi har hF
    { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore hfuncs
  have hac : argsComplete c.toRef (importArgs c.imports : Exports (core3P Pf)) = true :=
    argsComplete_toRef hi
  have hpre : precheckImports cfg.store (importArgs c.imports) Frame.empty c.toRef = .ok () :=
    precheck_toRef hi cfg.store hfuncs
  have hid : (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  refine ⟨sc'.exports, hx, ?_⟩
  unfold instantiateRootCall instantiateRoot
  refine (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg).bind ((TRuns.getStore cfg).bind ?_)
  refine (checkImport_run hpre cfg).bind
    ((TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind ?_)
  rw [hid]
  exact (hr.bind (f := fun sc => Pure.pure sc.exports) (TRuns.pure _ _)).bind
    (f := fun es => Pure.pure ((⟨0⟩ : InstId), es)) (TRuns.pure _ _)

/-- The initial configuration of `exportBehavioursI`: the host functions of the imports. -/
noncomputable def initI (c : SimpleI) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  Machine.Config.init (hostFuncs 0 c.imports CStore.empty) h₀

theorem afterFuncs_eq (c : SimpleI) (addr : Nat → Nat) :
    hostList 0 c.imports ++ liftedList addr ⟨0⟩ c.exports = c.afterFuncs Pf addr := by
  simp only [hostList, liftedList, SimpleI.afterFuncs, Nat.zero_add]
  rfl

/-- **The instantiation program of `c.toRef` runs silently** from the store of host functions
to `afterInst`, observing the root instance `0` and the export map `exportMapI c`. -/
theorem instProgI_run {c : SimpleI} (hc : c.Good) (hi : c.Inst) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hF : CoreFactsI c I cs ci) (h₀ : σ) :
    SRuns (instantiateProg c.toRef (importArgs c.imports) : P (core3P Pf) σ (Ret (core3P Pf)))
      (initI c h₀) [instantiatedObs ⟨0⟩ (exportMapI c)] .unit
      (afterInstH Pf cs (c.afterFuncs Pf fun k => I.addrs.getD k 0) h₀) := by
  have hinit : (initI c h₀ : Machine.Config (core3P Pf) σ) =
      Machine.Config.init { (CStore.empty : CStore (core3P Pf)) with
        funcs := hostList 0 c.imports } h₀ := by
    simp only [initI, hostFuncs_eq]
    rfl
  obtain ⟨es, hes, hr⟩ := rootCallI_run hc hi har hF
    { (Machine.Config.init { (CStore.empty : CStore (core3P Pf)) with
        funcs := hostList 0 c.imports } h₀ : Machine.Config (core3P Pf) σ) with
      store := DispatchSt.incNestingSt { (CStore.empty : CStore (core3P Pf)) with
        funcs := hostList 0 c.imports } }
    rfl rfl rfl
  rw [hinit, ← afterFuncs_eq]
  show SRuns (instantiateProg c.toRef (importArgs c.imports))
    (Machine.Config.init { (CStore.empty : CStore (core3P Pf)) with
      funcs := hostList 0 c.imports } h₀) [instantiatedObs ⟨0⟩ (exportMapI c)] .unit
    (afterInstH Pf cs (hostList 0 c.imports ++ liftedList (fun k => I.addrs.getD k 0) ⟨0⟩ c.exports) h₀)
  unfold instantiateProg
  refine SRuns.bind (os₁ := [])
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _) ?_
  refine SRuns.bind (os₁ := []) hr ?_
  dsimp only
  rw [hes]
  exact SRuns.bind (os₁ := []) (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)
    (.emit (.pure _ _))

variable {prof : ProfileKind} {hr : HostReady σ}
  {D : Call (core3P Pf) → P (core3P Pf) σ (Ret (core3P Pf))}

/-- The configuration after the instantiation host event. -/
noncomputable def instStartI (c : SimpleI) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  { (initI c h₀ : Machine.Config (core3P Pf) σ) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg c.toRef (importArgs c.imports)))] }

/-- **The instantiation is one deterministic run** from the host event to `afterInst`. -/
theorem instI_detRunL {c : SimpleI} (hc : c.Good) (hi : c.Inst) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hF : CoreFactsI c I cs ci) (h₀ : σ) :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ (exportMapI c)] ∧
      DetRunL prof hr D (instStartI c h₀)
        tr (afterInstH Pf cs (c.afterFuncs Pf fun k => I.addrs.getD k 0) h₀) := by
  have hlock : (initI c h₀ : Machine.Config (core3P Pf) σ).store.lockdown = false := by
    simp only [initI, hostFuncs_eq]
    rfl
  obtain ⟨tr, hq, ho, d⟩ := (instProgI_run hc hi har hF h₀).detRunL (prof := prof) (hr := hr)
    (dispatch := D) hlock none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterInstH Pf cs (c.afterFuncs Pf fun k => I.addrs.getD k 0) h₀ with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterInstH Pf cs (c.afterFuncs Pf fun k => I.addrs.getD k 0) h₀) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, d.trans (.cons rfl s (.refl rfl))⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl

/-- **The results of instantiating `c.toRef`** from the store of host functions of its
imports, with any host whose readiness is `hr`: the only one is the instance at `afterInst`
with root instance `0` and the export map `exportMapI c`. -/
theorem instBehavioursI_toRef {c : SimpleI} (hc : c.Good) (hi : c.Inst) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} (hF : CoreFactsI c I cs ci) (prof : ProfileKind)
    (h : Host (core3P Pf) σ) (h₀ : σ) :
    ∀ r ∈ instBehaviours prof h (initI c h₀) c.toRef (importArgs c.imports),
      r = .instance (afterInstH Pf cs (c.afterFuncs Pf fun k => I.addrs.getD k 0) h₀) ⟨0⟩
        (exportMapI c) := by
  obtain ⟨trD, hq, ho, d⟩ := instI_detRunL (prof := prof) (hr := h.hr) (D := h.dispatch)
    hc hi har hF h₀
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc', -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartI c h₀ := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inl hc')
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMapI c) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), exportMapI c) :=
      Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartI c h₀ := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStartI c h₀ := hostRun_inv s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

end Prog

/-- **The instantiation phase with imports**: for a component in the fragment wired as
`SimpleI.toRef` assumes, instantiating `c.toRef` from the store of host functions of its
imports, with the root arguments `importArgs`, under any host, has no other result than the
instance at `afterInst P cs (c.afterFuncs P addr)` (export `i` at function `n + i`), where the
core store `cs` renames to the instance's store under `trampIdx` and has only trampoline host
code: the configuration of `CallPhaseI`. -/
def InstPhaseI : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : SimpleI), c.Good → c.Inst → c.Arity →
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3P P).Store (CanonHost (core3P P))),
      c.mod.IsInst I ∧ Store.mapH trampIdx cs = I.store ∧ c.TrampOk cs ∧
      ∀ (h : Host (core3P P) Unit),
        ∀ r ∈ instBehaviours prof h (Machine.Config.init (hostFuncs 0 c.imports CStore.empty) ())
            c.toRef (importArgs c.imports),
          r = .instance (afterInst P cs (c.afterFuncs P fun k => I.addrs.getD k 0)) ⟨0⟩
            (exportMapI c)

/-- **The instantiation phase with imports, at any host state type**: as `InstPhaseI`, for a
host with state of any type `σ` in initial state `h₀`, the result is the instance at
`afterInstH P cs (c.afterFuncs P addr) h₀` (instantiation does not touch the host state). -/
def InstPhaseIS : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : SimpleI), c.Good → c.Inst → c.Arity →
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3P P).Store (CanonHost (core3P P))),
      c.mod.IsInst I ∧ Store.mapH trampIdx cs = I.store ∧ c.TrampOk cs ∧
      ∀ (σ : Type) (h : Host (core3P P) σ) (h₀ : σ),
        ∀ r ∈ instBehaviours prof h (Machine.Config.init (hostFuncs 0 c.imports CStore.empty) h₀)
            c.toRef (importArgs c.imports),
          r = .instance (afterInstH P cs (c.afterFuncs P fun k => I.addrs.getD k 0) h₀) ⟨0⟩
            (exportMapI c)

/-- **The instantiation phase with imports holds at any host state type** (`InstPhaseIS`). -/
theorem instPhaseIS : InstPhaseIS := by
  intro P prof c hc hi har
  obtain ⟨I, cs, ci, hF⟩ := coreFactsI (Pf := P) hc hi
  exact ⟨I, cs, hF.isInst, hF.store, hF.tramp,
    fun _ h h₀ => instBehavioursI_toRef hc hi har hF prof h h₀⟩

/-- **The instantiation phase with imports holds** (`InstPhaseI`). -/
theorem instPhaseI : InstPhaseI := by
  intro P prof c hc hi har
  obtain ⟨I, cs, hI, hcs, htr, h⟩ := instPhaseIS P prof c hc hi har
  exact ⟨I, cs, hI, hcs, htr, fun hh => h Unit hh ()⟩

end Silmaril.Proofs.Wasm.Component.Reference
