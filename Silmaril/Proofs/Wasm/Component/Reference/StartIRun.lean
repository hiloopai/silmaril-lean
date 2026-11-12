module

public import Silmaril.Proofs.Wasm.Component.Reference.StartICall
public import Silmaril.Proofs.Wasm.Component.Reference.StartPhase
public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkDefs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation program of a component with imports and a start function, to the hole

`instIS_reaches`: the instantiation program of `c.toRef` (a module whose start function is at
`a`), from the store of host functions of the imports with the root arguments `importArgs`, runs
deterministically, without observations, to `runStart ⟨0⟩ a` (the imports, the core module, the
trampolines and the inline core instance as in `toRefDefsI_run`, then the core instantiation up
to its start function, `instEnv_reaches`); after the start function it runs the exports (lift
`n + 1 + i`, `exportsDefsAtL_run`) to `endCfgI`, observing `exportMapIS c`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)
open Silmaril.Wasm.Numerics (Profile)

variable {Pf : Profile} {σ : Type}
  {g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
    Option (List Silmaril.Wasm.Component.Value.Val × σ)}
  {prof : ProfileKind}

/-- The function exports of the root instance of `c.toRef` with a start function: export `i` is
function `n + 1 + i`, after the `n` imported functions and the lifted start function. -/
def exportMapIS (c : SimpleI) : List (String × FuncId) :=
  c.exports.mapIdx fun i x => (x.name, ⟨c.imports.length + 1 + i⟩)

/-! ## The root checks, for `SimpleI.InstS` -/

/-- Every import of `c.toRef` is supplied by `importArgs`. -/
theorem argsComplete_toRefS {c : SimpleI} (hnd : (c.imports.map (·.1)).Nodup) :
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
  rw [importArgs_lookup hnd j hj]
  rfl

/-- The import pre-check of `c.toRef` passes in a store holding the host functions of the
imports. -/
theorem precheck_toRefS {c : SimpleI} (hnd : (c.imports.map (·.1)).Nodup)
    (s : CStore (core3P Pf)) (hs : s.funcs = hostList 0 c.imports) :
    precheckImports s (importArgs c.imports) Frame.empty c.toRef = .ok () := by
  have hn := toRefTail_noImport Pf c
  obtain ⟨f', hP⟩ := importsDefs_pre (s := s) (args := importArgs c.imports) c.imports 0
    Frame.empty fun j hj =>
      ⟨by rw [Nat.zero_add]; exact importArgs_lookup hnd j hj,
       by rw [Nat.zero_add]; exact hostList_get hs j hj⟩
  rw [toRef_eq]
  exact (hP.1 _).trans (precheckImports_ok s _ f' _ hn)

/-! ## The core instantiation, to the start function -/

/-- **The core instantiation with `"env"` reaches the start function.** -/
theorem instEnv_reaches (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    {m : Silmaril.Wasm.Module} {xas : List (core3P Pf).ExternVal}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hm : sc.frame.coreModules = [m])
    (himp : coreImportsFor? cfg.store.core m [("env", 0)] sc.frame = some xas)
    (hp : (core3P Pf).prepare? cfg.store.core m xas = some (cs, ci, some a)) :
    ∃ tr, Reaches prof (answerHostS Pf g).hr (DA Pf g) none (runStart ⟨0⟩ a)
      (instantiateCore ⟨0⟩ sc.frame 0 [("env", 0)] : Canon.P (core3P Pf) σ _) cfg tr
      { cfg with store := setCoreSt cs cfg.store }
      (fun m₂ tr' r m' => RunsQ (DA Pf g) none (pure ((core3P Pf).exports ci)) m₂ tr' r m') ∧
      traceObs tr = [] := by
  have hmod : sc.frame.coreModule? 0 = some m := by rw [Frame.coreModule?, hm]; rfl
  have R₄ := Reaches.here (prof := prof) (hr := (answerHostS Pf g).hr) (dispatch := DA Pf g)
    (th := none) (X := runStart ⟨0⟩ a)
    (fun _ => (pure ((core3P Pf).exports ci) : Canon.P (core3P Pf) σ _))
    { cfg with store := setCoreSt cs cfg.store }
  have R₃ : Reaches prof (answerHostS Pf g).hr (DA Pf g) none (runStart ⟨0⟩ a)
      (Canon.modifyStore (setCoreSt cs) >>= fun _ =>
        (runStart ⟨0⟩ a >>= fun _ => (pure ((core3P Pf).exports ci) : Canon.P (core3P Pf) σ _)))
      cfg ([.tau] ++ []) { cfg with store := setCoreSt cs cfg.store }
      (fun m₂ tr' r m' => RunsQ (DA Pf g) none (pure ((core3P Pf).exports ci)) m₂ tr' r m') :=
    Reaches.seq (RunsQ.modify rfl (.pure () _)) R₄
  unfold instantiateCore
  rw [hmod]
  apply Exists.intro
  apply And.intro
  · apply Reaches.seq (RunsQ.pure _ _)
    apply Reaches.seq (RunsQ.get (.pure _ _))
    dsimp only
    rw [himp]
    apply Reaches.seq (RunsQ.pure _ _)
    rw [hp]
    exact R₃
  · simp [traceObs, Label.obs?]

/-! ## The definitions, to the start function -/

/-- `c.toRef` as the definitions before the core instantiation, the core instantiation and the
exports. -/
theorem toRef_eqS (c : SimpleI) :
    c.toRef = ((SimpleI.importsDefs c.imports 0).1 ++
      ([.coreModule c.mod.mod] ++ (c.imports.mapIdx fun k _ => .canon (.lower k [])) ++
        [.coreInstance (.exports (c.mod.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩)))])) ++
      (.coreInstance (.instantiate 0 [("env", 0)]) ::
        SimpleI.exportsDefsAt c.mod.exports 1 c.imports.length 0 c.exports
          (SimpleI.importsDefs c.imports 0).2) := by
  rw [toRef_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **The definitions of `c.toRef` reach the start function** from a store with the empty core
store and the host functions of the imports; after it (one more component function, the lifted
start function), they run the exports, lift `n + 1 + i`. -/
theorem toRefDefsIS_reaches {c : SimpleI} (hc : c.Good) (hi : c.InstS) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} {a : Nat} (hF : CoreFactsIS c I cs ci (some a))
    (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = hostList 0 c.imports) :
    ∃ tr Post, Reaches prof (answerHostS Pf g).hr (DA Pf g) none (runStart ⟨0⟩ a)
      (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs c.imports)) {} c.toRef) cfg tr
      { cfg with store := setCoreSt cs { cfg.store with core := trampStore Pf c.imports } } Post ∧
      traceObs tr = [] ∧
      ∀ m₂ : Machine.Config (core3P Pf) σ, m₂.store.funcs.length = c.imports.length + 1 →
        ∃ tr' sc', Post m₂ tr' sc' { m₂ with store := { m₂.store with
          funcs := m₂.store.funcs ++ liftedList (fun k => I.addrs.getD k 0) ⟨0⟩ c.exports } } ∧
          traceObs tr' = [] ∧ funcExports sc'.exports = exportMapIS c := by
  have hget : ∀ j (hj : j < c.imports.length), ArenaField.funcs.get? cfg.store ⟨j⟩ =
      some (.host (witFt c.imports[j].2) ⟨j⟩) := hostList_get hfuncs
  -- the imports
  obtain ⟨scA, rA, ⟨newA, hfA⟩, hlA, hxA⟩ := importsDefs_run (R := callRecurse) (inst := ⟨0⟩)
    (outer := []) c.imports 0 {} cfg fun j hj =>
      ⟨by rw [Nat.zero_add]; exact importArgs_lookup hi.importNames j hj,
       by rw [Nat.zero_add]; exact hget j hj⟩
  have hlenm : c.mod.imports.length = c.imports.length := by rw [hc.imports, List.length_map]
  -- the core module
  have rB := instDef_coreModule (σ := σ) (R := callRecurse) (inst := ⟨0⟩) (outer := [])
    (args := importArgs c.imports) scA c.mod.mod
  -- the trampolines
  have hfB : ∀ j < c.imports.length,
      ({ scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module) } :
        Frame (core3P Pf)).funcs[j]? = some ⟨j⟩ := by
    intro j hj
    show scA.frame.funcs[j]? = _
    rw [hfA]
    simp [hj, Frame.empty]
  have rC := lowers_run (R := callRecurse) (outer := []) (args := importArgs c.imports)
    (arity_imports har) c.imports.length 0
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module) } }
    cfg (Nat.zero_add _) hfB (by rw [hcore]; rfl) hget
  -- the inline core instance
  have hcfC : (scA.frame.coreFuncs ++ addrList Pf (List.range' 0 c.imports.length)) =
      List.range c.mod.imports.length := by
    rw [hfA, hlenm, List.range_eq_range']
    rfl
  have rD := coreExports_run (R := callRecurse) (inst := ⟨0⟩) (outer := [])
    (args := importArgs c.imports)
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
                                         coreFuncs := scA.frame.coreFuncs ++
                                           addrList Pf (List.range' 0 c.imports.length) } }
    { cfg with store := { cfg.store with core := trampStore Pf c.imports } } c.mod.imports hcfC
  rw [← lowers_eq] at rC
  have hpre := TRuns.foldlM_append rA (TRuns.foldlM_append (TRuns.foldlM_append
    (TRuns.foldlM_cons (TRuns.of_eq cfg rB) (TRuns.foldlM_nil _ _)) rC)
    (TRuns.foldlM_cons rD (TRuns.foldlM_nil _ _)))
  -- the core instantiation, to the start function
  have hmE : (scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module)) =
      ([c.mod.mod] : List (core3P Pf).Module) := by rw [hfA]; rfl
  have hciE : (scA.frame.coreInstances ++
      ([envExports c.mod.imports] : List (List (String × (core3P Pf).ExternVal))))[0]? =
      some (envExports c.mod.imports) := by rw [hfA]; rfl
  obtain ⟨trE, RE, hoE⟩ := instEnv_reaches (prof := prof) (g := g)
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
                                         coreFuncs := scA.frame.coreFuncs ++
                                           addrList Pf (List.range' 0 c.imports.length),
                                         coreInstances := scA.frame.coreInstances ++
                                           ([envExports c.mod.imports] :
                                             List (List (String × (core3P Pf).ExternVal))) } }
    { cfg with store := { cfg.store with core := trampStore Pf c.imports } } hmE
    (hF.imports _ hciE) hF.prepare
  -- the frame of the core instantiation
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
  have hlA' : scA.frame.types.length = (SimpleI.importsDefs c.imports 0).2 := hlA
  have R₁ := Reaches.left (g := fun es => (pure { scA with frame := { scA.frame with
      coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
      coreFuncs := scA.frame.coreFuncs ++ addrList Pf (List.range' 0 c.imports.length),
      coreInstances := scA.frame.coreInstances ++
        ([envExports c.mod.imports] : List (List (String × (core3P Pf).ExternVal))) ++ [es] } } :
      Canon.P (core3P Pf) σ (Scope (core3P Pf)))) RE
  have R₂ := Reaches.left (g := fun sc => List.foldlM
    (instantiateDef callRecurse ⟨0⟩ [] (importArgs c.imports)) sc
    (SimpleI.exportsDefsAt c.mod.exports 1 c.imports.length 0 c.exports
      (SimpleI.importsDefs c.imports 0).2)) R₁
  obtain ⟨tr, R₃, ho⟩ := Reaches.seqT (g := fun sc => List.foldlM
    (instantiateDef callRecurse ⟨0⟩ [] (importArgs c.imports)) sc
    (.coreInstance (.instantiate 0 [("env", 0)]) ::
      SimpleI.exportsDefsAt c.mod.exports 1 c.imports.length 0 c.exports
        (SimpleI.importsDefs c.imports 0).2)) hpre (by exact R₂)
  refine ⟨tr, _, by rw [toRef_eqS]; erw [List.foldlM_append]; exact R₃, ho.trans hoE, ?_⟩
  · intro m₂ hf
    obtain ⟨scF, rF, hxF⟩ := exportsDefsAtL_run (R := callRecurse) (inst := ⟨0⟩) (outer := [])
      (args := importArgs c.imports) c.mod.exports 1 c.imports.length (c.imports.length + 1)
      (fun k => I.addrs.getD k 0) c.exports 0
      { scA with frame := { scA.frame with
          coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3P Pf).Module),
          coreFuncs := scA.frame.coreFuncs ++ addrList Pf (List.range' 0 c.imports.length),
          coreInstances := scA.frame.coreInstances ++
            ([envExports c.mod.imports] : List (List (String × (core3P Pf).ExternVal))) ++
              [(core3P Pf).exports ci] } }
      m₂ hinv hf (fun x hx => hF.lookup x hx)
    rw [hlA'] at rF
    obtain ⟨tr₂, hr₂, ho₂⟩ := SRuns.runsQO (dispatch := DA Pf g) rF none
    refine ⟨_, scF, ⟨_, _, _, _, ⟨_, _, _, _, .pure _ _, .pure _ _, rfl⟩, hr₂, rfl⟩, ?_, ?_⟩
    · simpa [traceObs] using ho₂
    · have hx₀ : funcExports scA.exports = [] := hxA
      rw [hxF]
      show funcExports scA.exports ++ _ = _
      rw [hx₀, List.nil_append, exportMapIS]

/-! ## The instantiation program -/

/-- The initial configuration of `exportBehavioursI`, with the store of host functions in
closed form. -/
def initIS (c : SimpleI) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  Machine.Config.init { (CStore.empty : CStore (core3P Pf)) with funcs := hostList 0 c.imports } h₀

theorem initI_eq (c : SimpleI) (h₀ : σ) :
    (initI c h₀ : Machine.Config (core3P Pf) σ) = initIS c h₀ := by
  simp only [initI, initIS, hostFuncs_eq]
  rfl

/-- The configuration at the start of the definitions: the store of host functions, nesting
incremented, instance `0` allocated. -/
def allocCfgI (c : SimpleI) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  { (initIS c h₀ : Machine.Config (core3P Pf) σ) with
    store := ArenaOps.allocSt ArenaField.insts {}
      (DispatchSt.incNestingSt (initIS c h₀ : Machine.Config (core3P Pf) σ).store) }

/-- The configuration at the start function: the trampolines allocated and the core store `cs`
installed. -/
def holeCfgI (c : SimpleI) (h₀ : σ) (cs : (core3P Pf).Store (CanonHost (core3P Pf))) :
    Machine.Config (core3P Pf) σ :=
  { (allocCfgI c h₀ : Machine.Config (core3P Pf) σ) with
    store := setCoreSt cs
      { (allocCfgI c h₀ : Machine.Config (core3P Pf) σ).store with core := trampStore Pf c.imports } }

/-- The configuration at the end of the instantiation program, from the configuration `m₂` after
the start function. -/
def endCfgI (m₂ : Machine.Config (core3P Pf) σ) (addr : Nat → Nat) (c : SimpleI) :
    Machine.Config (core3P Pf) σ :=
  let s : CStore (core3P Pf) :=
    { m₂.store with funcs := m₂.store.funcs ++ liftedList addr ⟨0⟩ c.exports }
  { m₂ with store := DispatchSt.decNestingSt s }

theorem initIS_funcs (c : SimpleI) (h₀ : σ) :
    (initIS c h₀ : Machine.Config (core3P Pf) σ).store.funcs = hostList 0 c.imports := rfl

theorem runsQ_checkImportA {th : Option ThreadId} {r : Except String Unit} (hr : r = .ok ())
    (m : Machine.Config (core3P Pf) σ) :
    RunsQ (DA Pf g) th (checkImport r : Canon.P (core3P Pf) σ Unit) m [] () m := by
  subst hr
  exact .pure _ _

/-- **The instantiation program reaches the start function**, without observations; after it,
the program runs to `endCfgI`, observing the instance and the export map `exportMapIS c`. -/
theorem instIS_reaches {c : SimpleI} (hc : c.Good) (hi : c.InstS) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} {a : Nat} (hF : CoreFactsIS c I cs ci (some a)) (h₀ : σ) :
    ∃ tr Post, Reaches prof (answerHostS Pf g).hr (DA Pf g) none (runStart ⟨0⟩ a)
      (instantiateProg c.toRef (importArgs c.imports) : Canon.P (core3P Pf) σ _) (initIS c h₀) tr
      (holeCfgI c h₀ cs) Post ∧ traceObs tr = [] ∧
      ∀ m₂ : Machine.Config (core3P Pf) σ, m₂.store.funcs.length = c.imports.length + 1 →
        ∃ tr', Post m₂ tr' .unit (endCfgI m₂ (fun k => I.addrs.getD k 0) c) ∧
          traceObs tr' = [instantiatedObs ⟨0⟩ (exportMapIS c)] := by
  obtain ⟨tr₀, Post₀, R₀, ho₀, hP₀⟩ := toRefDefsIS_reaches (prof := prof) (g := g) hc hi har hF
    (allocCfgI c h₀) rfl (initIS_funcs c h₀)
  have R₁ := Reaches.left (g := fun sc => (pure sc.exports :
    Canon.P (core3P Pf) σ (Exports (core3P Pf)))) R₀
  have R₂ := Reaches.left (g := fun es => (pure ((⟨0⟩ : InstId), es) :
    Canon.P (core3P Pf) σ (InstId × Exports (core3P Pf)))) R₁
  have hac : argsComplete c.toRef (importArgs c.imports : Exports (core3P Pf)) = true :=
    argsComplete_toRefS hi.importNames
  have hpre : precheckImports (DispatchSt.incNestingSt (initIS c h₀ :
      Machine.Config (core3P Pf) σ).store) (importArgs c.imports) Frame.empty c.toRef = .ok () :=
    precheck_toRefS (Pf := Pf) hi.importNames
    (DispatchSt.incNestingSt (initIS c h₀ : Machine.Config (core3P Pf) σ).store) (initIS_funcs c h₀)
  have hid : (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size
      (DispatchSt.incNestingSt (initIS c h₀ : Machine.Config (core3P Pf) σ).store)) =
      (⟨0⟩ : InstId) := rfl
  exact ⟨_, _, by
    unfold instantiateProg
    apply Reaches.seq (runs_modifyStore (impl := answerImplS g) DispatchSt.incNestingSt
      (initIS c h₀ : Machine.Config (core3P Pf) σ) rfl)
    dsimp only
    apply Reaches.left
    unfold instantiateRootCall instantiateRoot
    apply Reaches.seq (runs_trapIf (impl := answerImplS g) ((congrArg (!·) hac).trans rfl) _ _)
    apply Reaches.seq (RunsQ.get (.pure _ _))
    apply Reaches.seq (runsQ_checkImportA hpre _)
    apply Reaches.seq (runs_allocObj ArenaField.insts {} _ rfl)
    rw [hid]
    exact R₂, by simpa [traceObs, Label.obs?] using ho₀, by
    intro m₂ hf
    obtain ⟨tr', sc', hP, ho', hx⟩ := hP₀ m₂ hf
    refine ⟨_, ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, hP, .pure _ _, rfl⟩, .pure _ _, rfl⟩,
      RunsQ.modify rfl (RunsQ.emit (by exact RunsQ.pure _ _)), rfl⟩, ?_⟩
    simp only [traceObs_append, ho']
    simp only [traceObs, List.nil_append, hx]
    rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference
