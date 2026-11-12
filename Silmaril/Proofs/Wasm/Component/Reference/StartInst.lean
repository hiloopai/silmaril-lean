module

public import Silmaril.Proofs.Wasm.Component.Reference.StartCall
public import Silmaril.Proofs.Wasm.Component.Reference.InstNest
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Instantiating a simple component whose module has a start function

* `exportsDefs_runO`: the export definitions of `Simple.toRef` when the store already holds `o`
  component functions (the lifted start function): export `i` is the lifted function `o + i`.
* `CoreFactsS`, `coreFactsS`: the core instantiation of a module with an instance before its
  start function (`NumModule.IsInstS`) returns the start address.
* `instS_reaches`: the instantiation program of `c.toRef` runs deterministically, without
  observations, to `runStart ⟨0⟩ a`; after the start function it runs to `afterStartCfg`, the
  configuration between calls (`readyCfg`) with the start function's leftovers (`startGarb`) and
  the functions `startFn a :: liftedFuncs`, observing the export map `exportMapS c`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

/-! ## Export definitions after the start function -/

section Offset

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} {R : Recurse (core3P Pf) σ}
  {inst : InstId} {outer : List (Silmaril.Wasm.Execution.Core.Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-- The `canon lift` of export `i` allocates component function `o + i`. -/
theorem lift_runO (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ) {o i ft a : Nat}
    {t : Types.FuncType RtId} (hs : cfg.store.funcs.length = o + i)
    (ha : sc.frame.coreFuncs[i]? = some a) (ht : sc.frame.types[ft]? = some (.func t)) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lift i [] ft))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨o + i⟩] } }
      { cfg with store := ArenaOps.allocSt ArenaField.funcs (.lifted a t {} inst) cfg.store } := by
  rw [instDef_lift sc ha ht, ← hs]
  exact (TRuns.allocObj _ (fun _ _ => rfl) _ cfg).bind (TRuns.pure _ _)

/-- The definitions of one export, at offset `o`. -/
theorem exportDefs_runO (m : NumModule) (o i : Nat) (x : SimpleExport) (sc : Scope (core3P Pf))
    (cfg : Machine.Config (core3P Pf) σ) {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)}
    {a : (core3P Pf).FuncAddr} (hinv : ExpInv es₀ i sc.frame) (hs : cfg.store.funcs.length = o + i)
    (hlk : lookupExport? es₀ (((m.exports[x.core]?).map (·.1)).getD "") = some (.func a)) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (Simple.exportDefs m i x sc.frame.types.length).1) cfg sc'
        { cfg with store :=
            ArenaOps.allocSt ArenaField.funcs (.lifted a (liftedFt x) {} inst) cfg.store } ∧
      ExpInv es₀ (i + 1) sc'.frame ∧
      sc'.frame.types.length = (Simple.exportDefs m i x sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports ++ [(x.name, ⟨o + i⟩)] := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3P Pf).Module) x.ty.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3P Pf).Module) x.ty.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [exportDefs_eq, ← hl₁, ← hl₂]
  have hinv₂ : ExpInv es₀ i sc₂.frame := hP₂.expInv (hP₁.expInv hinv)
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3P Pf).Module) x.ty.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3P Pf).Module) x.ty.results
          sc₁.frame.types.length).1.head? } = some (liftedFt x) :=
    resolveFuncType_lifted (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := instDef_func (R := R) (inst := inst) (outer := outer) (args := args) sc₂ hft
  have hci : (Frame.coreInstance? { sc₂.frame with types := sc₂.frame.types ++
      [.func (liftedFt x)] } 0) = some es₀ := by
    show sc₂.frame.coreInstances[0]? = some es₀
    rw [hinv₂.ci]
    rfl
  have h₄ := instDef_alias (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    { sc₂ with frame := { sc₂.frame with types := sc₂.frame.types ++ [.func (liftedFt x)] } }
    hci hlk rfl
  have hcf : (sc₂.frame.coreFuncs ++ [a])[i]? = some a := by
    rw [List.getElem?_append_right (by rw [hinv₂.cf]), hinv₂.cf, Nat.sub_self]
    rfl
  have hty : (sc₂.frame.types ++ [.func (liftedFt x)])[sc₂.frame.types.length]? =
      some (.func (liftedFt x)) := by simp
  have h₅ := lift_runO (R := R) (inst := inst) (outer := outer) (args := args)
    { sc₂ with frame := { sc₂.frame with
        types := sc₂.frame.types ++ [Types.TypeDef.func (liftedFt x)],
        coreFuncs := sc₂.frame.coreFuncs ++ [a] } } cfg hs hcf hty
  have hfn : (sc₂.frame.funcs ++ [(⟨o + i⟩ : FuncId)])[2 * i]? = some ⟨o + i⟩ := by
    rw [List.getElem?_append_right (by rw [hinv₂.fn]), hinv₂.fn, Nat.sub_self]
    rfl
  have h₆ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    (nm := { name := x.name })
    { sc₂ with frame := { sc₂.frame with
        types := sc₂.frame.types ++ [Types.TypeDef.func (liftedFt x)],
        coreFuncs := sc₂.frame.coreFuncs ++ [a], funcs := sc₂.frame.funcs ++ [⟨o + i⟩] } } hfn
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons (TRuns.of_eq cfg h₄) (TRuns.foldlM_cons h₅
    (TRuns.foldlM_cons (TRuns.of_eq _ h₆) (TRuns.foldlM_nil _ _))))), ?_, ?_, ?_⟩
  · exact ⟨hinv₂.ci, by simp [hinv₂.cf], by simp [hinv₂.fn]; omega⟩
  · simp
  · have hx : funcExports sc₂.exports = funcExports sc.exports := hP₂.2.2.2.1.trans hP₁.2.2.2.1
    rw [funcExports_append_func, hx]

/-- **The definitions of all exports, at offset `o`**: export `i + k` is component function
`o + i + k`. -/
theorem exportsDefs_runO (m : NumModule) (o : Nat) (addr : Nat → (core3P Pf).FuncAddr)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} :
    ∀ (xs : List SimpleExport) (i : Nat) (sc : Scope (core3P Pf))
      (cfg : Machine.Config (core3P Pf) σ), ExpInv es₀ i sc.frame →
      cfg.store.funcs.length = o + i →
      (∀ x ∈ xs, lookupExport? es₀ (coreName m x) = some (.func (addr x.core))) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          (Simple.exportsDefs m i xs sc.frame.types.length)) cfg sc'
          { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst xs } } ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun k x => (x.name, ⟨o + i + k⟩))
  | [], i, sc, cfg, _, _, _ => by
    refine ⟨sc, ?_, by rw [List.mapIdx_nil, List.append_nil]⟩
    simp only [liftedList, List.map_nil, List.append_nil]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, i, sc, cfg, hinv, hs, hlk => by
    obtain ⟨sc₁, hr₁, hinv₁, hl₁, hx₁⟩ := exportDefs_runO (R := R) (inst := inst)
      (outer := outer) (args := args) m o i x sc cfg hinv hs (hlk x List.mem_cons_self)
    have hs₁ : (cfg.store.funcs ++ liftedList addr inst [x]).length = o + (i + 1) := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, hr₂, hx₂⟩ := exportsDefs_runO m o addr xs (i + 1) sc₁
      { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst [x] } }
      hinv₁ hs₁ (fun y hy => hlk y (List.mem_cons_of_mem _ hy))
    rw [exportsDefs_cons]
    refine ⟨sc₂, ?_, ?_⟩
    · rw [liftedList_cons, ← List.append_assoc]
      exact TRuns.foldlM_append hr₁ (hl₁ ▸ hr₂)
    · rw [hx₂, hx₁, List.mapIdx_cons, List.append_assoc, Nat.add_zero, ← Nat.add_assoc,
        mapIdx_shift]
      rfl

end Offset

/-! ## Silent runs with their observations -/

section Embed

variable {E : CoreEngine} {σ : Type} {dispatch : Call E → Canon.P E σ (Ret E)}

/-- A silent run is a big-step run of any dispatcher whose observations are those of the run. -/
theorem SRuns.runsQO {α : Type} {p : Canon.P E σ α} {m m' : Machine.Config E σ}
    {os : List HostObs} {a : α} (h : SRuns p m os a m') (th : Option ThreadId) :
    ∃ tr, RunsQ dispatch th p m tr a m' ∧ traceObs tr = os := by
  induction h with
  | pure a m => exact ⟨[], .pure a m, rfl⟩
  | get _ ih =>
    obtain ⟨tr, hr, ho⟩ := ih
    exact ⟨_, .get hr, ho⟩
  | modify hf _ ih =>
    obtain ⟨tr, hr, ho⟩ := ih
    exact ⟨_, .modify (hf _) hr, ho⟩
  | @emit o _ _ _ _ _ _ ih =>
    obtain ⟨tr, hr, ho⟩ := ih
    exact ⟨_, .emit hr, congrArg (o :: ·) ho⟩

end Embed

/-! ## The core instantiation with a start function -/

section Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {Pf : Silmaril.Wasm.Numerics.Profile}

/-- The core facts of a `Simple.InstS` component with the start function at `a`. -/
structure CoreFactsS (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (ci : (core3P Pf).Inst) (st : Option Nat) :
    Prop where
  isInst : c.mod.IsInstS I st
  store : Store.mapH (fun _ => 0) cs = I.store
  imports : (core3P Pf).importTypes c.mod.mod = []
  prepare : (core3P Pf).prepare? ((core3P Pf).empty _) c.mod.mod [] = some (cs, ci, st)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3P Pf).exports ci) (coreName c.mod x) =
    some (.func (I.addrs.getD x.core 0))

/-- **The core facts hold** for a `Simple.InstS` component. -/
theorem coreFactsS {c : Simple} (hc : c.Good) (hi : c.InstS) :
    ∃ I st cs ci, CoreFactsS (Pf := Pf) c I cs ci st := by
  obtain ⟨I, st, hI⟩ := hi.inst
  obtain ⟨⟨mt, hIs⟩, himp, -⟩ := id hI
  have hfn : Validation.CExternType.funcs mt.imports = [] :=
    List.forall₂_nil_right_iff.1 (himp ▸ hIs.importTypes)
  have hmt : mt.imports = [] := nil_of_funcs_nil hIs.funcImports hfn
  obtain ⟨f, st₀, hf, haddr, hrel⟩ := hIs.instantiated
  have hf₀ : instantiateOnce? (Silmaril.Wasm.Game.importStore []) c.mod.mod [] =
      some (I.store, f, st₀) := by
    rw [← hf, hmt]
    rfl
  have hf' : mapS (fun _ => 0) (instantiateOnce? ({} : Store (CanonHost (core3P Pf))) c.mod.mod [])
      = some (I.store, f, st₀) := by
    rw [← instantiateOnce?_importStore (fun _ => 0), hf₀]
  obtain ⟨cs, ho, hs⟩ := mapS_eq_some hf'
  have hi₀ : c.noStart.Inst := ⟨⟨I, hI.noStart⟩, hi.names⟩
  have ho₀ : instantiateOnce? ({} : Store (CanonHost (core3P Pf))) c.noStart.mod.mod [] =
      some (cs, f, none) := by
    show instantiateOnce? _ { c.mod.mod with start := none } _ = _
    rw [instantiateOnce?_noStart, ho]
    rfl
  have hv : Validation.validate? c.mod.mod = some mt := hIs.valid
  have hprep : (core3P Pf).prepare? ((core3P Pf).empty _) c.mod.mod [] = some (cs, f.module, st) := by
    show Core3.prepareE? {} c.mod.mod [] = _
    simp only [Core3.prepareE?, hv, hmt, ho, externAddrsOk?, ite_true]
    cases hrel with
    | none => rfl
    | some hx => simp only [hx]; rfl
  refine ⟨I, st, cs, f.module, hI, hs, importTypes_core3P Pf hv hmt, hprep, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hc.core x hx
  have hname : coreName c.mod x = n := by rw [coreName, hn]; rfl
  rw [hname, exports_core3P]
  exact lookup_funcExport hi₀ (validate?_noStart hv) ho₀ haddr hn

end Core

end Silmaril.Proofs.Wasm.Component.Reference
