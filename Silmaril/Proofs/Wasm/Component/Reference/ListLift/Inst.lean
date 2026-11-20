module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.InstDefs

/-!
# The instantiation phase of `ListComp.toRef`

As for simple components (`Silmaril.Proofs.Wasm.Component.Reference.InstRun`), instantiating
`c.toRef` from the empty store is a silent deterministic run (`SRuns`) of the instantiation
program: the root checks pass (no imports), the root instance `0` is allocated and the
definitions run (`toRefDefs_runL`). With the host event before and the end of the host frame
after, every machine run of the instantiation follows it (`DetRunL.inv`).

The root part is stated for any import-free component whose definitions run silently to
`liftStore` (`rootCall_runG`, `instProg_runG`, `instBehaviours_runG`); `instPhaseL` applies it
to `ListComp.toRef`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

section Root

variable {Pf : Profile}

/-- The definitions `ds` run silently from every configuration with the empty core store and
no component function, to the core store `cs` and the component functions `fs`, recording the
function exports `em`. -/
def DefsRun (ds : Core3Component) (cs : (core3P Pf).Store (CanonHost (core3P Pf)))
    (fs : List (CFuncInst (core3P Pf))) (em : List (String × FuncId)) : Prop :=
  ∀ cfg : Machine.Config (core3P Pf) Unit, cfg.core = (core3P Pf).empty _ →
    cfg.store.funcs = [] →
    ∃ sc', TRuns (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] []) {} ds) cfg sc'
        { cfg with core := cs, store := liftStore cfg.store fs } ∧
      funcExports sc'.exports = em

/-- **Root instantiation of an import-free component runs silently**: the root checks pass,
instance `0` is allocated, and the definitions run. -/
theorem rootCall_runG {ds : Core3Component} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {fs : List (CFuncInst (core3P Pf))} {em : List (String × FuncId)} (hn : NoImport ds)
    (hrun : DefsRun ds cs fs em) (cfg : Machine.Config (core3P Pf) Unit)
    (hcore : cfg.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = [])
    (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = em ∧
      TRuns (instantiateRootCall ds [] : P (core3P Pf) Unit _) cfg (⟨0⟩, es)
        { cfg with core := cs, store := liftStore (ArenaOps.allocSt ArenaField.insts {} cfg.store) fs } := by
  obtain ⟨sc', hr, hx⟩ := hrun { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hac : argsComplete ds ([] : Exports (core3P Pf)) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  have hpre : ∀ s : CStore (core3P Pf), precheckImports s [] Frame.empty ds = .ok () :=
    fun s => precheckImports_ok s [] _ _ hn
  have hid : (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  refine ⟨sc'.exports, hx, ?_⟩
  unfold instantiateRootCall instantiateRoot
  refine (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg).bind ((TRuns.getStore cfg).bind ?_)
  refine (checkImport_run (hpre _) cfg).bind
    ((TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind ?_)
  rw [hid]
  exact (hr.bind (f := fun sc => Pure.pure sc.exports) (TRuns.pure _ _)).bind
    (f := fun es => Pure.pure ((⟨0⟩ : InstId), es)) (TRuns.pure _ _)

/-- **The instantiation program runs silently** from the initial configuration to `afterInst`,
observing the root instance `0` and the export map. -/
theorem instProg_runG {ds : Core3Component} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {fs : List (CFuncInst (core3P Pf))} {em : List (String × FuncId)} (hn : NoImport ds)
    (hrun : DefsRun ds cs fs em) :
    SRuns (instantiateProg ds [] : P (core3P Pf) Unit (Ret (core3P Pf))) (initConfig ())
      [instantiatedObs ⟨0⟩ em] .unit (afterInst Pf cs fs) := by
  obtain ⟨es, hes, hr⟩ := rootCall_runG hn hrun
    { (initConfig () : Machine.Config (core3P Pf) Unit) with
      store := DispatchSt.incNestingSt (initConfig () : Machine.Config (core3P Pf) Unit).store }
    rfl rfl rfl
  unfold instantiateProg
  refine SRuns.bind (os₁ := [])
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _) ?_
  refine SRuns.bind (os₁ := []) hr ?_
  dsimp only
  rw [hes]
  exact SRuns.bind (os₁ := []) (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)
    (.emit (.pure _ _))

/-- The configuration after the instantiation host event. -/
noncomputable def instStartG (ds : Core3Component) : Machine.Config (core3P Pf) Unit :=
  { (initConfig () : Machine.Config (core3P Pf) Unit) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg ds []))] }

/-- **The instantiation is one deterministic run** from the host event to `afterInst`. -/
theorem inst_detRunLG {prof : ProfileKind} {hr : HostReady Unit}
    {D : Call (core3P Pf) → P (core3P Pf) Unit (Ret (core3P Pf))} {ds : Core3Component}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {fs : List (CFuncInst (core3P Pf))}
    {em : List (String × FuncId)} (hn : NoImport ds) (hrun : DefsRun ds cs fs em) :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ em] ∧
      DetRunL prof hr D (instStartG ds) tr (afterInst Pf cs fs) := by
  obtain ⟨tr, hq, ho, d⟩ := (instProg_runG hn hrun).detRunL (prof := prof) (hr := hr)
    (dispatch := D) rfl none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterInst Pf cs fs with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterInst Pf cs fs) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, d.trans (.cons rfl s (.refl rfl))⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl

/-- **The results of instantiating an import-free component whose definitions run silently**:
the only one is the instance at `afterInst` with root instance `0` and the export map `em`. -/
theorem instBehaviours_runG {ds : Core3Component}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {fs : List (CFuncInst (core3P Pf))}
    {em : List (String × FuncId)} (hn : NoImport ds) (hrun : DefsRun ds cs fs em)
    (prof : ProfileKind) :
    ∀ r ∈ instBehaviours prof (refHost Pf) (initConfig ()) ds [],
      r = .instance (afterInst Pf cs fs) ⟨0⟩ em := by
  obtain ⟨trD, hq, ho, d⟩ := inst_detRunLG (prof := prof) (hr := (refHost Pf).hr)
    (D := (refHost Pf).dispatch) hn hrun
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn', hc, -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartG ds := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn' (.inl hc)
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, em) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), em) := Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn', -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartG ds := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn' (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStartG ds := hostRun_inv s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

end Root

/-- **The instantiation phase** of `ListComp.toRef` (`InstPhaseL`). -/
theorem instPhaseL : InstPhaseL := by
  intro Pf prof c I _ hi
  obtain ⟨cs, ci, hF⟩ := coreFactsL (Pf := Pf) hi
  have hn : NoImport c.toRef := by
    obtain ⟨-, -, -, hn⟩ := toRefDefs_runL (R := callRecurse) (inst := ⟨0⟩) (outer := [])
      (args := []) hF hi (initConfig () : Machine.Config (core3P Pf) Unit) rfl rfl
    exact hn
  have hrun : DefsRun c.toRef cs (liftedFuncsL Pf c I) (exportMapL c) := by
    intro cfg hcore hfuncs
    obtain ⟨sc', hr, hx, -⟩ := toRefDefs_runL (R := callRecurse) (inst := ⟨0⟩) (outer := [])
      (args := []) hF hi cfg hcore hfuncs
    exact ⟨sc', hr, hx⟩
  exact ⟨cs, hF.store, instBehaviours_runG hn hrun prof⟩

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
