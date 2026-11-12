module

public import Silmaril.Proofs.Wasm.Component.Reference.InstRun
public import Silmaril.Proofs.Wasm.Component.Reference.CallBase

/-!
# Nested instantiation of an import-free simple component

The first step of the instantiation of `Linked2.toRef`: the parent's `instantiate 0` is the
late-bound call `Call.instantiate cl []` of the dispatcher (`instantiateCallProg`): allocate a
fresh component instance and run the child's definitions in it. For an import-free `Simple`
child whose definitions start from an empty core store and no component function (which holds
in the parent: its definitions before `instantiate 0` are the two `component` closures), the
call runs silently to the same store as root instantiation, with the instance id the next free
one and the exports `exportMap` (`instantiateCall_simple`, from `toRefDefs_run`).

`SRuns.runsQ`: silent runs (which make no late-bound calls) are big-step runs `RunsQ` of any
dispatcher, whose `call` constructor runs the nested instantiation inside the parent's program.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine

/-! ## Silent runs are big-step runs -/

section Embed

variable {E : CoreEngine} {σ : Type} {dispatch : Call E → P E σ (Ret E)}

/-- **A silent run is a big-step run** of any dispatcher, from any thread, with `tau` labels
and the run's observations. -/
theorem SRuns.runsQ {α : Type} {p : P E σ α} {m m' : Machine.Config E σ} {os : List HostObs}
    {a : α} (h : SRuns p m os a m') (th : Option ThreadId) :
    ∃ tr, RunsQ dispatch th p m tr a m' ∧ SRuns.Quiet tr := by
  induction h with
  | pure a m => exact ⟨[], .pure a m, fun _ h => nomatch h⟩
  | get _ ih =>
    obtain ⟨tr, hr, hq⟩ := ih
    exact ⟨_, .get hr, SRuns.Quiet.cons (.inl rfl) hq⟩
  | modify hf _ ih =>
    obtain ⟨tr, hr, hq⟩ := ih
    exact ⟨_, .modify (hf _) hr, SRuns.Quiet.cons (.inl rfl) hq⟩
  | @emit o _ _ _ _ _ _ ih =>
    obtain ⟨tr, hr, hq⟩ := ih
    exact ⟨_, .emit hr, SRuns.Quiet.cons (.inr ⟨o, rfl⟩) hq⟩

end Embed

/-! ## The nested instantiation of a simple component -/

section Nest

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type}

/-- The store after the nested instantiation of a simple component in the instance allocated
next: as `instStore`, at an arbitrary instance id. -/
noncomputable def nestStore (cs : (core3P Pf).Store (CanonHost (core3P Pf)))
    (s : CStore (core3P Pf)) (addr : Nat → Nat) (inst : InstId) (c : Simple) :
    CStore (core3P Pf) :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr inst c.exports)

/-- The id of the next component instance. -/
noncomputable abbrev nextInst (s : CStore (core3P Pf)) : InstId :=
  (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size s)

/-- The configuration after the nested instantiation. -/
noncomputable def nestCfg (cs : (core3P Pf).Store (CanonHost (core3P Pf)))
    (cfg : Machine.Config (core3P Pf) σ) (addr : Nat → Nat) (c : Simple) :
    Machine.Config (core3P Pf) σ :=
  { cfg with store := nestStore cs cfg.store addr (nextInst cfg.store) c }

/-- **The nested instantiation of an import-free simple component runs silently**: from a store
with the empty core store and no component function, the dispatcher's program for
`Call.instantiate ⟨c.toRef, outer⟩ []` allocates the next instance `inst`, instantiates the core
module and allocates one lifted function per export, answering the export map. -/
theorem instantiateCall_simple {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (outer : List (Frame (core3P Pf)))
    (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.store.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ es, funcExports es = exportMap c ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ [] : P (core3P Pf) σ (Ret (core3P Pf))) cfg
        (.items es)
        (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := by
  obtain ⟨sc', hr, hx, -⟩ := toRefDefs_run (R := callRecurse)
    (inst := nextInst cfg.store) (outer := outer)
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hmap : funcExports sc'.exports = exportMap c := by
    rw [hx, exportMap]
    simp only [Nat.zero_add]
  refine ⟨sc'.exports, hmap, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  have hr' : TRuns (List.foldlM (instantiateDef callRecurse (nextInst cfg.store) outer []) {}
      c.toRef) { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } sc'
      (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := hr
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr' (TRuns.pure _ _))

end Nest

end Silmaril.Proofs.Wasm.Component.Reference
