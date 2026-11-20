module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkNames
public import Silmaril.Proofs.Wasm.Component.Reference.StartInst

/-!
# Nested instantiation of an import-free simple component after a function prefix

The first relocation lemma for parents with host imports. `instantiateCall_simple'`
(`InstLinkNames`, used by `Linked2.toRef`) instantiates the exporter in a store with **no**
component functions, so its export `i` is the lifted function `i`. In `HLinked2.toRef` the
parent's host imports come first, so the store already holds `o = host.length` host functions
when the exporter is instantiated.

* `toRefDefs_runO`: the definitions of `c.toRef` run in a store holding `o` component functions
  (and the empty core store). The lifted functions are allocated after them, and export `i`
  is component function `o + i`. This is `toRefDefs_run` (the case `o = 0`) with the offset
  form `exportsDefs_runO` (`StartInst`) of the export definitions.
* `instantiateCall_simpleO`: the dispatcher's nested instantiation of `c.toRef` in such a store,
  with its export map of functions and generated type names (`instantiateCall_simple'` is the
  case `o = 0`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} {R : Recurse (core3P Pf) σ}
  {inst : InstId} {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-- **The definitions of `c.toRef` run after `o` component functions**: export `i` is the lifted
function `o + i`. -/
theorem toRefDefs_runO {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (cfg : Machine.Config (core3P Pf) σ) {o : Nat}
    (hcore : cfg.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs.length = o) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {} c.toRef) cfg sc'
        { cfg with core := cs, store :=
            liftStore cfg.store (liftedList (fun k => I.addrs.getD k 0) inst c.exports) } ∧
      funcExports sc'.exports = c.exports.mapIdx (fun k x => (x.name, ⟨o + 0 + k⟩)) := by
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
  have hs : cfg.store.funcs.length = o + 0 := hfuncs
  obtain ⟨sc', hr, hx⟩ := exportsDefs_runO (R := R) (inst := inst) (outer := outer)
    (args := args) c.mod o (fun k => I.addrs.getD k 0) c.exports 0
    { frame := coreFrame c.mod.mod ((core3P Pf).exports ci), exports := [] }
    { cfg with core := cs } hinv hs hF.lookup
  refine ⟨sc', ?_, hx⟩
  unfold Simple.toRef
  exact TRuns.foldlM_append (TRuns.foldlM_cons (TRuns.of_eq cfg h₁)
    (TRuns.foldlM_cons h₂ (TRuns.foldlM_nil _ _))) hr

/-- **The nested instantiation of an import-free simple component after `o` component
functions**, with an export map of functions and generated type names: export `i` is the lifted
function `o + i`. -/
theorem instantiateCall_simpleO {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFacts c I cs ci) (outer : List (Frame (core3P Pf)))
    (cfg : Machine.Config (core3P Pf) σ) {o : Nat}
    (hcore : cfg.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs.length = o) :
    ∃ es, funcExports es = c.exports.mapIdx (fun k x => (x.name, ⟨o + k⟩)) ∧ TagOrFunc es ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ [] : P (core3P Pf) σ (Ret (core3P Pf))) cfg
        (.items es)
        (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := by
  obtain ⟨sc', hr, hx⟩ := toRefDefs_runO (R := callRecurse)
    (inst := nextInst cfg.store) (outer := outer)
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hmap : funcExports sc'.exports = c.exports.mapIdx (fun k x => (x.name, ⟨o + k⟩)) := by
    rw [hx]
    simp only [Nat.add_zero]
  have ht : TagOrFunc sc'.exports :=
    SRuns.rets (Q := fun sc : Scope (core3P Pf) => TagOrFunc sc.exports) hr
      (foldlM_rets (E := core3P Pf) (R := callRecurse) (inst := nextInst cfg.store)
        (outer := outer) (args := []) c.toRef {} (expName_toRef c) TagOrFunc.nil)
  refine ⟨sc'.exports, hmap, ht, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  have hr' : TRuns (List.foldlM (instantiateDef callRecurse (nextInst cfg.store) outer []) {}
      c.toRef) { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } sc'
      (nestCfg cs cfg (fun k => I.addrs.getD k 0) c) := hr
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr' (TRuns.pure _ _))

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
