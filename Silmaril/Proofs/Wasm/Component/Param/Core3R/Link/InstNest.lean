module

public import Silmaril.Proofs.Wasm.Component.Reference.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstNest` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstNest` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine

/-! ## The nested instantiation of a simple component -/

section Nest

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type}

/-- The store after the nested instantiation of a simple component in the instance allocated
next: as `instStore`, at an arbitrary instance id. -/
noncomputable def nestStore (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR)))
    (s : CStore (core3R Pf V IR)) (addr : Nat → Nat) (inst : InstId) (c : Simple) :
    CStore (core3R Pf V IR) :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr inst c.exports)

/-- The id of the next component instance. -/
noncomputable abbrev nextInst (s : CStore (core3R Pf V IR)) : InstId :=
  (ArenaField.insts (E := core3R Pf V IR)).mkId (ArenaField.insts.size s)

/-- The configuration after the nested instantiation. -/
noncomputable def nestCfg (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR)))
    (cfg : Machine.Config (core3R Pf V IR) σ) (addr : Nat → Nat) (c : Simple) :
    Machine.Config (core3R Pf V IR) σ :=
  { cfg with store := nestStore cs cfg.store addr (nextInst cfg.store) c }

/-- **The nested instantiation of an import-free simple component runs silently**: from a store
with the empty core store and no component function, the dispatcher's program for
`Call.instantiate ⟨c.toRef, outer⟩ []` allocates the next instance `inst`, instantiates the core
module and allocates one lifted function per export, answering the export map. -/
theorem instantiateCall_simple {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) (outer : List (Frame (core3R Pf V IR)))
    (cfg : Machine.Config (core3R Pf V IR) σ)
    (hcore : cfg.store.core = (core3R Pf V IR).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ es, funcExports es = exportMap c ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ [] : P (core3R Pf V IR) σ (Ret (core3R Pf V IR))) cfg
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

end Silmaril.Proofs.Wasm.Component.Param.Core3R
