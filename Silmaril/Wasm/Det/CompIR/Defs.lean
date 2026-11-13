module

public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Wasm.Component.Semantics.Defs

/-!
# Determinism and statelessness of the component IR: definitions

The component IR (`Silmaril.Wasm.Component`, `Comp.den C c`) answers every call with an
`Option Payload`; `none` is a trap (out-of-range calls, failing adapters). `noneTraps X` is that
trap predicate on a signature with these answers (`sigU`, `sigN n`, `CoreIface.sig`).

* `CoreDet C`: every core module's strategy is deterministic modulo traps and trap-strict;
* `CoreStateless C`: every core module's strategy is stateless modulo traps and trap-strict.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.CompIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Det.Game

/-- The trap answer of the component IR: `none`. -/
def noneTraps (X : Type) : Traps ⟨X, fun _ => Option Payload⟩ := fun _ r => r = none

/-- Every core module is deterministic modulo traps and trap-strict. -/
def CoreDet {M : Type} [CoreModule M] (C : CoreSem M) : Prop :=
  ∀ m : M, DetMod (noneTraps _) (C.sem m) ∧ Strict (noneTraps _) (noneTraps _) (C.sem m)

/-- Every core module is stateless modulo traps and trap-strict. -/
def CoreStateless {M : Type} [CoreModule M] (C : CoreSem M) : Prop :=
  ∀ m : M, StatelessMod (noneTraps _) (C.sem m) ∧ Strict (noneTraps _) (noneTraps _) (C.sem m)

end Silmaril.Wasm.Det.CompIR
