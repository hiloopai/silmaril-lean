module

public import Silmaril.Wasm.Verify.Checker.Defs
public import Silmaril.Wasm.Spec.Run.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs

@[expose] public section

/-!
# An automated verifier for import-call properties of Core 3.0 modules

The checker `check m φ : Report` and the instances it computes (`instance?`,
`specInstance?`) are in `Silmaril.Wasm.Verify.Checker`, which imports no game semantics.
This header adds the semantics they are proved against: the instance predicates
`Silmaril.Wasm.Game.IsInstance` and `Silmaril.Wasm.Game.IsSpecInstance`, the specification
institutions (`Silmaril.Wasm.Spec`) and `progOf m`, the Wasm program of a module as a model
of them. Soundness: `Silmaril.Wasm.Verify.Check.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The Wasm program of a module: its instance, as a model of the specification institutions
(`Silmaril.Wasm.Spec.wasmSem`). -/
def progOf (m : Module) : Silmaril.Wasm.Spec.WasmProg (Silmaril.Wasm.Spec.ifaceOf (instOf m)) :=
  Silmaril.Wasm.Spec.WasmProg.ofInstance (instOf m)

end Silmaril.Wasm.Verify
