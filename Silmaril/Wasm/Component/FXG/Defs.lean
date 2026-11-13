module

public import Silmaril.Wasm.Component.Hered.Defs
public import Silmaril.Wasm.Models.FX.Defs

/-!
# A WasmFX component engine over Core threads: definitions

The reference component machine is parametric in a `CoreEngine`. A WasmFX engine with FX
threads (FX code, handler frames and a continuation store) is not built here: it would need a
store-free FX thread type with its status, resumption and the `Lawful` laws, and FX code cannot
enter a component anyway, because WasmFX has no module syntax or instantiation yet
(`Silmaril.Wasm.Models.FX`: FX functions are host functions with `fx h = some F`).

What the parametrization does allow now is an engine whose internal step **is the WasmFX
step**: `fxE P` is Core 3.0 (`core3P P`) with its internal step replaced by `InternalFX P`, a
step of `StepFX P` (with no FX functions, `noFX`, and the host that refuses every call) between
the FX images (`FX.ofCore`) of the threads' Core configurations. `FXG.Thms` proves, from the
conservativity theorem `FX.stepFX_conservative`, that this engine is Core 3.0
(`internalFX_iff`, `fxE_eq`), so it is a lawful game engine `fxG P` with the game semantics of
`core3G P` and the four hereditary soundness properties.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXG

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **The WasmFX internal step on Core threads**: a `StepFX` step, without FX functions and with
the host that refuses every call, from the FX image of the thread's Core configuration to the FX
image of an active thread. -/
def InternalFX (P : Profile) {H : Type}
    (x y : Store H × Silmaril.Wasm.SingleThreaded.Thread) : Prop :=
  ∃ f' code', y.2 = .active f' code' ∧
    Silmaril.Wasm.Models.FX.StepFX P (fun _ _ _ _ => False) Silmaril.Wasm.Models.FX.noFX
      (Silmaril.Wasm.Models.FX.ofCore (x.2.config x.1))
      (Silmaril.Wasm.Models.FX.ofCore ⟨y.1, f', code'⟩)

/-- **The WasmFX engine over Core threads**: Core 3.0 at profile `P` with the WasmFX internal
step. -/
noncomputable abbrev fxE (P : Profile) : Engine :=
  Hered.withRel (core3P P) (core3P P).Valid (InternalFX P)

end Silmaril.Wasm.Component.FXG
