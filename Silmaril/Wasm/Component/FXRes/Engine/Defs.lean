module

public import Silmaril.Wasm.Component.FXRes.Defs
public import Silmaril.Wasm.Component.FXEngineV.Defs

/-!
# One-shot continuations in the threads of the WasmFX component engine (definitions)

The WasmFX component engine with suspension `fxEV P` (`Silmaril.Wasm.Component.FXEngineV`) runs
FX threads by `StepFX'`, each with its own continuation store. `threadConts` reads that store
off a thread (Core threads have none); `ThreadRun P` are the runs of one thread (internal steps
and resumptions). Theorems (`Silmaril.Wasm.Component.FXRes.Engine.Thms`): every
internal step of the engine (`InternalV`) changes a thread's store by a `KStep`, and resumption
(`resumeV`) keeps it, so the one-shot results of `Silmaril.Wasm.Component.FXRes` hold for the threads
of `fxEV P`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXEngine

/-- The continuation store of a thread of `fxEV`. -/
def threadConts {H : Type} : ThreadV H → KStore
  | .core _ => []
  | .fx K _ _ => K
  | .parked K _ _ _ _ _ => K

/-- Runs of one thread of `fxEV P`: internal steps, and resumptions with a host result (after
which the store may have changed arbitrarily, as a host call may change it). -/
inductive ThreadRun {H : Type} (P : Silmaril.Wasm.Numerics.Profile) :
    Silmaril.Wasm.Execution.Core.Store (FXCode H) × ThreadV H →
      Silmaril.Wasm.Execution.Core.Store (FXCode H) × ThreadV H → Prop where
  | refl (x) : ThreadRun P x x
  | step {x y z} (h : InternalV P x y) (r : ThreadRun P y z) : ThreadRun P x z
  | resume {s s' t res z} (r : ThreadRun P (s', resumeV s t res) z) : ThreadRun P (s, t) z

end Silmaril.Wasm.Component.FXRes
