module

public import Silmaril.Wasm.FX.Examples.EveryRun.Thms
public import Silmaril.Wasm.FX.Logic.Typed.Thms

/-!
# The every-run WasmFX examples under typed `resume`

The proofs of `Silmaril.Wasm.FX.Examples.EveryRun` are in the untyped logic (`StepFX'`); through
`TSafe.behavioursR_sub` (`Silmaril.Wasm.FX.Logic.Typed`) they bound the behaviours under typed
`cont.bind` and `resume` (`StepFXR`, `Silmaril.Wasm.Models.FXResumeT`): at every profile without
host calls, every typed behaviour of each program is its intended result. These are inclusions;
the typed runs (for equality) are not constructed.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Typed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXResumeT (behavioursFXR)
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.FX.Logic.Typed (TSafe.behavioursR_sub)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- Sum of a generator under typed `resume`: every behaviour returns `6`. -/
theorem gen_behR_sub (P : Profile) :
    behavioursFXR P noHost (kitFx 6 genWY) (genProg P noHost) ⊆ {.returns [Val.i32 6]} :=
  TSafe.behavioursR_sub (r₀ := .values [Val.i32 6])
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.gen_tsafe (fun _ _ _ _ h => h)

/-- Take two from a generator under typed `resume`: every behaviour returns `3`. -/
theorem take_behR_sub (P : Profile) :
    behavioursFXR P noHost (kitFx 4 takeWY) (takeProg P noHost) ⊆ {.returns [Val.i32 3]} :=
  TSafe.behavioursR_sub (r₀ := .values [Val.i32 3])
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.take_tsafe (fun _ _ _ _ h => h)

/-- Cancelling a generator under typed `resume`: every behaviour throws the exception `0`. -/
theorem cancel_behR_sub (P : Profile) :
    behavioursFXR P noHost (kitFx 2 cancelWY) (cancelProg P noHost) ⊆ {.throws 0} :=
  TSafe.behavioursR_sub (r₀ := .throw 0)
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.cancel_tsafe (fun _ _ _ _ h => h)

/-- Switching between two coroutines under typed `resume`: every behaviour returns `42`. -/
theorem switch_behR_sub (P : Profile) :
    behavioursFXR P noHost swFx switchProg ⊆ {.returns [Val.i32 42]} :=
  TSafe.behavioursR_sub (r₀ := .values [Val.i32 42])
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.switch_tsafe (fun _ _ _ _ h => h)

end Silmaril.Wasm.FX.Examples.Typed
