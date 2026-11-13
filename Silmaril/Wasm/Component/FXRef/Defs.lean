module

public import Silmaril.Wasm.Component.FXEngine.Defs

/-!
# The reference-machine half over the WasmFX engine: definitions

The soundness theorems of the component IR over an engine (`Simple.soundE`, `docs/projects/spectec/README.md`
§3) take the reference-machine half `RefToSpec E ofCore P` as a hypothesis. For the WasmFX
engine `fxE P` it is open; this module states it.

* `ofCoreFX m`: a Core 3.0 module as an FX module with no FX functions (`ofNum m = ofCoreFX m.mod`);
* **`RefToSpecFXAll`** (open, frozen): at every profile, every behaviour of the reference
  component machine running `c.toRef` over `fxE P` is an outcome of the Core 3.0 canonical-ABI
  specification at `P`, for the components of `Reference.refToSpec_of_arity`'s fragment.

* **`RefToSpecEFXAll`** (open, frozen): its machine half, against the FX engine's own
  specification `exportSpecE (fxE P) ofNum`. The engine-run half is proved
  (`FXRef.specSub_fx`), so `RefToSpecEFXAll → RefToSpecFXAll` (`FXRef.refToSpec_fx_of`).

Why it is open: `refToSpec_core3P` is a symbolic execution of the reference machine through
`core3P P` (`refToSpec_of_arity`), and its copy for restrictions (`core3R P V I`, about 10k
lines) relies on the engine having Core 3.0's stores and threads. `fxE P` has stores over host
codes `FXCode H` and threads `ThreadFX H`, so neither applies; what is proved about `fxE P` on
Core modules is the instance-level simulation behind `fxG_sem_eq_core3G` and the equality of
the two canonical-ABI specifications (`exportSpecE_ofNum`), not a transport of the whole
component machine. Transporting it means a simulation of the reference machine
(`Silmaril.Raw.Wasm.Component`, about 15k lines, whose stores have host codes `CanonHost E` and
whose canonical options mention `E`'s addresses) along `FXCode.host`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Numerics (Profile)

/-- A Core 3.0 module as an FX module with no FX functions. -/
def ofCoreFX (m : Silmaril.Wasm.Module) : ModuleFX := ⟨m, []⟩

/-- **The reference-machine half over the WasmFX engine** (proved: `FXRefE.refToSpec_fx`). -/
def RefToSpecFXAll : Prop := ∀ P : Profile, RefToSpec (fxE P) ofCoreFX P

/-- **The machine half over the WasmFX engine** (proved: `FXRefE.refToSpecE_fx`): every behaviour of the reference machine
running `c.toRef` over `fxE P` is an outcome of the FX engine's own specification. -/
def RefToSpecEFXAll : Prop := ∀ P : Profile, RefToSpecE (fxE P) ofCoreFX ofNum

end Silmaril.Wasm.Component.FXRef
