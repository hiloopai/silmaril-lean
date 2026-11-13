module

public import Silmaril.Wasm.Component.FXRes.ContComp.Defs
public import Silmaril.Wasm.Component.Reference.Defs

/-!
# Validating the `cont` component: definitions

The reference component validator `Validation.check? feat P validCore` is generic in the core
module type `M` and takes the core module types from `validCore : M → Option CoreModuleType`.
For Core 3.0 modules that is `core3ModuleType?` (the module validator `validate?`). The modules
of `fxCE P` are `ModuleFX`: a Core module and FX function declarations, which are exported by
name but checked by no validator (`StepFX'` is untyped), and the engine's own `exportTypes` are
those of the Core part, without the FX functions.

So the module type of `contModule` is given here by a **Core shadow**: the Core part
`contCore` with one Core stub per FX function, of the FX function's declared type, at the FX
function's index (`make` at `4`, `run` at `5`, after the imports and `g`), exported under the FX
function's name. `contShadow` is valid Core 3.0 (`validate?`), and its exports are those of
`contModule`'s instance (`make`, `run`); the stubs' bodies are placeholders that the validator
type-checks against the stated types, so the declared types of the FX functions are checked to
be well formed and to match how the component uses them, but **the FX bodies themselves are
not type-checked**.

* `contShadow`: the shadow module; `contModuleTypeC?`: `core3ModuleType?` of the shadow, the
  module type of the component's single core module `contModule`;
* `contCheck?`: the validator at the Component Model 2 feature gates; `contShadowBad`,
  `contCheckBad?`: the same with `make` stubbed at the wrong type, for a negative check.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContValid

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.FXRes.ContComp
open Silmaril.Wasm.Models.FXAsyncFX (ix)

/-- **The Core shadow of `contModule`**: `contCore` with stubs of `make : [] → [i32]` (type `2`)
and `run : [i32] → [i32]` (type `0`) at indices `4` and `5`, exported by name. -/
def contShadow : Silmaril.Wasm.Module :=
  { contCore with
    funcs := contCore.funcs ++ [⟨⟨2⟩, [], [.intConst .i32 0]⟩, ⟨⟨0⟩, [], [.localGet (ix 0)]⟩]
    exports := [⟨"make", .func (ix 4)⟩, ⟨"run", .func (ix 5)⟩] }

/-- The core module type of the (single) core module of `contComp`: that of the shadow of
`contModule`. -/
def contModuleTypeC? (_ : ModuleFX) : Option (Types.CoreModuleType Core3Extern) :=
  core3ModuleType? contShadow

/-- **The validator of `contComp`** at the Component Model 2 feature gates. -/
def contCheck? : Except ValidationError (Types.ComponentType Nat Core3Extern) :=
  check? Features.p2 core3Profile contModuleTypeC? contComp

/-- A mistyped shadow, for a negative check: `make` stubbed at `run`'s type `[i32] → [i32]`. -/
def contShadowBad : Silmaril.Wasm.Module :=
  { contShadow with
    funcs := contCore.funcs ++ [⟨⟨0⟩, [], [.localGet (ix 0)]⟩, ⟨⟨0⟩, [], [.localGet (ix 0)]⟩] }

/-- The validator with the mistyped shadow. -/
def contCheckBad? : Except ValidationError (Types.ComponentType Nat Core3Extern) :=
  check? Features.p2 core3Profile (fun _ : ModuleFX => core3ModuleType? contShadowBad) contComp

end Silmaril.Wasm.Component.FXRes.ContValid
