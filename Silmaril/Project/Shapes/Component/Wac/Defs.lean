module

public import Silmaril.Project.Defs
public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Wac.Targets.Defs
public import Silmaril.Wasm.Wit.Project.IR.Defs

/-!
# Standard problem shapes: WAC compositions

Two shapes about a composed component (the output of `wac compose`, a component in the
composition profile of `Silmaril.Wasm.Wac`, read under the format `wac.composition`):

| name | Lean | statement |
|---|---|---|
| `silmaril.shapes.component.wac_has_world` | `WacHasWorld (c : Ast) (W : WorldType)` | `c` is in the composition profile and fits `W` by names and sorts (`Wac.Targets.Fits` of its surface world) |
| `silmaril.shapes.component.wac_has_ir_world` | `WacHasIRWorld (c : Ast) (W : IRWorld)` | `c` is in the profile and lowers (`Wac.Lower.toCompCore`) to an IR component with the function world `W` |

`WacHasWorld` is the relation of WAC's `package p targets w;` and of `wac targets`, at the
level `Silmaril.Wasm.Wac.Targets` decides it: every import of the composition is an import of
`W` with the same sort, and every non-type export of `W` is an export of the composition with
the same sort. It does not compare the types behind the names (unlike `wac-types`'
`validate_target`); `WacHasIRWorld` does, at the function level of the component IR, for
compositions whose packages are embedded and in the `Binary.lower` subset.

The typed WIT projection (`silmaril.shapes.component.has_world`, `Wit.Project.projectX`) is
undefined on the usual `wac compose` output, which is why these shapes use the surface world
and the IR (`docs/projects/wasm-wasi.md`, "Targets").

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Wasm.Wit.Project (WorldType IRWorld compWorld)

/-- **The WAC composition `c` has the world `W`**: `c` is in the composition profile and fits
`W` by the names and sorts of its imports and exports (`wac targets`). -/
@[problem "silmaril.shapes.component.wac_has_world"
  (title := "A WAC composition has a given world (names and sorts)")]
def WacHasWorld (c : Ast) (W : WorldType) : Prop :=
  Silmaril.Wasm.Wac.Profile c ∧ Silmaril.Wasm.Wac.Targets.Fits (Silmaril.Wasm.Wac.Targets.surface c) W

/-- **The WAC composition `c` has the function world `W`**: `c` is in the composition profile
and its lowering to the component IR imports and exports the functions of `W`. -/
@[problem "silmaril.shapes.component.wac_has_ir_world"
  (title := "A WAC composition lowers to a component with given functions")]
def WacHasIRWorld (c : Ast) (W : IRWorld) : Prop :=
  Silmaril.Wasm.Wac.Profile c ∧ ∃ m, Silmaril.Wasm.Wac.Lower.toCompCore c = .ok m ∧ compWorld m = W

/-- The decision procedure of `WacHasWorld`. -/
def wacHasWorld (c : Ast) (W : WorldType) : Bool :=
  Silmaril.Wasm.Wac.isProfile c && Silmaril.Wasm.Wac.Targets.fits (Silmaril.Wasm.Wac.Targets.surface c) W

/-- The decision procedure of `WacHasIRWorld`. -/
def wacHasIRWorld (c : Ast) (W : IRWorld) : Bool :=
  Silmaril.Wasm.Wac.isProfile c &&
    match Silmaril.Wasm.Wac.Lower.toCompCore c with
    | .ok m => compWorld m == W
    | .error _ => false

end Silmaril.Project.Shapes.Component

end
