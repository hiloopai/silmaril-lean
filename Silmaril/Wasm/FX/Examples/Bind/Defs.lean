module

public import Silmaril.Wasm.FX.Examples.Defs

/-!
# A `cont.bind` program

The explainer pinned in `docs/projects/wasm-wasi.md` describes `cont.bind` (partial application of a
continuation) but gives no program using it; this program is written for this workflow. Two FX
functions of `StepFX'` (`Silmaril.Wasm.Models.FXV`):

* function `0` (`add40`, `[i32] → [i32]`): `local.get 0; i32.const 40; i32.add`;
* function `1` (main, `[] → [i32]`): `i32.const 2; ref.func 0; cont.new $ct;
  cont.bind $ct $ct'; resume $ct'`: make a continuation of `add40`, bind its argument `2`,
  and resume the bound continuation with no further arguments.

Intended result: `42`. `StepFX'` binds and resumes with **any** split of the values below the
continuation (`Silmaril.Wasm.Models.FXResume`); every split either reaches `add40` with the
argument `2` or gets stuck at the call, so the behaviour is still exactly `42`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAsyncFX (ix)

/-- `[] → [i32]`: the type of the bound continuation and of main. -/
def bdT : DefType := Silmaril.Wasm.V2.FuncType.toDefType ⟨[], [.num (.int .i32)]⟩

/-- The module types: the kit's (`[i32] → [i32]` first), then `bdT`. -/
def bdTypes : List DefType := kitTypes ++ [bdT]

/-- The module instance: two functions, one tag. -/
def bdM : ModuleInst := { types := bdTypes, tags := [0], funcs := List.range 2 }

/-- `add40`: `local.get 0; i32.const 40; i32.add`. -/
def add40Body : List InstrFX :=
  [.core (.localGet (ix 0)), .core (.intConst .i32 40), .core (.intBinOp .i32 .add)]

/-- Main: bind `2` to a continuation of `add40`, then resume it. -/
def bindMain : List InstrFX :=
  [.core (.intConst .i32 2), .core (.refFunc (ix 0)), .fx (.contNew (ix 0)),
    .fx (.contBind (ix 0) (ix 2)), .fx (.resume (ix 2) [])]

/-- The FX functions of the `cont.bind` program. -/
def bdFx : Nat → Option FuncFX
  | 0 => some ⟨bdM, 1, 1, [], add40Body⟩
  | 1 => some ⟨bdM, 0, 1, [], bindMain⟩
  | _ => none

/-- The store: the two FX functions. -/
def bdStore : Store Nat :=
  { funcs := [⟨kitTypes.head!, bdM, .host 0⟩, ⟨bdT, bdM, .host 1⟩], tags := [⟨kitTypes.head!⟩] }

/-- The `cont.bind` program: call function `1` (main). -/
def bindProg : ConfigFX Nat :=
  ⟨bdStore, [], ⟨[], bdM⟩, [.core (.plain (.call (ix 1)))]⟩

end Silmaril.Wasm.FX.Examples
