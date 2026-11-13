module

public import Silmaril.Wasm.FX.Examples.Defs

/-!
# WasmFX examples for `resume_throw` and `switch`

Two small WasmFX programs of `StepFX'` (`Silmaril.Wasm.Models.FXV`) in the kit of
`Silmaril.Wasm.FX.Examples.Defs` (FX functions without parameters, one tag at address `0`). The
explainer pinned in `docs/projects/wasm-wasi.md` gives `resume_throw` as an instruction snippet only and
`switch` only as a design sketch, so these programs are written for this track; they use the
explainer's instructions and its `block … resume (tag $e $l) …` shape (`resumeFX`).

* **Cancelling a generator** (`cancelWY`, `resume_throw`): function `0` is the generator of the
  sum example (`genY`, yields `1`, `2`, `3`); function `1` (main) resumes it once and, at the
  first yield, cancels it with `resume_throw $e` instead of resuming it. The exception is raised
  at the generator's `suspend`; nothing catches it, so the program throws. Intended result: the
  exception at address `0` (the first exception of the store).
* **Switching between two coroutines** (`switchWY`, `switch`): function `0` (`B`) suspends
  at once, then drops the continuation it is switched to with and returns `42`; function `1`
  (`A`) suspends at once and, when resumed with `B`'s continuation, switches to it; function `2`
  (main) starts `B` and `A` up to their first suspension and resumes `A` with `B`'s
  continuation under the handler `(on $e switch)`. Intended result: `B`'s `42`, returned through
  `A`'s handler.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX

/-! ## Cancelling a generator with `resume_throw` -/

/-- The bodies: the generator and the main function that cancels it at its first yield. -/
def cancelWY : Nat → List InstrFX
  | 0 => genY
  | 1 => [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)),
      resumeFX [.fx (.resumeThrow (ix 0) (ix 0) [])]]
  | _ => []

/-- The WasmFX program: call function `1` (main). -/
def cancelProg (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) : ConfigFX Nat :=
  fxInit (kitS P host 2 cancelWY) 1 []

/-! ## Switching between two coroutines -/

/-- `[] → [cont]`: start a coroutine up to its first suspension. -/
def btS : BlockType := .typeIdx (ix 2)

/-- `[cont cont] → [i32]`: resume a coroutine with another one as argument. -/
def btR : BlockType := .typeIdx (ix 3)

/-- The module types of the switch example: the kit's, then `btS` and `btR` (the continuation
slots are typed `i32`; the untyped `StepFX'` reads only arities). -/
def swTypes : List Silmaril.Wasm.Validation.DefType :=
  kitTypes ++ [Silmaril.Wasm.V2.FuncType.toDefType ⟨[], [.num (.int .i32)]⟩,
    Silmaril.Wasm.V2.FuncType.toDefType ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩]

/-- The module instance: three functions and one tag. -/
def swM : ModuleInst := { types := swTypes, tags := [0], funcs := List.range 3 }

/-- Start the coroutine `f`: `block btS (ref.func f; cont.new; resume (on $e 0)) end`. -/
def startFX (f : Nat) : InstrFX :=
  .block btS [.core (.refFunc (ix f)), .fx (.contNew (ix 0)),
    .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]

/-- The bodies of `B`, `A` and main. -/
def switchWY : Nat → List InstrFX
  | 0 => [.fx (.suspend (ix 0)), .core .drop, .core (.intConst .i32 42), .core .nop]
  | 1 => [.fx (.suspend (ix 0)), .fx (.switch (ix 0) (ix 0))]
  | 2 => [startFX 0, startFX 1, .block btR [.fx (.resume (ix 0) [.onSwitch (ix 0)])]]
  | _ => []

/-- The FX functions of the switch example. -/
def swFx : Nat → Option FuncFX
  | f => if f < 3 then some ⟨swM, 0, 1, [], switchWY f⟩ else none

/-- The store: three FX functions and one tag. -/
def swStore : Store Nat :=
  { funcs := (List.range 3).map fun f => ⟨kitTypes.head!, swM, .host f⟩,
    tags := [⟨kitTypes.head!⟩] }

/-- The WasmFX program: call function `2` (main). -/
def switchProg : ConfigFX Nat :=
  ⟨swStore, [], ⟨[], swM⟩, [.core (.plain (.call (ix 2)))]⟩

end Silmaril.Wasm.FX.Examples
