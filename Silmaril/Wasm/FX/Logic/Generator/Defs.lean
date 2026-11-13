module

public import Silmaril.Wasm.FX.Logic.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# A one-shot generator in WasmFX: the program

The generator `gen` yields `1` (`suspend $yield`) and then returns `2`. The consumer creates a
continuation of `gen`, resumes it under a handler for `$yield`, receives the yielded value and
the continuation of the rest of the generator at the handler's label, resumes that continuation
(no handler: `gen` does not yield again) and adds the two values:

    (func $gen (result i32)
      (i32.const 1) (suspend $yield) (i32.const 2))
    ;; main:
    (block $on_yield (result i32 (ref $ct))
      (ref.func $gen) (cont.new $ct) (resume $ct (on $yield $on_yield))
      (unreachable))
    (resume $ct)          ;; resume the rest of the generator: returns 2
    (i32.add)             ;; 1 + 2

The block's result type is given by the type index `1`, `[] → [i32 i32]`: the FX reduction
reads only its arity (two operands; the continuation reference is the second).

* `genM`: the module instance (types, one tag, one function); `genStore`: the store with `gen`
  as an FX function (host code `0`) and the tag `$yield`; `genFx`: the FX function table;
* `genBody`, `mainBody`: the code; `genF0`: the frame of `main`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Generator

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX

/-- An index. -/
def ix {k : IndexKind} (j : Nat) : Idx k := ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- The types: `$ct`'s function type `[] → [i32]` and the block type `[] → [i32 i32]`. -/
def genTypes : List Silmaril.Wasm.Validation.DefType :=
  [Silmaril.Wasm.V2.FuncType.toDefType ⟨[], [.num (.int .i32)]⟩,
    Silmaril.Wasm.V2.FuncType.toDefType ⟨[], [.num (.int .i32), .num (.int .i32)]⟩]

/-- The module instance. -/
def genM : ModuleInst := { types := genTypes, tags := [0], funcs := [0] }

/-- The generator's body: yield `1`, return `2`. -/
def genBody : List InstrFX :=
  [.core (.intConst .i32 1), .fx (.suspend (ix 0)), .core (.intConst .i32 2)]

/-- The FX function table: host code `0` is `gen`. -/
def genFx : Nat → Option FuncFX
  | 0 => some ⟨genM, 0, 1, [], genBody⟩
  | _ => none

/-- The store: `gen` and the tag `$yield`. -/
def genStore : Store Nat :=
  { funcs := [⟨genTypes.head!, genM, .host 0⟩], tags := [⟨genTypes.head!⟩] }

/-- The frame of `main`. -/
def genF0 : Frame := ⟨[], genM⟩

/-- The consumer. -/
def mainBody : List InstrFX :=
  [.block (.typeIdx (ix 1))
      [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)),
        .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)]), .core .unreachable],
    .fx (.resume (ix 0) []), .core (.intBinOp .i32 .add)]

end Silmaril.Wasm.FX.Logic.Generator
