module

public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# A counterexample to `Task.machine_core`: the program and the store

`Task.machine_core` (`Silmaril.Wasm.FX.Asyncify.Tool.Core`) asks for a simulation of the bounded frame
machine by Core 3.0 from **every** initial globals `gs`. With an unaligned `sp` the machine reads
its word memory at an unaligned address, where `MemAre` (aligned words only) says nothing. The
pieces of the counterexample:

* `cxFn`, `cxP`: one function, one parameter, no statements, tail `local.get 0` (`F = 2`,
  `SB = 4`); `cxFd`: its asyncified body (prologue: when `state = 2`, `sp := sp - 8` and
  `local 0 := mem sp`);
* `cxS`, `cxMI`: a Core store holding it, globals `state = 2`, `sp = 9`, and a memory of 12 zero
  bytes;
* `m7`: a word memory that agrees with those bytes at every aligned word but holds `7` at address
  `1`;
* `runTo cap E n c`: the result of the bounded machine from `c` within `n` steps, if it returns.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- The source function: `(param i32) (result i32) local.get 0`. -/
def cxFn : FnSrc := ⟨1, 0, 1, [], [.localGet (lidx 0)]⟩

/-- The source program: no imports, the function `cxFn`. -/
def cxP : Prog := ⟨[], [cxFn]⟩

/-- The asyncified function. -/
def cxFd : FnDef := ⟨1, cxP.frameWords - 1, 1, cxP.tBody cxFn⟩

/-- The Core type `[i32] → [i32]`. -/
def cxDT : DefType := V2.FuncType.toDefType ⟨[.i32], [.i32]⟩

/-- The module instance: function 0, globals 0 and 1, memory 0. -/
def cxMI : ModuleInst := { globals := [0, 1], mems := [0], funcs := [0] }

/-- The store: `state = 2`, `sp = 9` (not a multiple of 4), 12 zero bytes, the asyncified
function. -/
def cxS : Store Unit :=
  { globals := [⟨⟨.var, .i32⟩, .i32 2⟩, ⟨⟨.var, .i32⟩, .i32 9⟩]
    mems := [⟨⟨.i32, ⟨1, none⟩⟩, ⟨Array.replicate 12 0⟩⟩]
    funcs := [⟨cxDT, cxMI, .wasm ⟨⟨0⟩, List.replicate cxFd.nlocals .i32, cxFd.body⟩⟩] }

/-- A word memory that is zero at every aligned word and `7` at address 1. -/
def m7 : Nat → W := fun a => if a = 1 then 7 else 0

/-- The values the bounded machine returns from `c` within `n` steps, if it returns. -/
def runTo (cap : Nat) (E : Env) : Nat → Cfg → Option (List W)
  | 0, _ => none
  | n + 1, c =>
    match stepB cap E c with
    | .next c' => runTo cap E n c'
    | .done vs _ => some vs
    | _ => none

end Silmaril.Wasm.FX.Asyncify.Tool
