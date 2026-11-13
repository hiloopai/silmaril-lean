module

public import Silmaril.Wasm.Det.Component.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Defs

/-!
# Litmus components for determinism and statelessness across calls

Three canonical-ABI sessions over Core 3.0 instances (`Silmaril.Wasm.Det.Component`, `abiSem`):

* **the adder** `adderX`: `add(a: u32, b: u32) -> u32`, flat, over the instance store
  `binStore .add` of `Silmaril.Wasm.Component.Reference.Litmus.binCore3 .add`
  (`local.get 0; local.get 1; i32.add`). The same component as the reference litmus `adderS`.
* **a stateful component** `litX` over the shared litmus module
  `Silmaril.Wasm.Det.Core.Litmus.litMod`: exports `one() -> u32` (function `0`, `i32.const 1`),
  `set()` (function `2`, `global.set` of `5`) and `get() -> u32` (function `3`, `global.get`).
  The core module keeps state in a global (a flag written by `set`, not a counter). `get` is not
  stateless; `one` is.
* **a `list<u8>` export over a scratch buffer** `bufX`: `len(bs: list<u8>) -> u32` over

  ```wat
  (module
    (memory 1)
    (func (export "realloc") (param i32 i32 i32 i32) (result i32) i32.const 1024) ;; 0
    (func (export "len") (param i32 i32) (result i32) local.get 1))             ;; 1
  ```

  The canonical ABI lowers the argument by calling `realloc`, which always returns the fixed
  scratch address `1024`, and writing the bytes there, so the linear memory changes on every
  call. The core function reads only its arguments.

`bufStore` is the allocation of `bufMod` by silmaril-lean's `prepare?` (one page of memory).
Theorems: `Silmaril.Wasm.Det.Component.Litmus.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Component.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The adder session: one flat export over core function `0`. -/
def adderX : Unit → AbiFn := fun _ => { fn := 0 }

/-- The exports of the stateful component. -/
inductive LitExp where
  | one
  | set
  | get
  deriving DecidableEq

/-- `one`, `set` and `get` as flat lifts of functions `0`, `2` and `3` of `litMod`. -/
def litX : LitExp → AbiFn
  | .one => { fn := 0 }
  | .set => { fn := 2 }
  | .get => { fn := 3 }

/-- The scratch-buffer module. -/
def bufMod : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32, .i32, .i32], [.i32]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 1024]⟩, ⟨⟨1⟩, [], [.localGet ⟨1⟩]⟩]
  exports := [⟨"realloc", .func ⟨0⟩⟩, ⟨"len", .func ⟨1⟩⟩]

/-- The spec's allocation of `bufMod` into the empty store. -/
def bufStore : Store Nat :=
  ((prepare? evalConst? ({} : Store Nat) bufMod []).getD (⟨{}, {}, []⟩, none)).1.store

/-- `len(bs: list<u8>) -> u32`: core function `1`, the argument lowered by `realloc` (function
`0`) into memory `0`. -/
def bufX : Unit → AbiFn := fun _ => { fn := 1, argBuf := some (0, 0) }

end Silmaril.Wasm.Det.Component.Litmus
