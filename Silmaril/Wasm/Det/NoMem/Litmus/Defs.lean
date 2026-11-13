module

public import Silmaril.Wasm.Det.NoMem.Module.Defs

/-!
# Litmus module for the memory-free, float-free subset

```wat
(module
  (type $f (func (param i32) (result i32)))                         ;; type 0
  (type $s (struct (field (mut i32))))                              ;; type 1
  (type $n (func (result f32)))                                     ;; type 2
  (import "env" "h" (func $h (type $f)))                            ;; function 0
  (func $box (export "box") (type $f)                               ;; function 1
    local.get 0  struct.new $s  struct.get $s 0  call $h  i32.const 1  i32.add)
  (func $nan (export "nan") (type $n)                               ;; function 2
    f32.const nan  f32.const nan  f32.add)
  (func $twice (export "twice") (type $f)                           ;; function 3
    local.get 0  call $box  call $box))
```

* `box` allocates a GC struct, reads its field, calls the import `h` and adds `1`; `twice` calls
  `box` twice. Both are in the subset (direct mode: their direct-call closure `{0, 1, 3}` holds
  the import and subset functions only).
* `nan` adds two NaNs: a float instruction, outside the subset; the module as a whole is not in
  the subset (`storeB` fails).

`gcMod` is validated by silmaril-lean's `validate?` and allocated by `prepare?` against a fresh
host function for the import (`Silmaril.Wasm.Det.NoMem.instPrep`); `gcStore` is the allocated store.

`startMod` (instance level, with a start function):

```wat
(module
  (global $g (mut i32) (i32.const 0))
  (func $init  i32.const 6  i32.const 7  i32.mul  global.set $g)        ;; function 0
  (func $get (export "get") (result i32)  global.get $g)                ;; function 1
  (start $init))
```

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NoMem.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The canonical positive `f32` NaN. -/
def nanBits : BitVec 32 := 0x7fc00000

/-- The litmus module. -/
def gcMod : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩,
    ⟨[⟨true, [], .struct [⟨.var, .val .i32⟩]⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.f32]⟩⟩]⟩]
  imports := [⟨"env", "h", .func ⟨0⟩⟩]
  funcs := [
    ⟨⟨0⟩, [], [.localGet ⟨0⟩, .structNew ⟨1⟩, .structGet none ⟨1⟩ ⟨0⟩, .call ⟨0⟩,
      .intConst .i32 1, .intBinOp .i32 .add]⟩,
    ⟨⟨2⟩, [], [.floatConst .f32 nanBits, .floatConst .f32 nanBits, .floatBinOp .f32 .add]⟩,
    ⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩, .call ⟨1⟩]⟩]
  exports := [⟨"box", .func ⟨1⟩⟩, ⟨"nan", .func ⟨2⟩⟩, ⟨"twice", .func ⟨3⟩⟩]

/-- Validation and allocation of `gcMod` against a fresh host function for its import. -/
def gcPrep : Option (Config Nat × Option FuncIdx) := instPrep gcMod

/-- The store of the instance of `gcMod`. -/
def gcStore : Store Nat := (gcPrep.map (·.1.store)).getD {}

/-- A module with a start function computing a global. -/
def startMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 6, .intConst .i32 7, .intBinOp .i32 .mul, .globalSet ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"get", .func ⟨1⟩⟩]
  start := some ⟨0⟩

end Silmaril.Wasm.Det.NoMem.Litmus
