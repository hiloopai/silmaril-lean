module

public import Silmaril.Project.Shapes.WasmWastLink.Defs

/-!
# WAST rows: the `spectest` host's identity semantics, a hand-written linked script

Not generated from the spec test suite (`tools/wasm-wast/gen.py` imports these rows into the
group `silmaril.wasm_wast`). The script is `tools/wasm-wast/regress/right-spectest-shared.wast`,
written here as modules:

```wast
(module $W
  (import "spectest" "memory" (memory 1))
  (import "spectest" "print_i32" (func $print (param i32)))
  (import "spectest" "global_i32" (global $g1 i32))
  (import "spectest" "global_i32" (global $g2 i32))
  (func (export "store") (i32.store (i32.const 0) (i32.const 42)) (call $print (i32.const 42)))
  (func (export "g") (result i32) (i32.add (global.get $g1) (global.get $g2))))
(module $R
  (import "spectest" "memory" (memory 1))
  (func (export "load") (result i32) (i32.load (i32.const 0))))
(assert_return (invoke $R "load") (i32.const 0))
(assert_return (invoke $W "store"))
(assert_return (invoke $R "load") (i32.const 42))
(assert_return (invoke $W "g") (i32.const 1332))
```

`$W` and `$R` import `spectest`'s `memory` separately. In the reference interpreter it is one
memory (`interpreter/host/spectest.ml` l. 30–32, a top-level value), so the store through `$W` is
seen by the load through `$R`: the third assertion distinguishes a shared memory (42) from a
memory allocated per import (0). The two imports of `global_i32` are two fresh globals of value
666 in the reference interpreter (l. 10–20); immutable, so Wasm code sees only their values. The
call of `print_i32` prints `42 : i32`: the host-call log of the script is `[(1, [i32 42])]`.
-/

@[expose] public section

namespace Silmaril.Project.WasmWast.SpectestHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWastLink

/-- `i32`. -/
abbrev i32 : ValType := .num (.int .i32)

/-- The function type `ps → rs`, final, no supertypes. -/
def fnType (ps rs : List ValType) : RecType := ⟨[⟨true, [], .func ⟨ps, rs⟩⟩]⟩

/-- `$W`: imports `memory`, `print_i32` and `global_i32` twice; `store` writes 42 at address 0
and prints it; `g` adds the two globals. -/
def writer : Module where
  types := [fnType [i32] [], fnType [] [], fnType [] [i32]]
  imports := [⟨"spectest", "memory", .memory ⟨.i32, ⟨1, none⟩⟩⟩,
    ⟨"spectest", "print_i32", .func ⟨0⟩⟩,
    ⟨"spectest", "global_i32", .global ⟨.const, i32⟩⟩,
    ⟨"spectest", "global_i32", .global ⟨.const, i32⟩⟩]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 0, .intConst .i32 42, .intStore .i32 none ⟨0⟩ ⟨2, 0⟩,
      .intConst .i32 42, .call ⟨0⟩]⟩,
    ⟨⟨2⟩, [], [.globalGet ⟨0⟩, .globalGet ⟨1⟩, .intBinOp .i32 .add]⟩]
  exports := [⟨"store", .func ⟨1⟩⟩, ⟨"g", .func ⟨2⟩⟩]

/-- `$R`: imports `memory`; `load` reads address 0. -/
def reader : Module where
  types := [fnType [] [i32]]
  imports := [⟨"spectest", "memory", .memory ⟨.i32, ⟨1, none⟩⟩⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨2, 0⟩]⟩]
  exports := [⟨"load", .func ⟨0⟩⟩]

/-- The script, in order. -/
def cmds : List Cmd := [
  .module (some "W") writer,
  .module (some "R") reader,
  .action (.invoke (.named "R") "load" []) (some (.values [Val.i32 0])),
  .action (.invoke (.named "W") "store" []) (some (.values [])),
  .action (.invoke (.named "R") "load" []) (some (.values [Val.i32 42])),
  .action (.invoke (.named "W") "g" []) (some (.values [Val.i32 1332]))]

end Silmaril.Project.WasmWast.SpectestHost

end
