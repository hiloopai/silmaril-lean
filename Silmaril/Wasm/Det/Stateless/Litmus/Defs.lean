module

public import Silmaril.Wasm.Det.Stateless.Defs
public import Silmaril.Wasm.Verify.Check.Defs

/-!
# Litmus module for stateless code

```wat
(module
  (import "env" "h" (func $h (param i32) (result i32)))          ;; function 0 (host)
  (global $cnt (mut i32) (i32.const 0))                           ;; a counter
  (global $k i32 (i32.const 7))                                   ;; immutable
  (global $tmp (mut i32) (i32.const 0))                           ;; scratch
  (func $twice (export "twice") (param i32) (result i32)          ;; function 1
    local.get 0  local.get 0  i32.add)
  (func $pure (export "pure") (param i32) (result i32)            ;; function 2
    local.get 0  call $twice  call $h)
  (func $bump (export "bump")                                     ;; function 3
    global.get $cnt  i32.const 1  i32.add  global.set $cnt)
  (func $read (export "read") (result i32)                        ;; function 4
    global.get $cnt)
  (func $readk (export "readk") (param i32) (result i32)          ;; function 5
    local.get 0  global.get $k  i32.add)
  (func $scratch (export "scratch") (param i32) (result i32)      ;; function 6
    local.get 0  global.set $tmp  global.get $tmp  i32.const 1  i32.add))
```

* `twice` and `pure` read no global: stateless over every call state of the module (`pure`
  calls `twice` and the import `h`, so its outputs depend on the import's answers only);
* `readk` reads the immutable global `$k`, which no function of the module writes: stateless
  over the call states;
* `scratch` writes the scratch global `$tmp` and reads it back: the syntactic checks reject it
  (it reads a written global); it is stateless by a Hoare-logic VC;
* `bump`/`read` make the module stateful: `read` returns `0` initially and `1` after `bump`;
* every function is in the subset with global reads and writes, so the module is
  deterministic modulo traps and imports at every profile.

`slMod` is a silmaril-lean Core `Module`; `slInst` its scalar instance against a fresh host
function for the import (`Silmaril.Wasm.Verify.instOf`: validation, then silmaril-lean's
executable instantiation), `slStore` its store, `slEntry` its entry functions (`1`–`6`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Stateless.Litmus

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

/-- `[i32] → [i32]`. -/
def tyUn : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[] → []`. -/
def tyVoid : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩
/-- `[] → [i32]`. -/
def tyGet : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- The body of `scratch`. -/
def scratchBody : List Instr :=
  [.localGet ⟨0⟩, .globalSet ⟨2⟩, .globalGet ⟨2⟩, .intConst .i32 1, .intBinOp .i32 .add]

/-- The litmus module. -/
def slMod : Module where
  types := [tyUn, tyVoid, tyGet]
  imports := [⟨"env", "h", .func ⟨0⟩⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩, ⟨⟨.const, .i32⟩, [.intConst .i32 7]⟩,
    ⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨0⟩, .intBinOp .i32 .add]⟩,
    ⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩, .call ⟨0⟩]⟩,
    ⟨⟨1⟩, [], [.globalGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add, .globalSet ⟨0⟩]⟩,
    ⟨⟨2⟩, [], [.globalGet ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.localGet ⟨0⟩, .globalGet ⟨1⟩, .intBinOp .i32 .add]⟩,
    ⟨⟨0⟩, [], scratchBody⟩]
  exports := [⟨"twice", .func ⟨1⟩⟩, ⟨"pure", .func ⟨2⟩⟩, ⟨"bump", .func ⟨3⟩⟩,
    ⟨"read", .func ⟨4⟩⟩, ⟨"readk", .func ⟨5⟩⟩, ⟨"scratch", .func ⟨6⟩⟩]

/-- The scalar instance of `slMod`. -/
def slInst : Silmaril.Wasm.Game.ScalarInstance := Silmaril.Wasm.Verify.instOf slMod

/-- The store of the instance. -/
def slStore : Store Nat := slInst.store

/-- The entry functions: the six exports. -/
def slEntry (a : Nat) : Prop := 1 ≤ a ∧ a ≤ 6

end Silmaril.Wasm.Det.Stateless.Litmus
