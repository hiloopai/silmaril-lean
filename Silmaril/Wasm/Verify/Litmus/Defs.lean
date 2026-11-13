module

public import Silmaril.Wasm.Verify.Check.Defs

@[expose] public section

/-!
# Litmus modules for the verifier

Real Core 3.0 modules (silmaril-lean `Module`s, written as abstract syntax) importing an
`assert : [i32] → []` function as import `0`:

* `modDead`: exports `inc` (`local.get 0; i32.const 1; i32.add`); a second, **unexported and
  unreferenced** function calls `assert(0)`. The import is unreachable: `neverCall 0` is proved.
  ```wat
  (module
    (import "env" "assert" (func (param i32)))                    ;; function 0
    (func (export "inc") (param i32) (result i32)
      local.get 0  i32.const 1  i32.add)                         ;; function 1
    (func  i32.const 0  call 0))                                  ;; function 2 (dead)
  ```
* `modOne`: exports `run`, which calls `assert(1)`.
* `modIndirect`: exports `run`, which does `call_indirect` through a table whose active element
  segment holds function 2, which calls `assert(0)`.
* `modStart`: a start function calls `assert(1)`; `modStartOk`: a start function sets a global,
  and only a dead function calls `assert(0)`.
* `modZero`: the export calls `assert(0)`; `modParam`: the export calls `assert` with its
  parameter; `modNested`: the export calls `assert(1)` inside a `block` and `assert(7)` inside
  an `if`, between other instructions; `modBranch`: `if x then assert(0)`.
* Locals: `modGuardParam` (`if x then assert(x)`), `modSetLocal` (`x := 1; assert(x)`),
  `modLoopLocal` (the same through a loop, a block and an `if`), `modSetZero`
  (`x := 0; assert(x)`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify.Litmus

open Silmaril.Wasm Silmaril.Wasm.Validation

/-- `[i32] → []`. -/
def tyAssert : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[i32] → [i32]`. -/
def tyInc : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[] → []`. -/
def tyVoid : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩

/-- The `assert` import. -/
def assertImport : Import := ⟨"env", "assert", .func ⟨0⟩⟩

/-- A dead function calling `assert(0)`. -/
def deadAssert : Func := ⟨⟨2⟩, [], [.intConst .i32 0, .call ⟨0⟩]⟩

/-- Never calls `assert`: the only function calling it is dead. -/
def modDead : Module where
  types := [tyAssert, tyInc, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add]⟩, deadAssert]
  exports := [⟨"inc", .func ⟨1⟩⟩]

/-- Calls `assert(1)` from its export. -/
def modOne : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 1, .call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- Calls through a table that holds a function calling `assert(0)`. -/
def modIndirect : Module where
  types := [tyAssert, tyInc, tyVoid]
  imports := [assertImport]
  tables := [⟨⟨.i32, ⟨1, some 1⟩, ⟨true, .abstract .func⟩⟩, [.refNull (.abstract .func)]⟩]
  funcs := [⟨⟨2⟩, [], [.intConst .i32 0, .callIndirect ⟨0⟩ ⟨2⟩]⟩, deadAssert]
  elems := [⟨⟨true, .abstract .func⟩, [[.refFunc ⟨2⟩]], .active ⟨0⟩ [.intConst .i32 0]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- Calls `assert(0)` from its export. -/
def modZero : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 0, .call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- Calls `assert` with its own (unknown) argument. -/
def modParam : Module where
  types := [tyAssert]
  imports := [assertImport]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩]⟩]
  exports := [⟨"check", .func ⟨1⟩⟩]

/-- Calls `assert(1)` twice, once inside a block and once inside an `if`, with other work in
between. -/
def modNested : Module where
  types := [tyAssert, tyInc]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [], [
    .block .empty [.intConst .i32 1, .call ⟨0⟩],
    .localGet ⟨0⟩,
    .if_ .empty [.intConst .i32 7, .call ⟨0⟩] [.nop],
    .localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add]⟩]
  exports := [⟨"inc", .func ⟨1⟩⟩]

/-- A start function calls `assert(1)`. -/
def modStart : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 1, .call ⟨0⟩]⟩]
  start := some ⟨1⟩

/-- The export `run(x)` calls `assert(0)` only when `x ≠ 0`: refuted with the argument `1`. -/
def modBranch : Module where
  types := [tyAssert]
  imports := [assertImport]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .if_ .empty [.intConst .i32 0, .call ⟨0⟩] [.nop]]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- A start function sets a global; the export reads it; an unexported, unreferenced function
calls `assert(0)`. The import is unreachable even with the instantiation phase. -/
def modStartOk : Module where
  types := [tyAssert, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩, tyVoid]
  imports := [assertImport]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨2⟩, [], [.intConst .i32 1, .globalSet ⟨0⟩]⟩, ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩, deadAssert]
  exports := [⟨"get", .func ⟨2⟩⟩]
  start := some ⟨1⟩

/-- The export `check(x)` tests its parameter before asserting it:
`local.get 0; if (then local.get 0; call $assert)`. Proved by the flow analysis. -/
def modGuardParam : Module where
  types := [tyAssert]
  imports := [assertImport]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .if_ .empty [.localGet ⟨0⟩, .call ⟨0⟩] [.nop]]⟩]
  exports := [⟨"check", .func ⟨1⟩⟩]

/-- The export sets a local to `1`, then asserts it: `i32.const 1; local.set 0; local.get 0;
call $assert`. Proved by the flow analysis. -/
def modSetLocal : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [.i32], [.intConst .i32 1, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The export sets a local to `1`, then asserts it in a loop, inside a block, after testing
its parameter: facts survive branches and loops. Proved by the flow analysis. -/
def modLoopLocal : Module where
  types := [tyAssert]
  imports := [assertImport]
  funcs := [⟨⟨0⟩, [.i32], [
    .intConst .i32 7, .localSet ⟨1⟩,
    .loop .empty [
      .block .empty [.localGet ⟨1⟩, .call ⟨0⟩],
      .localGet ⟨0⟩, .if_ .empty [.localGet ⟨0⟩, .call ⟨0⟩] [.nop],
      .localGet ⟨0⟩, .brIf ⟨0⟩]]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The export sets a local to `0`, then asserts it: refuted. -/
def modSetZero : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [.i32], [.intConst .i32 0, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- Two exports: `a` calls `assert(1)`, `b` calls a helper that never asserts (`a` calls the
helper too). Per export: `neverCallFrom (0, b)` is proved, `neverCallFrom (0, a)` refuted.
  ```wat
  (module
    (import "env" "assert" (func (param i32)))                    ;; function 0
    (func (export "a")  call 3  i32.const 1  call 0)              ;; function 1
    (func (export "b")  call 3)                                   ;; function 2
    (func  i32.const 5  drop))                                    ;; function 3
  ```
-/
def modTwo : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  funcs := [⟨⟨1⟩, [], [.call ⟨3⟩, .intConst .i32 1, .call ⟨0⟩]⟩, ⟨⟨1⟩, [], [.call ⟨3⟩]⟩,
    ⟨⟨1⟩, [], [.intConst .i32 5, .drop]⟩]
  exports := [⟨"a", .func ⟨1⟩⟩, ⟨"b", .func ⟨2⟩⟩]

/-- Three exports: `a` returns; function 3 (unexported) calls `assert(1)` and **escapes**
through the table; `b` calls it with `call_indirect`, `c` only takes its reference
(`ref.func 3; drop`). For every export the import is callable through the escaping reference:
`b` is refuted; `a` and `c` are unknown (`reaches [3, 0]`: the callable set of every export
contains every escaping function, whether or not the export makes an indirect call).
  ```wat
  (module
    (import "env" "assert" (func (param i32)))                    ;; function 0
    (table 1 1 funcref)
    (elem (i32.const 0) func 3)
    (func (export "a"))                                           ;; function 1
    (func (export "b")  i32.const 0  call_indirect (type $void))  ;; function 2
    (func  i32.const 1  call 0)                                   ;; function 3
    (func (export "c")  ref.func 3  drop))                        ;; function 4
  ```
-/
def modEscape : Module where
  types := [tyAssert, tyVoid]
  imports := [assertImport]
  tables := [⟨⟨.i32, ⟨1, some 1⟩, ⟨true, .abstract .func⟩⟩, [.refNull (.abstract .func)]⟩]
  funcs := [⟨⟨1⟩, [], []⟩, ⟨⟨1⟩, [], [.intConst .i32 0, .callIndirect ⟨0⟩ ⟨1⟩]⟩,
    ⟨⟨1⟩, [], [.intConst .i32 1, .call ⟨0⟩]⟩, ⟨⟨1⟩, [], [.refFunc ⟨3⟩, .drop]⟩]
  elems := [⟨⟨true, .abstract .func⟩, [[.refFunc ⟨3⟩]], .active ⟨0⟩ [.intConst .i32 0]⟩]
  exports := [⟨"a", .func ⟨1⟩⟩, ⟨"b", .func ⟨2⟩⟩, ⟨"c", .func ⟨4⟩⟩]

end Silmaril.Wasm.Verify.Litmus
