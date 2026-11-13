module

public import Silmaril.Wasm.Resource.Examples.Defs

@[expose] public section

/-!
# Clients of the handle protocol checked by the typestate verifier: modules

Real Core 3.0 modules with the imports `alloc : [] → [i32]` (0), `use : [i32] → []` (1),
`free : [i32] → []` (2) of `Silmaril.Wasm.Resource.Examples`, and two mutable `i32` globals, both
`0` initially: the flag `gf` (global 0) and the handle `gh` (global 1). No global is imported, so
their store addresses are `0` and `1`: the pair `(0, 1)` of `checkClient`.

* `cliAUF`: `run` clears the flag, allocates into `gh`, uses and frees `gh`.
* `cliSession`: export `a` allocates into `gh` and sets the flag; `b` uses `gh` under
  `global.get gf; if`; `c` clears the flag (under the same test) and frees `gh`. Any interleaving
  of export calls is safe: `b` and `c` only touch `gh` while the flag is set.
* `cliUAF` (use after free) and `cliDoubleFree`: rejected by the checker.

Handles in locals (frame-local facts):

* `cliLocal`: `run` (one `i32` local) is `call alloc; local.set 0; local.get 0; call use;
  local.get 0; call free`.
* `cliLocalHelper`: `run` calls `helper` twice, and `helper` (its own `i32` local) is the body of
  `cliLocal`: the facts live in the callee frame and die with it.
* `cliLocalTwo`: two handles in locals `0` and `1`, both used, then the second freed.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.ClientExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Resource.Examples (tyAlloc tyUse tyVoid handleImports)

/-- The flag (global 0) and the handle (global 1): mutable `i32`, initially `0`. -/
def flagGlobals : List Global :=
  [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩, ⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]

/-- Clear the flag, allocate into `gh`. -/
def allocInto : List Instr :=
  [.intConst .i32 0, .globalSet ⟨0⟩, .call ⟨0⟩, .globalSet ⟨1⟩]

/-- `run`: allocate, use, free. -/
def cliAUF : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  globals := flagGlobals
  funcs := [⟨⟨2⟩, [], allocInto ++ [.globalGet ⟨1⟩, .call ⟨1⟩, .globalGet ⟨1⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- A session over three export calls. -/
def cliSession : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  globals := flagGlobals
  funcs := [⟨⟨2⟩, [], allocInto ++ [.intConst .i32 1, .globalSet ⟨0⟩]⟩,
    ⟨⟨2⟩, [], [.globalGet ⟨0⟩, .if_ .empty [.globalGet ⟨1⟩, .call ⟨1⟩] []]⟩,
    ⟨⟨2⟩, [], [.globalGet ⟨0⟩, .if_ .empty
      [.intConst .i32 0, .globalSet ⟨0⟩, .globalGet ⟨1⟩, .call ⟨2⟩] []]⟩]
  exports := [⟨"a", .func ⟨3⟩⟩, ⟨"b", .func ⟨4⟩⟩, ⟨"c", .func ⟨5⟩⟩]

/-- Use after free. -/
def cliUAF : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  globals := flagGlobals
  funcs := [⟨⟨2⟩, [], allocInto ++ [.globalGet ⟨1⟩, .call ⟨2⟩, .globalGet ⟨1⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Double free. -/
def cliDoubleFree : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  globals := flagGlobals
  funcs := [⟨⟨2⟩, [], allocInto ++ [.globalGet ⟨1⟩, .call ⟨2⟩, .globalGet ⟨1⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Allocate into local `0`, use it, free it. -/
def locAUF : List Instr :=
  [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨2⟩]

/-- `run`: allocate into a local, use, free. -/
def cliLocal : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [.i32], locAUF⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- `run` calls `helper` twice; `helper` allocates into its local, uses, frees. -/
def cliLocalHelper : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [], [.call ⟨4⟩, .call ⟨4⟩]⟩, ⟨⟨2⟩, [.i32], locAUF⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Two handles in two locals: both used, the second freed. -/
def cliLocalTwo : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [.i32, .i32], [.call ⟨0⟩, .localSet ⟨0⟩, .call ⟨0⟩, .localSet ⟨1⟩,
    .localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨1⟩, .call ⟨1⟩, .localGet ⟨1⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- A helper `$use_then_free : [i32] → []` (function `4`): uses and frees its argument. -/
def helperUF : Func := ⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨2⟩]⟩

/-- **A handle passed to an internal callee**: `run` allocates into a local, uses it and hands it
to the helper, which uses and frees it. -/
def cliArg : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [.i32], [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨0⟩,
    .call ⟨4⟩]⟩, helperUF]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- A freed handle passed to the helper (a use after free inside the callee). -/
def cliArgUAF : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [.i32], [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨2⟩, .localGet ⟨0⟩,
    .call ⟨4⟩]⟩, helperUF]
  exports := [⟨"run", .func ⟨3⟩⟩]

end Silmaril.Wasm.Resource.ClientExamples
