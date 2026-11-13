module

public import Silmaril.Wasm.Resource.ReplayExamples.Defs

@[expose] public section

/-!
# Borrowing clients: modules

Real Core 3.0 modules with the imports `alloc : [] → [i32]` (0), `use : [i32] → []` (1),
`free : [i32] → []` (2) of `Silmaril.Wasm.Resource.Examples`, and the roles `ρRun` of
`Silmaril.Wasm.Resource.ReplayExamples` (export `0` lends its argument):

* `obBorrowUse`: `run : [i32] → []` is `local.get 0; call use; local.get 0; call use` (uses the
  borrowed handle twice).
* `obBorrowAlloc`: `run : [i32] → []` (one more local) uses the borrowed handle, allocates a fresh
  handle into local `1`, uses it, and uses the borrowed handle again.
* `obSession`: export `0` (`run`, lent) uses its argument; export `1` (`mk : [] → []`, no role)
  allocates into a local and uses it.
* `obFreeBorrow` (of `Silmaril.Wasm.Resource.ReplayExamples`) frees its borrowed argument: rejected
  by the checker and refuted (`obFreeBorrow_not_ob`).

Frees of owned handles (`checkOF`, free import `2`):

* `obOwnAUF`: `run : [i32] → []` (lent) uses its argument, allocates a handle into local `1`,
  uses it, uses the borrowed handle again, and frees the allocated handle;
* `obKeepFree`: `keep : [i32] → []` (ownership transferred, roles `ρKeep`) uses and frees its
  argument;
* `obOwnUAF`: `run` allocates into local `1`, frees it, then uses it: rejected and refuted.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.OBExamples

open Silmaril.Wasm.Resource.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Use the borrowed handle twice. -/
def obBorrowUse : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Use the borrowed handle, allocate and use a fresh one, use the borrowed one again. -/
def obBorrowAlloc : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [.i32], [.localGet ⟨0⟩, .call ⟨1⟩, .call ⟨0⟩, .localSet ⟨1⟩, .localGet ⟨1⟩,
    .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Two exports: `run` (lent) uses its argument, `mk` allocates into a local and uses it. -/
def obSession : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩]⟩,
    ⟨⟨2⟩, [.i32], [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩, ⟨"mk", .func ⟨4⟩⟩]

/-- Borrow, allocate, use both, free the allocated handle. -/
def obOwnAUF : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [.i32], [.localGet ⟨0⟩, .call ⟨1⟩, .call ⟨0⟩, .localSet ⟨1⟩, .localGet ⟨1⟩,
    .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨1⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Use and free a handle handed over by the environment. -/
def obKeepFree : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨2⟩]⟩]
  exports := [⟨"keep", .func ⟨3⟩⟩]

/-- Use after free of an allocated (owned) handle. -/
def obOwnUAF : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [.i32], [.call ⟨0⟩, .localSet ⟨1⟩, .localGet ⟨1⟩, .call ⟨2⟩, .localGet ⟨1⟩,
    .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

end Silmaril.Wasm.Resource.OBExamples
