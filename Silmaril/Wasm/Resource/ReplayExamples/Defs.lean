module

public import Silmaril.Wasm.Resource.Replay.Defs
public import Silmaril.Wasm.Resource.Examples.Defs

@[expose] public section

/-!
# Replaying environment answers: examples

Real Core 3.0 modules with the imports `alloc : [] → [i32]`, `use : [i32] → []`,
`free : [i32] → []` of `Silmaril.Wasm.Resource.Examples` (one local `i32` where needed):

* `cliUaf` (export `run : [] → []`): `call alloc; local.set 0; local.get 0; call free;
  local.get 0; call use` (use after free);
* `cliDoubleFree` (export `run : [] → []`): `call alloc; local.set 0; local.get 0; call free;
  local.get 0; call free` (double free);
* `obFreeBorrow` (export `run : [i32] → []`, its argument borrowed): `local.get 0; call free`
  (a borrowed handle dropped);
* `obFreeTwice` (export `keep : [i32] → []`, its argument owned): `local.get 0; call free;
  local.get 0; call free` (an owned handle dropped twice).

`ρRun`, `ρKeep`: the ownership roles by number (import `0` allocates, `1` uses, `2` frees; export
`0` lends, resp. transfers ownership of, its argument).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.ReplayExamples

open Silmaril.Wasm.Resource.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- Use after free. -/
def cliUaf : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [.i32], [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨2⟩, .localGet ⟨0⟩,
    .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Double free. -/
def cliDoubleFree : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [.i32], [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨2⟩, .localGet ⟨0⟩,
    .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- A borrowed handle dropped. -/
def obFreeBorrow : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- An owned handle dropped twice. -/
def obFreeTwice : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨2⟩, .localGet ⟨0⟩, .call ⟨2⟩]⟩]
  exports := [⟨"keep", .func ⟨3⟩⟩]

/-- Roles: imports `alloc`, `use`, `free`; export `0` lends its argument. -/
def ρRun : NRoles where
  alloc i := i == 0
  use i := i == 1
  free i := i == 2
  give _ := false
  lend j := j == 0
  take _ := false

/-- Roles: imports `alloc`, `use`, `free`; export `0` transfers ownership of its argument. -/
def ρKeep : NRoles where
  alloc i := i == 0
  use i := i == 1
  free i := i == 2
  give _ := false
  lend _ := false
  take j := j == 0

end Silmaril.Wasm.Resource.ReplayExamples
