module

public import Silmaril.Wasm.Resource.ExternClient.Defs

@[expose] public section

/-!
# Real `externref` clients that use and free their handles

Two real Core 3.0 modules with the reference-typed imports of
`Silmaril.Wasm.Resource.ExternExamples` (`env.alloc : [] → [externref]`, `env.use`, `env.free :
[externref] → []`, host codes `0`, `1`, `2`) and one export `run : [] → []`, the function at store
address `3`, with one `externref` local:

* `exAUF`: `call $alloc; local.set 0; local.get 0; call $use; local.get 0; call $free`;
* `exUAF`: `call $alloc; local.set 0; local.get 0; call $free; local.get 0; call $use`, a use after
  free.

Both untyped instances are `⟨Unit, fun _ => 3⟩`. The guard sets are `guardU` of the checker.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.ExternClientExamples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.UntypedExample Silmaril.Wasm.Resource.ExternExamples
  Silmaril.Wasm.Resource.ExternClient Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The types: `0 = [] → [externref]`, `1 = [externref] → []`, `2 = [] → []`. -/
def aufTypes : List RecType := handleTypes ++ [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]

/-- **Allocate, use, free.** -/
def exAUF : Module where
  types := aufTypes
  imports := handleImports
  funcs := [⟨⟨2⟩, [externRef],
    [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨1⟩, .localGet ⟨0⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- **Use after free.** -/
def exUAF : Module where
  types := aufTypes
  imports := handleImports
  funcs := [⟨⟨2⟩, [externRef],
    [.call ⟨0⟩, .localSet ⟨0⟩, .localGet ⟨0⟩, .call ⟨2⟩, .localGet ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- The instantiated store of `exAUF`. -/
abbrev aufS : Store Nat := storeOf exAUF

/-- The instantiated store of `exUAF`. -/
abbrev uafS : Store Nat := storeOf exUAF

/-- The untyped instance of `exAUF`: the export `run` at address `3`. -/
def aufU : UInstance := ⟨Unit, fun _ => 3⟩

/-- The untyped instance of `exUAF`: the export `run` at address `3`. -/
def uafU : UInstance := ⟨Unit, fun _ => 3⟩

/-- The function list of both modules. -/
def fs4 : List Nat := [0, 1, 2, 3]

/-- The guard set of `exAUF`: the checker's `guardU`. -/
abbrev aufG : List Nat := guardU aufS fs4 [3] 0 1 2

end Silmaril.Wasm.Resource.ExternClientExamples
