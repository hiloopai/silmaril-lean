module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# A closed module for native adequacy

Non-vacuity example for `Silmaril.Wasm.Interp.native_adequacy`:

```wat
(module
  (type (func (param i32 i32) (result i32)))
  (func (type 0)
    (block (result i32)
      (select (local.get 0) (local.get 1) (local.get 0))  ;; a ≠ 0 ? a : b
      (br_table 0 0 (local.get 1))))                      ;; carries it out of the block
  (export "f" (func 0)))
```

* `exMod`: the module (silmaril-lean's Core `Module`), with a `select` and a `br_table`;
* `exPrep`: the result of silmaril-lean's executable instantiation `prepare?` into the empty
  store (no imports, no segments, no start function);
* `exStore`: the store it allocates (one Wasm function at address `0`).

Theorems in `Silmaril.Wasm.Interp.Example.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `i32`. -/
abbrev i32 : ValType := .num (.int .i32)

/-- The example module. -/
def exMod : Module where
  types := [⟨[⟨true, [], .func ⟨[i32, i32], [i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.block (.value i32)
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .localGet ⟨0⟩, .select none, .localGet ⟨1⟩,
      .brTable [⟨0⟩] ⟨0⟩]]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The spec's allocation of `exMod` into the empty store. -/
def exPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) exMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `exMod`. -/
def exStore : Store Empty := exPrep.1.store

end Silmaril.Wasm.Interp.Example
