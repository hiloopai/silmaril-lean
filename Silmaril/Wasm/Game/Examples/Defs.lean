module

public import Silmaril.Wasm.Game.SpecInst.Defs

/-!
# A module whose start function calls an import

Non-vacuity example for the spec-faithful instantiation of
`Silmaril.Wasm.Game.SpecInst`:

```wat
(module
  (type (func))
  (import "env" "f" (func (type 0)))   ;; function 0
  (func (type 0) call 0)                ;; function 1: calls the import
  (start 1)                             ;; the module's actual start field
  (export "run" (func 1)))
```

* `exStart`: the module (silmaril-lean's `Module`, with `start := some 1`);
* `exMT`: its validated module type (`validate?`; the default is never used,
  `Silmaril.Wasm.Game.Examples.exStart_valid`);
* `exPrep`: the result of the spec's allocation `prepare?` into `importStore`;
* `exC₀`: the configuration of `$instantiate` (`call 1`; no segments);
* `exI`: the scalar instance (one import and one export of type `[] → []`);
* `exAnswer`: the environment answering every import call with `values []`.

A second module, `exMem`, imports a **memory** and a function, has an active
data segment for the imported memory and the same start function; it is
instantiated by the spec into the store `exMemStore` holding the memory and a
host function (`IsSpecInstanceAt`), so its `$instantiate` configuration
`exMemC₀` runs `memory.init`/`data.drop` before the start call.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Examples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation

/-- A module with one imported function `[] → []` and a start function that calls it. -/
def exStart : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "f", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]
  start := some ⟨1⟩
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The validated type of `exStart`. -/
def exMT : CModuleType := (validate? exStart).getD ⟨[], []⟩

/-- The spec's allocation of `exStart` against fresh host functions for its import. -/
def exPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs exMT.imports)) exStart
    (importAddrs exMT)).getD (⟨{}, {}, []⟩, none)

/-- The configuration of `$instantiate` for `exStart`. -/
def exC₀ : Config Nat := exPrep.1.withStart exPrep.2

/-- The scalar instance of `exStart`. -/
def exI : ScalarInstance where
  imports := [⟨[], []⟩]
  exports := [⟨[], []⟩]
  addrs := exportFuncAddrs exPrep.1.frame.module
  store := exPrep.1.store

/-- The empty typed result list of a function type without results. -/
def unitTyped (ft : FnType) (h : ft.results = []) : Typed ft.results := ⟨[], h ▸ .nil⟩

/-- The environment answering every import call of `exI` with `values []`. -/
def exAnswer : Env exI.E := fun e => some (.values (unitTyped _ (by
  obtain ⟨⟨i, hi⟩, _⟩ := e
  have h0 : i = 0 := by simp [exI] at hi; omega
  subst h0
  rfl)))

/-! ## A module importing a memory -/

/-- The memory type `i32 0` (no pages). -/
def memTy : MemoryType := ⟨.i32, ⟨0, none⟩⟩

/-- A module importing a memory and a function, with an active (empty) data segment for the
imported memory and a start function calling the imported function. -/
def exMem : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "mem", .memory memTy⟩, ⟨"env", "f", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]
  data := [⟨ByteArray.empty, .active ⟨0⟩ [.intConst .i32 0]⟩]
  start := some ⟨1⟩
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The validated type of `exMem`. -/
def exMemMT : CModuleType := (validate? exMem).getD ⟨[], []⟩

/-- The store providing the imports of `exMem`: a memory of type `memTy` (owned by the closed
program) and a host function for the imported function. -/
def exMemStore : Store Nat :=
  { mems := [⟨memTy, ByteArray.empty⟩],
    funcs := (importStore (CExternType.funcs exMemMT.imports)).funcs }

/-- The external addresses of the imports of `exMem`. -/
def exMemXas : List ExternAddr := [.mem 0, .func 0]

/-- The spec's allocation of `exMem` into `exMemStore`. -/
def exMemPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? exMemStore exMem exMemXas).getD (⟨{}, {}, []⟩, none)

/-- The configuration of `$instantiate` for `exMem`: the data segment's `memory.init`, then the
start call. -/
def exMemC₀ : Config Nat := exMemPrep.1.withStart exMemPrep.2

/-- The scalar instance of `exMem`. -/
def exMemI : ScalarInstance where
  imports := [⟨[], []⟩]
  exports := [⟨[], []⟩]
  addrs := exportFuncAddrs exMemPrep.1.frame.module
  store := exMemPrep.1.store

end Silmaril.Wasm.Game.Examples
