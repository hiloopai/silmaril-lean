module

public import Silmaril.Wasm.Models.V2CoreInstImp.Thms

/-!
# The instantiation domain at stores with functions: definitions

An earlier step put points with imports in `V2CoreInstImp.domInstP P`, but only points whose
store has no function. The point below has one.

* `nopType`: the 2.0 function type `[] → []`.
* `nopModInst`: the module instance with the single type `nopType` and the single function
  address `0`.
* `nopFunc`: the instance of a Wasm function of type `nopType` (type index `0`), no locals and an
  empty body, in `nopModInst`.
* `fnStore`, `fnPt`: the store holding `nopFunc` and nothing else, and that store with the
  closed host. A module may import its function at type `nopType`.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstFn

open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec

/-- The 2.0 function type `[] → []`. -/
def nopType : Silmaril.Wasm.V2.FuncType := ⟨[], []⟩

/-- The module instance with the single type `nopType` and the single function address `0`. -/
def nopModInst : Silmaril.Wasm.V2.Execution.ModuleInst :=
  { types := [nopType], funcs := [0] }

/-- A Wasm function of type `nopType`, with no locals and an empty body, in `nopModInst`. -/
def nopFunc : Silmaril.Wasm.V2.Execution.FuncInst Nat :=
  { type := nopType, module := nopModInst, code := .wasm { type := ⟨0⟩, locals := [], body := [] } }

/-- The 2.0 store holding `nopFunc` and nothing else. -/
def fnStore : Silmaril.Wasm.V2.Execution.Store Nat := { funcs := [nopFunc] }

/-- `fnStore` with the closed host. -/
def fnPt : Pt Nat := (fnStore, closedV)

end Silmaril.Wasm.Models.V2CoreInstFn
