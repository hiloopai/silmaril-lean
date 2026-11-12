module

public import Silmaril.Wasm.Game.Signature.Defs
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Scalar instances: data and fresh host functions

The executable data of the game semantics of Core 3.0 instances, without the
game semantics itself (`Silmaril.Wasm.Game.Strategy`, `Silmaril.Wasm.Game.Instantiate`,
`Silmaril.Wasm.Game.SpecInst` build on it):

* `ScalarInstance`: an instantiated module with scalar function imports and
  exports (import types, export types, export addresses, store);
* `importStore ds`: one fresh host function per import (code `.host j` at
  address `j`), and `importAddrs mt` their addresses `0, …, n - 1`;
* `exportFuncAddrs mi`: the function addresses of the function exports.

Executable checkers (`Silmaril.Wasm.Verify`) instantiate modules with these
definitions and import only this header.
-/

@[expose] public section

namespace Silmaril.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- An instantiated module with scalar function interfaces. Host function code `.host i`
denotes import `i`. -/
structure ScalarInstance where
  /-- The types of the imported functions. -/
  imports : List FnType
  /-- The types of the exported functions. -/
  exports : List FnType
  /-- The function address implementing each export. -/
  addrs : List Nat
  /-- The store right after instantiation. -/
  store : Store Nat

/-- A store holding one host function per import, with code its index. -/
def importStore (ds : List DefType) : Store Nat :=
  { funcs := ds.mapIdx fun j d => { type := d, module := {}, code := .host j } }

/-- The function addresses of the function exports of a module instance, in export order. -/
def exportFuncAddrs (mi : ModuleInst) : List Nat :=
  mi.exports.filterMap fun x => match x.addr with
    | .func a => some a
    | _ => none

/-- The import addresses `0, …, n - 1` of the fresh host functions of `importStore`. -/
def importAddrs (mt : CModuleType) : List ExternAddr :=
  (List.range mt.imports.length).map ExternAddr.func

end Silmaril.Wasm.Game
