module

public import Silmaril.Wasm.Game.Strategy.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Scalar instances of Core 3.0 modules

A `ScalarInstance` is abstract (types, export addresses, store).
`IsInstance m mt I` says that `I` is *the* instance of the module `m` against
fresh host functions for its imports:

* `m` validates with module type `mt`, every import of `mt` is a function, and
  the closed import types `ds = CExternType.funcs mt.imports` have the scalar
  function types `I.imports` (this ties the host functions to the module's
  declared import types: `instantiateOnce?` does not check import types);
* `m` is instantiated by silmaril-lean's `instantiateOnce?` into
  `importStore ds`, which holds one host function per import (import `j` is
  the host function with code `.host j` at address `j`, of type `ds[j]`),
  against the addresses `0, …, |ds| - 1`;
* there is **no start function** (`instantiateOnce?` returns `none` as the
  pending start call): a start function would run during instantiation,
  possibly calling imports, before any export call. Modules with a start
  function are `IsInstanceStart` (`Silmaril.Wasm.Game.Start`), whose strategy has
  an instantiation phase; `isInstanceStart_none_iff` makes `IsInstance` its
  start-free case;
* the function exports, in export order, are at `I.addrs` and have the scalar
  types `I.exports`.

`IsInstance.ok` (`Silmaril.Wasm.Game.Instantiate.Thms`): such an instance is well
formed, so `I.σ P` is the strategy of the module `m` and adequacy (M2)
applies to it; `Module.strategy` packages this.
-/

@[expose] public section

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- `I` is the instance of the module `m` (of validated type `mt`) against fresh host
functions for its imports (see the module docstring). -/
structure IsInstance (m : Module) (mt : CModuleType) (I : ScalarInstance) : Prop where
  valid : validate? m = some mt
  funcImports : ∀ xt ∈ mt.imports, ∃ d, xt = .func d
  importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs mt.imports) I.imports
  instantiated : ∃ f : Frame,
    instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
        ((List.range mt.imports.length).map ExternAddr.func) = some (I.store, f, none) ∧
      exportFuncAddrs f.module = I.addrs
  exportTypes : List.Forall₂
    (fun a ft => ∃ fi : FuncInst Nat, I.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports

end Silmaril.Wasm.Game
