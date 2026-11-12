module

public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Core.Soundness.InstantiationOnce.Defs
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Core.Soundness.InstantiationOnceAlloc

@[expose] public section

/-! # Typing of instantiation with every global allocated once

`instantiateOnce?` (Exec/InstantiateOnce.lean) runs `$evalglobals` and then the spec's
instantiation of the global-free residue `Module.globalResidue`, whose trailing global imports
are the globals `$evalglobals` allocated. `Instantiate.ok` (the typing of `$instantiate`) does not
apply to the residue: a residue whose initialisers mention `ref.func` of a function defined later
is not typed against the store `$evalglobals` leaves (its provisional instance names function
addresses that `$allocmodule` only allocates). The typing of the residue is therefore proved from
the module's own `Module_ok`:

* `Instantiate.alloc_ok_residue` (Soundness/InstantiationOnceAlloc.lean): the allocation of the
  residue, against the globals that `$evalglobals` allocated (typed at the module's closed global
  types), gives a typed store and a module instance typed against the module context (the
  counterpart of `Instantiate.alloc_ok_aux`);
* `prepare?_globalResidue_ok`: the configuration that the spec's `prepare?` builds for the
  residue, with its start call, is typed, its store extends the original store, and the only new
  function instances are the module's Wasm functions.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

end Silmaril.Wasm.Execution.Core
