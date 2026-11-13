module

public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Core.Soundness.InstantiationOnceAlloc.Defs
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

@[expose] public section

/-! # Typing of the allocation of the global-free residue

`Instantiate.alloc_ok_residue`: the allocation of the global-free residue
(`Module.globalResidue`) of a valid module, against the globals that `$evalglobals` allocated
(typed at the module's closed global types), gives a typed store and a module instance typed
against the module context. It is the counterpart of `Instantiate.alloc_ok_aux` for single
allocation: the module's globals are not allocated again, and the instance names those that
`$evalglobals` allocated, after the imported ones.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

end Silmaril.Wasm.Execution.Core
