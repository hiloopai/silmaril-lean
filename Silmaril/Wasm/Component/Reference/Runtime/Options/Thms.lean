module

public import Silmaril.Wasm.Component.Reference.Runtime.Options.Defs
public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Wasm.Component.Reference.Runtime.Ids.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs

/-!
# `Runtime.Options`: laws of the component reference

Theorems of the component reference copy `Runtime.Options`, refined out of `Silmaril.Raw`: the
ones other topics use (through `Silmaril.Wasm.Component.Reference.Laws.Thms`) and the laws their
proofs need. The other theorems stay in `Silmaril.Raw.Wasm.Component.Runtime.Options`, which
imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

namespace CanonOpts

variable {E : CoreEngine}

theorem ptrType_none (memAddr : E.MemAddr → AddrType) (o : CanonOpts E) (h : o.memory = none) :
    o.ptrType memAddr = .i32 := by
  simp [ptrType, h]

end CanonOpts

end Silmaril.Wasm.Component.Runtime
