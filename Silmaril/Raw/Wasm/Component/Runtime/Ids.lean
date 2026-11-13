module

public import Silmaril.Wasm.Component.Reference.Runtime.Ids.Defs

/-!
# Runtime object identities

Arena identities for the component-model runtime store (`Runtime.CStore`) and
the machine. The Python reference (`design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
refers to runtime objects by Python object identity; here every such object
lives in an append-only arena (`Runtime.Arena`) and is named by its index,
wrapped in a distinct structure per object kind so that ids of different kinds
cannot be confused:
`InstId`, `RtId`, `FuncId`, `TaskId`, `ThreadId`, `SubtaskId`, `HandleObjId`, `EndId`,
`WsetId`, `ErrCtxId`, `CallerId`, `CancelId`, `HostFuncId`, `HostBufId`, `CallId`.

These are *not* the per-instance handle-table indices that core wasm code sees
(those are `Nat` indices of `Runtime.Table`); a table slot stores one of these
ids. Nothing here is a specification of allocation: which fresh id an arena
returns is fixed by `Runtime.Arena.alloc` (its length).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

end Silmaril.Wasm.Component.Runtime
