module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Kernel.Reactor.Defs
public import Silmaril.Project.WasmComponents.Versions.Thms

/-!
# The reactor adapter: its embedded world is the component `reactorPayloadAst` (kernel)

**PROVED** (kernel): Silmaril's list encoder (`Binary.Encode.ast`) writes bytes 29405 to 40200 of
`adapter/wasi_snapshot_preview1.reactor.wasm` (its `component-type` payload) from
`reactorPayloadAst`, so the verified component parser reads that payload back.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem reactor_payload_list : Silmaril.Wasm.Component.Binary.Encode.ast reactorPayloadAst =
    some (sliceOf silmaril.wasm_components.adapter.reactor.world.bytes.data 29405 40200).data.toList := by
  decide +kernel

end Silmaril.Project.WasmComponents.Kernel

end
