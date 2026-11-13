module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Kernel.Command.Defs
public import Silmaril.Project.WasmComponents.Versions.Thms

/-!
# The command adapter: its embedded world is the component `commandPayloadAst` (kernel)

**PROVED** (kernel): Silmaril's list encoder (`Binary.Encode.ast`) writes bytes 29470 to 40309 of
`adapter/wasi_snapshot_preview1.command.wasm` (its `component-type` payload) from
`commandPayloadAst`, so the verified component parser reads that payload back.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem command_payload_list : Silmaril.Wasm.Component.Binary.Encode.ast commandPayloadAst =
    some (sliceOf silmaril.wasm_components.adapter.command.world.bytes.data 29470 40309).data.toList := by
  decide +kernel

end Silmaril.Project.WasmComponents.Kernel

end
