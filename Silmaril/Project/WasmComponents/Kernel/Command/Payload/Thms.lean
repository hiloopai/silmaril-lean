module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Versions.Thms

/-!
# The command adapter: where its embedded world is (kernel)

**PROVED** (kernel): in `adapter/wasi_snapshot_preview1.command.wasm` (wasmtime v50.0.1, 51854 B),
the one `component-type` custom section has its contents at bytes 29470 to 40309
(`extractPayloadFast`, equal to `Wit.Binary.extractPayload`).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem command_payloadAt : payloadAt silmaril.wasm_components.adapter.command.world.bytes.data 29470 40309 = true := by
  decide +kernel

end Silmaril.Project.WasmComponents.Kernel

end
