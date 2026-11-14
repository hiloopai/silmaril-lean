module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Versions.Thms

/-!
# The reactor adapter: where its embedded world is (kernel)

**PROVED** (kernel): in `adapter/wasi_snapshot_preview1.reactor.wasm` (wasmtime v50.0.1, 51660 B),
the one `component-type` custom section has its contents at bytes 29405 to 40200
(`extractPayloadFast`, equal to `Wit.Binary.extractPayload`).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem reactor_payloadAt : payloadAt silmaril.wasm_components.adapter.reactor.world.bytes.data 29405 40200 = true := by
  decide +kernel

end Silmaril.Project.WasmComponents.Kernel

end
