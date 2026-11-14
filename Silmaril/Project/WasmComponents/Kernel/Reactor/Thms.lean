module

public import Silmaril.Project.WasmComponents.Kernel.Reactor.Payload.Thms
public import Silmaril.Project.WasmComponents.Kernel.Reactor.Cert.Thms

/-!
# The reactor adapter: the world it embeds (kernel)

**PROVED** (kernel): `adapter/wasi_snapshot_preview1.reactor.wasm` read under `wasm.module.world`
(`Wit.Binary.extractWorldType`) is `reactorWorld`, the frozen `Task`
`silmaril.wasm_components.versions.reactor_world` ; hence its `parses`. The payload's
place is `reactor_payloadAt`, its component AST `reactor_payload_list`, and the world decoding of
the AST's sections (`decodeWorldTypeSections`) runs here.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem reactor_world_parse : silmaril.wasm_components.adapter.reactor.world.parse =
    worldDecodeFast reactorPayloadAst :=
  wasmModuleWorld_parse_of_ast rfl reactor_payloadAt reactor_payload_list

/-- **The `Task` `reactor_world`**: the reactor adapter embeds `reactorWorld`. -/
@[solves "silmaril.wasm_components.versions.reactor_world"]
theorem reactor_world :
    Silmaril.Project.WasmComponents.Versions.Task.silmaril.wasm_components.versions.reactor_world := by
  show silmaril.wasm_components.adapter.reactor.world.parse =
    some Silmaril.Project.WasmComponents.Versions.reactorWorld
  rw [reactor_world_parse]
  decide +kernel

@[solves "silmaril.wasm_components.adapter.reactor.world.parses"]
theorem reactor_world_parses : silmaril.wasm_components.adapter.reactor.world.parses := by
  have h : silmaril.wasm_components.adapter.reactor.world.parse =
      some Silmaril.Project.WasmComponents.Versions.reactorWorld := reactor_world
  show silmaril.wasm_components.adapter.reactor.world.parse.isSome = true
  rw [h]; rfl

end Silmaril.Project.WasmComponents.Kernel

end
