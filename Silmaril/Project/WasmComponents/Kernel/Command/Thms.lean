module

public import Silmaril.Project.WasmComponents.Kernel.Command.Payload.Thms
public import Silmaril.Project.WasmComponents.Kernel.Command.Cert.Thms

/-!
# The command adapter: the world it embeds (kernel)

**PROVED** (kernel): `adapter/wasi_snapshot_preview1.command.wasm` read under `wasm.module.world`
(`Wit.Binary.extractWorldType`) is `commandWorld`, the frozen `Task`
`silmaril.wasm_components.versions.command_world` ; hence its `parses`. The payload's
place is `command_payloadAt`, its component AST `command_payload_list`, and the world decoding of
the AST's sections (`decodeWorldTypeSections`) runs here.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem command_world_parse : silmaril.wasm_components.adapter.command.world.parse =
    worldDecodeFast commandPayloadAst :=
  wasmModuleWorld_parse_of_ast rfl command_payloadAt command_payload_list

/-- **The `Task` `command_world`**: the command adapter embeds `commandWorld`. -/
@[solves "silmaril.wasm_components.versions.command_world"]
theorem command_world :
    Silmaril.Project.WasmComponents.Versions.Task.silmaril.wasm_components.versions.command_world := by
  show silmaril.wasm_components.adapter.command.world.parse =
    some Silmaril.Project.WasmComponents.Versions.commandWorld
  rw [command_world_parse]
  decide +kernel

@[solves "silmaril.wasm_components.adapter.command.world.parses"]
theorem command_world_parses : silmaril.wasm_components.adapter.command.world.parses := by
  have h : silmaril.wasm_components.adapter.command.world.parse =
      some Silmaril.Project.WasmComponents.Versions.commandWorld := command_world
  show silmaril.wasm_components.adapter.command.world.parse.isSome = true
  rw [h]; rfl

end Silmaril.Project.WasmComponents.Kernel

end
