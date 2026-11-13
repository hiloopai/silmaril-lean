import Silmaril.Project.WasmComponents.Versions.Thms

/-!
The compiled check of the six frozen `Task`s of `Silmaril.Project.WasmComponents.Versions.Thms`:
each equation between a registered value's decoding and a term of
`Silmaril.Project.WasmComponents.Versions.Defs`, evaluated by `decide` in the interpreter (not the
kernel). Run from the repository root after building that module:

    lake env lean examples/wasm-components/gen/VersionsCheck.lean

Each line prints `true`.
-/

open Silmaril.Project.WasmComponents.Versions Silmaril.Project.Shapes.Component

#eval decide (silmaril.wasm_components.adapter.reactor.world.parse = some reactorWorld)
#eval decide (silmaril.wasm_components.adapter.reactor.parse.map coreImports = some reactorImports)
#eval decide (silmaril.wasm_components.adapter.command.world.parse = some commandWorld)
#eval decide (silmaril.wasm_components.adapter.command.parse.map coreImports = some commandImports)
#eval decide (silmaril.wasm_components.wasi.io.v0_2_6.oci.parse.map summary = some io026Summary)
#eval decide (silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse.map summary = some io0212Summary)
