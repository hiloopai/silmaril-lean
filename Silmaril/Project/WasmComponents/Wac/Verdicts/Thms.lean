module

public import Silmaril.Project.WasmComponents.Wac.Elab.Thms
public import Silmaril.Project.WasmComponents.Wac.Typed.Thms

/-!
# The Wasm components pilot: the verdict DAG of the WAC composition

Loads `silmaril/wasm-components/wac-dag.toml`, the group `silmaril.wasm_components.wac` of the
rows and value obligations of `Silmaril.Project.WasmComponents.Wac.Thms`,
`Silmaril.Project.WasmComponents.Wac.Elab.Thms` and `Silmaril.Project.WasmComponents.Wac.Typed.Thms`
(split so that each module stays under 20 s).
-/

silmaril load "silmaril/wasm-components/wac-dag.toml"
