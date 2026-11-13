module

public import Silmaril.Project.WasmComponents.Kernel.Io026.Cert.Thms

/-!
# `wasi:io@0.2.6`: the published file decodes, with the summary 

**PROVED** (kernel):

* `io026_list` (`….Io026.Cert.Thms`): Silmaril's list encoder writes the bytes of `components/wasi/io-0.2.6.wasm` (OCI
  layer `sha256:8e8ebc63…`) from `io026Ast`, so the component parser reads them back;
* `io026_summary`: read under `wit.binary`, the file decodes to a package with summary
  `io026Summary`, the frozen `Task` `silmaril.wasm_components.versions.io_0_2_6_summary` ;
  hence its `parses`.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Project.Shapes.Component

theorem io026_parse : silmaril.wasm_components.wasi.io.v0_2_6.oci.parse =
    witDecodeFast io026Ast :=
  witBinary_parse_of_ast rfl io026_list

/-- **The `Task` `io_0_2_6_summary`**: `wasi:io@0.2.6` decodes to a package with summary
`io026Summary`. -/
@[solves "silmaril.wasm_components.versions.io_0_2_6_summary"]
theorem io026_summary : Silmaril.Project.WasmComponents.Versions.Task.silmaril.wasm_components.versions.io_0_2_6_summary := by
  show silmaril.wasm_components.wasi.io.v0_2_6.oci.parse.map summary =
    some Silmaril.Project.WasmComponents.Versions.io026Summary
  rw [io026_parse]
  decide +kernel

@[solves "silmaril.wasm_components.wasi.io.v0_2_6.oci.parses"]
theorem io026_parses : silmaril.wasm_components.wasi.io.v0_2_6.oci.parses := by
  have h : silmaril.wasm_components.wasi.io.v0_2_6.oci.parse.map summary =
      some Silmaril.Project.WasmComponents.Versions.io026Summary := io026_summary
  show silmaril.wasm_components.wasi.io.v0_2_6.oci.parse.isSome = true
  cases e : silmaril.wasm_components.wasi.io.v0_2_6.oci.parse with
  | none => rw [e] at h; cases h
  | some _ => rfl

end Silmaril.Project.WasmComponents.Kernel

end
