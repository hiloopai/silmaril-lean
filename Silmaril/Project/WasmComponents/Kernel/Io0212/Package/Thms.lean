module

public import Silmaril.Project.WasmComponents.Kernel.Io0212.Oci.Thms
public import Silmaril.Project.WasmComponents.Versions.Thms

/-!
# `wasi:io@0.2.12` as a WIT package: it decodes, with the summary 

**PROVED** (kernel): the published file read under `wit.binary` (`Wit.Binary.decodePackage`)
decodes, and its package has the summary `io0212Summary`, the frozen `Task`
`silmaril.wasm_components.versions.io_0_2_12_summary` . The component parse is the
certificate `oci_list`; the sections are decoded by `decodeSectionsWith readDocsFast`
(`witBinary_parse_of_ast`), on the AST, with the 12 KB `package-docs` section read as ASCII.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Project.Shapes.Component

theorem oci_package_bytes : silmaril.wasm_components.wasi.io.v0_2_12.oci.package.bytes =
    silmaril.wasm_components.wasi.io.v0_2_12.oci.bytes := rfl

/-- The published `wasi:io@0.2.12` under `wit.binary` is the fast decoding of its AST. -/
theorem oci_package_parse : silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse =
    witDecodeFast io0212OciAst :=
  witBinary_parse_of_ast rfl (by rw [oci_package_bytes]; exact oci_list)

/-- **The `Task` `io_0_2_12_summary`**: `wasi:io@0.2.12` decodes to a package with summary
`io0212Summary`. -/
@[solves "silmaril.wasm_components.versions.io_0_2_12_summary"]
theorem io0212_summary : Silmaril.Project.WasmComponents.Versions.Task.silmaril.wasm_components.versions.io_0_2_12_summary := by
  show silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse.map summary =
    some Silmaril.Project.WasmComponents.Versions.io0212Summary
  rw [oci_package_parse]
  decide +kernel

@[solves "silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parses"]
theorem oci_package_parses : silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parses := by
  have h : silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse.map summary =
      some Silmaril.Project.WasmComponents.Versions.io0212Summary := io0212_summary
  show silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse.isSome = true
  cases e : silmaril.wasm_components.wasi.io.v0_2_12.oci.package.parse with
  | none => rw [e] at h; cases h
  | some _ => rfl

end Silmaril.Project.WasmComponents.Kernel

end
