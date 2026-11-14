module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io0212.Defs
public import Silmaril.Project.WasmComponents.Thms

/-!
# `wasi:io@0.2.12`: the published file parses (kernel)

**PROVED** (kernel, about 13 s): Silmaril's list encoder (`Binary.Encode.ast`) writes the bytes of
the published file (`components/wasi/io-0.2.12.wasm`, OCI layer `sha256:910ed36e…`) from `io0212OciAst`, so the verified parser reads them back (`Kernel.is_of_ast`).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

/-- **The published `wasi:io@0.2.12` parses to `io0212OciAst`.** -/
theorem oci_list :
    Silmaril.Wasm.Component.Binary.Encode.ast io0212OciAst =
      some silmaril.wasm_components.wasi.io.v0_2_12.oci.bytes.data.data.toList := by
  decide +kernel

theorem oci_is : silmaril.wasm_components.wasi.io.v0_2_12.oci.Is io0212OciAst :=
  is_of_ast rfl oci_list

@[solves "silmaril.wasm_components.wasi.io.v0_2_12.oci.parses"]
theorem oci_parses : silmaril.wasm_components.wasi.io.v0_2_12.oci.parses := by
  show silmaril.wasm_components.wasi.io.v0_2_12.oci.parse.isSome = true
  rw [oci_is]; rfl

end Silmaril.Project.WasmComponents.Kernel

end
