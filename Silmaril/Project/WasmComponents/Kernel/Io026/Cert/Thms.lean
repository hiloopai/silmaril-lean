module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io026.Defs
public import Silmaril.Project.WasmComponents.Versions.Thms

/-!
# `wasi:io@0.2.6`: the component certificate (kernel)

**PROVED** (kernel): Silmaril's list encoder (`Binary.Encode.ast`) writes the bytes of
`components/wasi/io-0.2.6.wasm` (OCI layer `sha256:8e8ebc63…`) from `io026Ast`, so the verified
component parser reads them back (`Kernel.parse_of_list`).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem io026_list :
    Silmaril.Wasm.Component.Binary.Encode.ast io026Ast =
      some silmaril.wasm_components.wasi.io.v0_2_6.oci.bytes.data.data.toList := by
  decide +kernel

end Silmaril.Project.WasmComponents.Kernel

end
