module

public import Silmaril.Project.WasmComponents.Kernel.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io0212.Defs
public import Silmaril.Project.WasmComponents.Thms

/-!
# `wasi:io@0.2.12`: the `tests/wat` fixture parses (kernel)

**PROVED** (kernel, about 13 s): Silmaril's list encoder (`Binary.Encode.ast`) writes the bytes of
`tests/wat/fixtures/wasi-io-0.2.12.wasm` from `io0212FixtureAst`, so the verified parser reads them back (`Kernel.is_of_ast`).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

/-- **The fixture parses to `io0212FixtureAst`.** -/
theorem fixture_list :
    Silmaril.Wasm.Component.Binary.Encode.ast io0212FixtureAst =
      some silmaril.wasm_components.wasi.io.v0_2_12.fixture.bytes.data.data.toList := by
  decide +kernel

theorem fixture_is : silmaril.wasm_components.wasi.io.v0_2_12.fixture.Is io0212FixtureAst :=
  is_of_ast rfl fixture_list

@[solves "silmaril.wasm_components.wasi.io.v0_2_12.fixture.parses"]
theorem fixture_parses : silmaril.wasm_components.wasi.io.v0_2_12.fixture.parses := by
  show silmaril.wasm_components.wasi.io.v0_2_12.fixture.parse.isSome = true
  rw [fixture_is]; rfl

end Silmaril.Project.WasmComponents.Kernel

end
