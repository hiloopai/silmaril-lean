module

public import Silmaril.Project.WasmComponents.Kernel.Io0212.Fixture.Thms

/-!
# The `wasi:io@0.2.12` fixture as a WIT package: it decodes

**PROVED** (kernel): `tests/wat/fixtures/wasi-io-0.2.12.wasm` read under `wit.binary`
(`Wit.Binary.decodePackage`) decodes: the component parse is the certificate `fixture_list`,
and the sections are decoded by `decodeSectionsWith readDocsFast` (`witBinary_parse_of_ast`).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

theorem fixture_package_bytes : silmaril.wasm_components.wasi.io.v0_2_12.fixture.package.bytes =
    silmaril.wasm_components.wasi.io.v0_2_12.fixture.bytes := rfl

theorem fixture_package_parse : silmaril.wasm_components.wasi.io.v0_2_12.fixture.package.parse =
    witDecodeFast io0212FixtureAst :=
  witBinary_parse_of_ast rfl (by rw [fixture_package_bytes]; exact fixture_list)

@[solves "silmaril.wasm_components.wasi.io.v0_2_12.fixture.package.parses"]
theorem fixture_package_parses : silmaril.wasm_components.wasi.io.v0_2_12.fixture.package.parses := by
  show silmaril.wasm_components.wasi.io.v0_2_12.fixture.package.parse.isSome = true
  rw [fixture_package_parse]
  decide +kernel

end Silmaril.Project.WasmComponents.Kernel

end
