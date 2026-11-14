module

public import Silmaril.Project.Components.Defs

/-!
# The Wasm components pilot: its registry records

The pilot's binaries as registry records (`Silmaril.Project.Components`): releases
`namespace:name@version` with their SHA-256 digests (the `sha256` of `silmaril/artifacts.toml`),
and the builds whose recipes are pinned.

| record | release | digest | what it is |
|---|---|---|---|
| `ioOciRelease` | `wasi:io@0.2.12` | `910ed36e…` | the published OCI layer (`ghcr.io/webassembly/wasi/io:0.2.12`) |
| `ioFixtureRelease` | `wasi:io@0.2.12` | `085c156c…` | verified's `tests/wat` fixture of the same release |
| `compBRelease` | `silmaril:comp-b@0.1.0` | `778812d6…` | `gen.comp_b`, named here for the pilot |
| `Components.runRelease` | `silmaril:run@0.1.0` | `a0e91d45…` | `gen.run` (`component-run.wasm`) |

Builds (`Build`: source digest, toolchain, flags, output digest):

* `ioFixtureBuild`: `wasm-tools 1.263.0 component wit io.wit --wasm` on the `io.wit` of the
  crate `wasip2 1.0.4+wasi-0.2.12` (sha256 `96e206d0…`, `tests/wat/README.md`; checked against
  the crate on the build machine), giving the fixture.
* `ioReencodeBuild`: `wasm-wit encode` of the published file, giving the fixture's digest (the
  receipt `examples/wasm-components/RECEIPTS-reencode.sha256`).
* `ioOciBuild s`: the published file, built from a source `s` that its registry entry does not
  pin, by the toolchain its `producers` section names (`wit-component 0.244.0`,
  `wasm-pkg-core 0.15.0`).
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Project.Components

/-- A digest from 64 lowercase hex digits (the zero-length digest if they do not read). -/
def hexDigest (s : String) : Digest := (Digest.ofHex? s).getD default

/-- `wasi:io@0.2.12`. -/
def wasiIo : Silmaril.Wasm.Wit.PackageName :=
  { ns := "wasi", name := "io", version := some { major := 0, minor := 2, patch := 12 } }

def ioOciDigest : Digest :=
  hexDigest "910ed36e3589ab4c16c9942528152b80485e659852297916313318da47b44af8"

def ioFixtureDigest : Digest :=
  hexDigest "085c156c4b0426e44606a929db36c99042df4e20129a304ce0906496fda6f9d0"

/-- The sha256 of `wit/deps/io.wit` of the crate `wasip2 1.0.4+wasi-0.2.12`. -/
def ioWitDigest : Digest :=
  hexDigest "96e206d00076fa0480df32c5bcf255a3fa4862805ac2f6b8537a781cce54f433"

/-- `wasi:io@0.2.12` as published. -/
def ioOciRelease : Release := ⟨wasiIo, ioOciDigest⟩

/-- `wasi:io@0.2.12` as Silmaril's fixture. -/
def ioFixtureRelease : Release := ⟨wasiIo, ioFixtureDigest⟩

/-- `gen.comp_b` as a release `silmaril:comp-b@0.1.0`. -/
def compBRelease : Release where
  pkg := { ns := "hello", name := "comp-b", version := some { major := 0, minor := 1, patch := 0 } }
  digest := hexDigest "778812d65295fedaa45bf99c095227deeccdcb60224e8262e6deea18e1c05b5c"

/-- The fixture's build: `wasm-tools component wit io.wit --wasm`. -/
def ioFixtureBuild : Build :=
  ⟨ioWitDigest, [("wasm-tools", "1.263.0")], ["component", "wit", "--wasm"], ioFixtureDigest⟩

/-- `wasm-wit encode` of the published file. -/
def ioReencodeBuild : Build :=
  ⟨ioOciDigest, [("wasm-wit", "silmaril-lean")], ["encode"], ioFixtureDigest⟩

/-- The published file's build, from a source `s` the registry does not pin, by the toolchain
its `producers` section names. -/
def ioOciBuild (s : Digest) : Build :=
  ⟨s, [("wit-component", "0.244.0"), ("wasm-pkg-core", "0.15.0")], [], ioOciDigest⟩

end Silmaril.Project.WasmComponents

end
