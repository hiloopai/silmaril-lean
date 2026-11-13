module

public import Silmaril.Wasm.Component.Binary.Example.Defs

/-!
# The Wasm components pilot: a provider component for a WAC composition

`provider` is the producer half of `Binary.Example.linked` as a component of its own: it
instantiates the core module `Binary.Example.producer` (`get` returns `42`), lifts `get` at the
type `func() -> u32` and exports it as `get`. `Binary.Example.compB` imports a function `get` of
that type and exports `run` (`get() + 1`). The WAC source
`examples/wasm-components/wac/pilot.wac` plugs the one into the other, and
`wac compose` (wac-cli 0.12.0) writes the composition `pilot.wasm`; see
`docs/projects/wasm-wasi.md` and `Silmaril.Project.WasmComponents.Wac.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Wac

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Example

/-- The producer as a component: instantiate `producer`, lift its `get` and export it. -/
def provider : Ast := .mk [
  .coreModule producer,
  .types [getTy],
  .coreInstances [.instantiate 0 []],
  .aliases [⟨.core .func, .coreExport 0 "get"⟩],
  .canons [.lift 0 [] 0],
  .exports [⟨↑"get", ⟨.func, 0⟩, none⟩]]

/-- The bytes of a custom section's contents. -/
def bytesOf (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The `component-name` section `wac compose` writes: the instance `0` is named `provider`,
the instance `1` `b`. -/
def nameSection : ByteArray := bytesOf [0x01, 0x0f, 0x05, 0x02, 0x00, 0x08,
  0x70, 0x72, 0x6f, 0x76, 0x69, 0x64, 0x65, 0x72, 0x01, 0x01, 0x62]

/-- The `producers` section: `processed-by wac-parser 0.12.0`. -/
def producersSection : ByteArray := bytesOf [0x01, 0x0c,
  0x70, 0x72, 0x6f, 0x63, 0x65, 0x73, 0x73, 0x65, 0x64, 0x2d, 0x62, 0x79, 0x01, 0x0a,
  0x77, 0x61, 0x63, 0x2d, 0x70, 0x61, 0x72, 0x73, 0x65, 0x72, 0x06,
  0x30, 0x2e, 0x31, 0x32, 0x2e, 0x30]

/-- **The composition `wac compose` writes for `pilot.wac`** (wac-cli 0.12.0): the provider and
`compB` embedded as components, each instantiated, the provider's `get` passed to `compB`, and
`compB`'s `run` exported. -/
def pilot : Ast := .mk [
  .component provider,
  .instances [.instantiate 0 []],
  .aliases [⟨.func, .export 0 "get"⟩],
  .component compB,
  .instances [.instantiate 1 [("get", ⟨.func, 0⟩)]],
  .aliases [⟨.func, .export 1 "run"⟩],
  .exports [⟨↑"run", ⟨.func, 1⟩, none⟩],
  .custom "component-name" nameSection,
  .custom "producers" producersSection]

end Silmaril.Project.WasmComponents.Wac

end
