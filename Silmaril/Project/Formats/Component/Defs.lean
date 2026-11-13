module

public import Silmaril.Project.Defs
public import Silmaril.Project.Formats.Wasm.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Wit.Project.Defs

/-!
# Formats `wasm.component.*` and `wasm.module.*`

Component binaries as silmaril formats (`docs/projects/wasm-wasi.md`):

| name | value | parser | printer |
|---|---|---|---|
| **`wasm.component.binary`** | `Component.Binary.Ast` | `Component.Binary.parse` (verified grammar) | `Component.Binary.encode` |
| `wasm.component.ir` | `Comp CoreMod` (the nested component IR) | `parse`, then `lower` (partial) | none |
| `wasm.component.world` | `Wit.Project.WorldType` | `parse`, then `Wit.Project.project` | none |
| **`wasm.module.core3`** | `Silmaril.Wasm.Module` | the decoder of `wasm.binary.core` | as `wasm.binary.core` |

`wasm.component` defaults to `wasm.component.binary`, `wasm.module` to `wasm.module.core3`
(the same declaration as `wasm.binary.core`, under the name the component registry uses).

Laws (`Silmaril.Project.Formats.Component.Thms`): `wasm.component.binary` is `sound` for the
grammar `componentG` of the component-model binary format and satisfies `roundtrip`
(`parse_encode`); `wasm.component.ir` and `wasm.component.world` are `sound` for "the bytes
are a component of the grammar, and the IR lowering / world projection of that component is
the value".
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm.Component

/-- A component binary to its abstract syntax (`Component.Binary.parse`), printed back by
`Component.Binary.encode`. -/
def wasmComponent : Format blob Binary.Ast where
  parse b := match Binary.parse b.data with
    | .ok c => some c
    | .error _ => none
  print := some fun c => (Binary.encode c).map fun bs => ⟨bs⟩

/-- The specification relation of `wasm.component.binary`: the bytes are a component of the
grammar of the component-model binary format. -/
def ComponentRel (b : Silmaril.Formats.Bytes) (c : Binary.Ast) : Prop :=
  (Binary.componentG (b.data.size + 1)).G b.data.data.toList c

/-- A component binary lowered to the component IR (`Component.Binary.parseComponent`; the
lowering is partial, see `Silmaril.Wasm.Component.Binary.Lower.Defs`). -/
def wasmComponentIR : Format blob (Comp Binary.CoreMod) :=
  wasmComponent.andThen fun c => match Binary.lower c with
    | .ok m => some m
    | .error _ => none

/-- The specification relation of `wasm.component.ir`. -/
def ComponentIRRel (b : Silmaril.Formats.Bytes) (m : Comp Binary.CoreMod) : Prop :=
  ∃ c, ComponentRel b c ∧ Binary.lower c = .ok m

/-- A component binary to its world: the component type `Wit.Project.project` reads off. -/
def wasmComponentWorld : Format blob Silmaril.Wasm.Wit.Project.WorldType :=
  wasmComponent.andThen Silmaril.Wasm.Wit.Project.project

/-- The specification relation of `wasm.component.world`. -/
def ComponentWorldRel (b : Silmaril.Formats.Bytes) (w : Silmaril.Wasm.Wit.Project.WorldType) : Prop :=
  ∃ c, ComponentRel b c ∧ Silmaril.Wasm.Wit.Project.project c = some w

end Silmaril.Project.Formats

silmaril format wasm.component.binary := Silmaril.Project.Formats.wasmComponent
  (doc := "WebAssembly component binary to its AST (Component.Binary.parse, verified grammar); printer Component.Binary.encode")
silmaril format wasm.component.ir := Silmaril.Project.Formats.wasmComponentIR
  (base := wasm.component.binary)
  (doc := "Component binary lowered to the nested component IR (Component.Binary.lower, partial: no memory, strings, resources)")
silmaril format wasm.component.world := Silmaril.Project.Formats.wasmComponentWorld
  (base := wasm.component.binary)
  (doc := "Component binary to its world, the component type of its imports and exports (Wit.Project.project)")
silmaril format_default wasm.component := wasm.component.binary
silmaril format wasm.module.core3 := Silmaril.Project.Formats.wasm
  (doc := "WebAssembly core module binary to the Core 3.0 module AST; the declaration of wasm.binary.core")
silmaril format_default wasm.module := wasm.module.core3
