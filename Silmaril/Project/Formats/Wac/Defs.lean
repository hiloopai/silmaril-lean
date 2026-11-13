module

public import Silmaril.Project.Formats.Component.Defs
public import Silmaril.Wasm.Wac.Text.Parse.Defs
public import Silmaril.Wasm.Wac.Text.Print.Defs
public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Wac.Targets.Defs

/-!
# Formats `wac.*`

WAC, the composition language of the Component Model, as silmaril formats, on the WAC
formalization `Silmaril/Wasm/Wac` (`docs/projects/wasm-wasi.md`; read here from `origin/wasm-wac` at
`1e3e6e7cc`, not edited):

| name | value | parser | printer |
|---|---|---|---|
| **`wac.text`** | `Wac.Text.Document` (surface syntax) | UTF-8, then the verified `Wac.Text.parse` | `Wac.Text.print`, on well-formed documents |
| `wac.composition` | `Component.Binary.Ast` in the composition profile | `wasm.component.binary`, then `Wac.isProfile` | `Component.Binary.encode`, on profile components |
| `wac.world` | `Wit.Project.WorldType` (names and sorts) | `wac.composition`, then `Wac.Targets.surface` | none |
| `wac.ir` | `Comp CoreMod` | `wac.composition`, then `Wac.Lower.toCompCore` (packages embedded) | none |

`wac` defaults to `wac.text`. A `wac compose` output (with embedded packages, the default
`--import-dependencies false`) is a `wac.composition`.

**Why `wac.world` is a world of names and sorts.** The typed projection
`Wit.Project.project` (`wasm.component.world`) is undefined on the usual `wac compose` output:
its exports are aliased from instances the composition creates, and their function types live
inside the embedded components (see `Silmaril.Wasm.Wac.Targets`). `Wac.Targets.surface` is total;
`wac.ir` gives the typed function-level world (`Wit.Project.compWorld`) when the embedded
packages are in the `Binary.lower` subset.

Laws (`Silmaril.Project.Formats.Wac.Thms`): `wac.text` satisfies `roundtrip`
(`Wac.Text.parse_print`); `wac.composition` satisfies `roundtrip` and is `sound` for "a
component of the component grammar, in the composition profile"; `wac.world` and `wac.ir` are
`sound` for "a profile component of the grammar, whose surface world / lowering is the value".

A Silmaril addition.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm

/-- WAC text (UTF-8) to its document; printed back only when well formed (`Wac.Text.wf`, the
condition of the round trip). -/
def wacText : Format blob Wac.Text.Document where
  parse b := (String.fromUTF8? b.data).bind Wac.Text.parse
  print := some fun d => if Wac.Text.wf d then some ⟨(Wac.Text.print d).toUTF8⟩ else none

/-- A composed component (component binary) in the composition profile of `wac-graph`. -/
def wacComposition : Format blob Component.Binary.Ast where
  parse b := (wasmComponent.parse b).bind fun c => if Wac.isProfile c then some c else none
  print := some fun c =>
    if Wac.isProfile c then (Component.Binary.encode c).map fun bs => ⟨bs⟩ else none

/-- The specification relation of `wac.composition`: a component of the grammar, in the
composition profile. -/
def WacCompositionRel (b : Silmaril.Formats.Bytes) (c : Component.Binary.Ast) : Prop :=
  ComponentRel b c ∧ Wac.Profile c

/-- A composition to its world of names and sorts (`Wac.Targets.surface`). -/
def wacWorld : Format blob Wit.Project.WorldType :=
  wacComposition.andThen fun c => some (Wac.Targets.surface c)

/-- The specification relation of `wac.world`. -/
def WacWorldRel (b : Silmaril.Formats.Bytes) (w : Wit.Project.WorldType) : Prop :=
  ∃ c, WacCompositionRel b c ∧ Wac.Targets.surface c = w

/-- A composition, with its packages embedded, as a component of the component IR
(`Wac.Lower.toCompCore`). -/
def wacIR : Format blob (Component.Comp Component.Binary.CoreMod) :=
  wacComposition.andThen fun c => (Wac.Lower.toCompCore c).toOption

/-- The specification relation of `wac.ir`. -/
def WacIRRel (b : Silmaril.Formats.Bytes) (m : Component.Comp Component.Binary.CoreMod) : Prop :=
  ∃ c, WacCompositionRel b c ∧ Wac.Lower.toCompCore c = .ok m

end Silmaril.Project.Formats

silmaril format wac.text := Silmaril.Project.Formats.wacText
  (doc := "WAC text (UTF-8) to its document (Wac.Text.parse, verified lexer and parser); printer Wac.Text.print on well-formed documents")
silmaril format_default wac := wac.text
silmaril format wac.composition := Silmaril.Project.Formats.wacComposition
  (doc := "A composed component (wac compose output) to its AST in the composition profile (Component.Binary.parse, Wac.isProfile); printer Component.Binary.encode")
silmaril format wac.world := Silmaril.Project.Formats.wacWorld
  (base := wac.composition)
  (doc := "A composed component to the names and sorts of its imports and exports (Wac.Targets.surface)")
silmaril format wac.ir := Silmaril.Project.Formats.wacIR
  (base := wac.composition)
  (doc := "A composed component with embedded packages to the component IR (Wac.Lower.toCompCore, partial)")
