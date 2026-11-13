module

public import Silmaril.Project.Formats.Component.Defs
public import Silmaril.Wasm.Wit.Text.Parse.Defs
public import Silmaril.Wasm.Wit.Text.Print.Defs
public import Silmaril.Wasm.Wit.Elab.Defs
public import Silmaril.Wasm.Wit.Binary.Custom.Defs
public import Silmaril.Wasm.Wit.Binary.Embed.Defs

/-!
# Formats `wit.*` and `wasm.module.world`

WIT, the interface language of the Component Model, as silmaril formats, on the WIT
formalization `Silmaril/Wasm/Wit` (`tools/wasm-tools/README.md`):

| name | value | parser | printer |
|---|---|---|---|
| **`wit.text`** | `Wit.Document` (surface syntax) | UTF-8, then the verified `Wit.Text.parse` | `Wit.Text.print` |
| `wit.package` | `Wit.Binary.Package × Wit.Binary.Env` | `wit.text`, then `Wit.Elab.elaborate` of the main package | none |
| `wit.binary` | `Wit.Binary.Package` | `Wit.Binary.decodePackage` (a WIT package as a type-only component) | none |
| `wasm.module.world` | the world a core module embeds | `Wit.Binary.extractWorldType` (the `component-type` custom section) | none |

`wit` defaults to `wit.text`. A `wit.binary` value has no printer here: `encodePackage` needs
the interfaces the binary uses (`decodeEnv`), which the value type does not carry.

Laws (`Silmaril.Project.Formats.Wit.Thms`): `wit.package` is `sound` for "the text is a valid
WIT universe, and the result is a valid package with distinct names, named after the main
package" (`elaborate_sound`); `wit.binary` is `sound` for "a component of the grammar whose
sections decode to the package"; `wasm.module.world` is `sound` for "the module's only
`component-type` section is a component of the grammar that decodes to the world".
`wit.text` has no grammar relation (its parser is the specification); its laws are
conditional round trips.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm

/-- WIT text (UTF-8) to a surface document. -/
def witText : Format blob Wit.Document where
  parse b := (String.fromUTF8? b.data).bind Wit.Text.parse
  print := some fun d => some ⟨(Wit.Text.print d).toUTF8⟩

/-- The elaboration of the main package of a WIT document against the document's packages
(no feature gates enabled). -/
def elabDocument (d : Wit.Document) : Option (Wit.Binary.Package × Wit.Binary.Env) :=
  match Wit.Elab.elaborate d.packages d.main.name [] with
  | .ok r => some r
  | .error _ => none

/-- WIT text to the resolved binary model of its main package. -/
def witPackage : Format blob (Wit.Binary.Package × Wit.Binary.Env) :=
  witText.andThen elabDocument

/-- The specification relation of `wit.package`. -/
def WitPackageRel (b : Silmaril.Formats.Bytes) (r : Wit.Binary.Package × Wit.Binary.Env) : Prop :=
  ∃ d, witText.parse b = some d ∧ Wit.Valid (Wit.Universe.gate [] d.packages) ∧
    r.1.Valid r.2 ∧ r.1.NamesUnique ∧ r.1.name = Wit.Elab.pkgName d.main.name

/-- A WIT package binary (the type-only component wit-component writes) to its package. -/
def witBinary : Format blob Wit.Binary.Package where
  parse b := match Wit.Binary.decodePackage b.data with
    | .ok p => some p
    | .error _ => none

/-- The specification relation of `wit.binary`. -/
def WitBinaryRel (b : Silmaril.Formats.Bytes) (p : Wit.Binary.Package) : Prop :=
  ∃ c, ComponentRel b c ∧ Wit.Binary.decodeSections c.sections = .ok p

/-- The world embedded in a core module, with its package, name and string encoding. -/
abbrev EmbeddedWorld :=
  Wit.Binary.PackageName × String × Wit.Binary.World × Wit.Binary.StringEncoding

/-- A core module to the world it embeds (its `component-type` custom section). -/
def wasmModuleWorld : Format blob EmbeddedWorld where
  parse b := match Wit.Binary.extractWorldType b.data with
    | .ok w => some w
    | .error _ => none

/-- The specification relation of `wasm.module.world`. -/
def ModuleWorldRel (b : Silmaril.Formats.Bytes) (w : EmbeddedWorld) : Prop :=
  ∃ payload c, Wit.Binary.extractPayload b.data = .ok payload ∧ ComponentRel ⟨payload⟩ c ∧
    Wit.Binary.decodeWorldTypeSections c.sections = .ok w

end Silmaril.Project.Formats

silmaril format wit.text := Silmaril.Project.Formats.witText
  (doc := "WIT text (UTF-8) to the surface document (Wit.Text.parse, verified lexer and parser); printer Wit.Text.print")
silmaril format wit.package := Silmaril.Project.Formats.witPackage
  (base := wit.text)
  (doc := "WIT text to the resolved binary model of its main package (Wit.Elab.elaborate, no gates enabled)")
silmaril format wit.binary := Silmaril.Project.Formats.witBinary
  (doc := "WIT package binary (type-only component) to its package (Wit.Binary.decodePackage)")
silmaril format_default wit := wit.text
silmaril format wasm.module.world := Silmaril.Project.Formats.wasmModuleWorld
  (doc := "Core module to the world its component-type custom section embeds (Wit.Binary.extractWorldType)")
