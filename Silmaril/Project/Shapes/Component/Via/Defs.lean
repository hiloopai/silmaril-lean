module

public import Silmaril.Project.Shapes.Component.Defs
public import Silmaril.Project.Components.SemVer.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

/-!
# Standard problem shapes: WASI versions and upgrades of components

Shapes relating WASI versions (`Silmaril.Wasi.Versions`, `docs/projects/wasm-wasi.md`) and releases of
one package, in the family `silmaril.shapes.component.*`:

| name | Lean | statement |
|---|---|---|
| `silmaril.shapes.component.implements_via` | `ImplementsVia σ A B` | linked over **every** host of the theory `B` (its imports), `σ` is a host of the theory `A` (its exports) |
| `silmaril.shapes.component.imports_via` | `ImportsVia X M ns v L` | the module's embedded world (`wasm.module.world`) imports only `ns` interfaces compatible with `v`, among them those of the functions `L`; its core imports (`wasm.module`) resolve to the world's interfaces at compatible versions that do not precede theirs, and include each function of `L` |
| `silmaril.shapes.component.release_implements_via` | `ReleaseImplementsVia X M ns v L σ A B` | `ImportsVia X M ns v L` and `ImplementsVia σ A B`, for a model `σ` importing exactly `L` |
| `silmaril.shapes.component.wit_upgrade` | `WitUpgrade X₁ X₂` | two WIT package releases: one package, `X₂`'s version a compatible upgrade of `X₁`'s, and every type and function of every interface of `X₁` is in the same interface of `X₂` |

**Implementation morphisms.** `ImplementsVia σ A B` is the relation of `docs/projects/wasm-wasi.md`:
`σ` imports world B and exports world A, and for every host model `η` of B's theory (over any
lower interface) the composite `link η σ` is a host model of A's theory. The preview1 adapter
slice is such a `σ` (`Silmaril.Wasi.Versions.Adapter.adapter_model`). It is a sentence about a
*model* of the component, not about its bytes.

**Binary interface.** `ImportsVia` is what the bytes of a core module say about the WASI
versions it uses. An interface `ns:pkg/iface` is named without its version in
`Silmaril.Wasi` (`FnName.iface`), so the version lives only in the binary: the embedded world names
`ns:pkg/iface@version` (`Wit.Binary.IfaceName`), the core imports name modules
`ns:pkg/iface@version`. A core import resolves when the world imports the same interface at a
compatible version that does not precede it (`SemVer.Upgrade`, the rule by which wit-component
matches an import of `@0.2.6` to a world's `@0.2.12`).

`ReleaseImplementsVia` puts the two together for a release whose behaviour is given by a
hand-written model `σ` (a transcription of its source): it does **not** say that `σ` is the
semantics of the bytes. What ties `σ` to the bytes is only that `σ`'s imports are among the
binary's imports, on the version track `v`.

**WIT upgrades.** A WIT package (a type-only component) has no behaviour, so the semantic
`upgrade_compatible` does not apply to it; `wit_upgrade` is the interface-level condition.
Definitions are compared after `PackageSummary` drops docs, stability gates and the versions of
the packages that type references name (they change with every release of a package).
`PackageSummary` keeps the interfaces only, not the worlds.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Components.SemVer
open Silmaril.Wasm (Wit.Version)

/-! ## Implements a WASI version via another -/

/-- **`σ` implements the theory `A` via the theory `B`**: linked over any host `η` (any lower
interface `Y`) whose answers satisfy `B`, the composite's answers satisfy `A`. -/
@[problem "silmaril.shapes.component.implements_via"
  (title := "A component implements one WASI version via another")]
def ImplementsVia {I X : Set FnName} {SA SB : Type} (σ : Strategy (nsig I) (nsig X))
    (A : Protocol SA WEv) (B : Protocol SB WEv) : Prop :=
  ∀ (Y : Sig.{0}) (η : Host Y I), (hostSat B.Accepts).holds η → (hostSat A.Accepts).holds (link η σ)

/-! ## Interface names and versions in a binary -/

/-- The name `ns:pkg/iface` of an interface without its version, as `FnName.iface`. -/
def ifaceKey (i : Silmaril.Wasm.Wit.Binary.IfaceName) : String :=
  i.pkg.ns ++ ":" ++ i.pkg.name ++ "/" ++ i.name

/-- An interface without its version: `(ns, pkg, iface)`. -/
abbrev IfaceId : Type := String × String × String

/-- The interface of a name, without its version. -/
def ifaceId (i : Silmaril.Wasm.Wit.Binary.IfaceName) : IfaceId := (i.pkg.ns, i.pkg.name, i.name)

/-- `ns:pkg/iface` (the form of `FnName.iface`), parsed. -/
def ifaceId? (s : String) : Option IfaceId :=
  match Silmaril.Wasm.Wit.Text.Parse.splitFirst ':' s.toList with
  | (_, none) => none
  | (ns, some rest) =>
    match Silmaril.Wasm.Wit.Text.Parse.splitFirst '/' rest with
    | (_, none) => none
    | (pkg, some iface) => some (String.ofList ns, String.ofList pkg, String.ofList iface)

/-- The interfaces a world imports by reference. -/
def worldIfaces (w : Silmaril.Wasm.Wit.Binary.World) : List Silmaril.Wasm.Wit.Binary.IfaceName :=
  w.imports.filterMap fun
    | .ifaceRef i _ _ => some i
    | _ => none

/-- The interface of a core import module name `ns:pkg/iface@version` (or without version);
`none` for other module names (`env`, `__main_module__`). -/
def coreIface? (m : String) : Option Silmaril.Wasm.Wit.Binary.IfaceName :=
  match Silmaril.Wasm.Wit.Text.Parse.splitFirst ':' m.toList with
  | (_, none) => none
  | (ns, some rest) =>
    match Silmaril.Wasm.Wit.Text.Parse.splitFirst '/' rest with
    | (_, none) => none
    | (pkg, some r) =>
      match Silmaril.Wasm.Wit.Text.Parse.splitFirst '@' r with
      | (iface, v) => some ⟨⟨String.ofList ns, String.ofList pkg, v.map String.ofList⟩,
          String.ofList iface⟩

/-- A core import, read: the interface its module names (if any) and its name. -/
abbrev CoreImport : Type := Option Silmaril.Wasm.Wit.Binary.IfaceName × String

/-- The imports of a core module, read. -/
def coreImports (m : Silmaril.Wasm.Module) : List CoreImport :=
  m.imports.map fun i => (coreIface? i.moduleName, i.name)

/-- Every import of the world is an interface of the namespace `ns` at a version compatible
with `v`. -/
def onTrackB (w : Silmaril.Wasm.Wit.Binary.World) (ns : String) (v : Wit.Version) : Bool :=
  w.imports.all fun
    | .ifaceRef i _ _ => i.pkg.ns == ns && (match binVersion? i.pkg with
      | some u => decide (Compatible u v)
      | none => false)
    | _ => false

/-- The world imports the interface of every function of `L`. -/
def coversB (w : Silmaril.Wasm.Wit.Binary.World) (L : List FnName) : Bool :=
  L.all fun f => match ifaceId? f.iface with
    | none => false
    | some k => (worldIfaces w).any fun i => ifaceId i == k

/-- A core import resolves in the world: an interface import is matched by a world import of
the same interface whose version is a compatible upgrade of the import's. -/
def resolvesB (w : Silmaril.Wasm.Wit.Binary.World) : Option Silmaril.Wasm.Wit.Binary.IfaceName → Bool
  | none => true
  | some i => (worldIfaces w).any fun j => ifaceId j == ifaceId i &&
      (match binVersion? i.pkg, binVersion? j.pkg with
        | some u, some u' => decide (Upgrade u u')
        | _, _ => false)

/-- Every function of `L` is a core import: of a module naming its interface (at some
version), with its name. -/
def sliceInB (imps : List CoreImport) (L : List FnName) : Bool :=
  L.all fun f => match ifaceId? f.iface with
    | none => false
    | some k => imps.any fun p => p.2 == f.fn && p.1.map ifaceId == some k

/-- The binary conditions of `ImportsVia` on a world and the core imports. -/
def ViaOk (w : Silmaril.Project.Formats.EmbeddedWorld) (imps : List CoreImport) (ns : String)
    (v : Wit.Version) (L : List FnName) : Prop :=
  onTrackB w.2.2.1 ns v = true ∧ coversB w.2.2.1 L = true ∧
    imps.all (fun p => resolvesB w.2.2.1 p.1) = true ∧ sliceInB imps L = true

instance (w : Silmaril.Project.Formats.EmbeddedWorld) (imps : List CoreImport) (ns : String)
    (v : Wit.Version) (L : List FnName) : Decidable (ViaOk w imps ns v L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- **The module's WASI imports are on the version track `v`** (see the module docstring). -/
@[problem "silmaril.shapes.component.imports_via"
  (title := "A core module's WASI imports are on one version track")]
def ImportsVia (X : Value Silmaril.Project.Formats.EmbeddedWorld) (M : Value Silmaril.Wasm.Module)
    (ns : String) (v : Wit.Version) (L : List FnName) : Prop :=
  X.Satisfies fun w => M.Satisfies fun m => ViaOk w (coreImports m) ns v L

/-- **A release implements the theory `A` via `B` on the version track `v`**: its binary imports
are on the track (`ImportsVia`), and the model `σ`, importing exactly the functions `L`,
implements `A` via `B`. -/
@[problem "silmaril.shapes.component.release_implements_via"
  (title := "A component release implements one WASI version via another version track")]
def ReleaseImplementsVia {X' : Set FnName} {SA SB : Type}
    (X : Value Silmaril.Project.Formats.EmbeddedWorld) (M : Value Silmaril.Wasm.Module)
    (ns : String) (v : Wit.Version) (L : List FnName) (σ : Strategy (nsig {f | f ∈ L}) (nsig X'))
    (A : Protocol SA WEv) (B : Protocol SB WEv) : Prop :=
  ImportsVia X M ns v L ∧ ImplementsVia σ A B

/-! ## WIT package upgrades -/

open Silmaril.Wasm.Wit.Binary in
/-- A type reference without the version of the package it names. -/
def TyRef.unver (r : TyRef) : TyRef :=
  match r.owner with
  | .local => r
  | .iface i => ⟨.iface ⟨{ i.pkg with version := none }, i.name⟩, r.name⟩

open Silmaril.Wasm.Wit.Binary in
mutual
/-- A type without the versions of referenced packages. -/
def Ty.unver : Ty → Ty
  | .prim p => .prim p
  | .ref r => .ref (TyRef.unver r)
  | .list t => .list (Ty.unver t)
  | .fixedList t n => .fixedList (Ty.unver t) n
  | .map k v => .map (Ty.unver k) (Ty.unver v)
  | .option t => .option (Ty.unver t)
  | .result a b => .result (Ty.unverOpt a) (Ty.unverOpt b)
  | .tuple ts => .tuple (Ty.unverList ts)
  | .own r => .own (TyRef.unver r)
  | .borrow r => .borrow (TyRef.unver r)
  | .future t => .future (Ty.unverOpt t)
  | .stream t => .stream (Ty.unverOpt t)
/-- `Ty.unver` on an optional type. -/
def Ty.unverOpt : Option Ty → Option Ty
  | none => none
  | some t => some (Ty.unver t)
/-- `Ty.unver` on a list. -/
def Ty.unverList : List Ty → List Ty
  | [] => []
  | t :: ts => Ty.unver t :: Ty.unverList ts
end

open Silmaril.Wasm.Wit.Binary in
/-- A type definition's kind without docs and versions of references. -/
def kindSummary : TyDefKind → TyDefKind
  | .record fs => .record (fs.map fun f => { name := f.name, ty := Ty.unver f.ty })
  | .variant cs => .variant (cs.map fun c => { name := c.name, ty := Ty.unverOpt c.ty })
  | .enum cs => .enum (cs.map fun c => { name := c.name, ty := () })
  | .flags fs => .flags (fs.map fun f => { name := f.name, ty := () })
  | .resource => .resource
  | .type t => .type (Ty.unver t)

open Silmaril.Wasm.Wit.Binary in
/-- A function's name, kind and signature without versions of references. -/
def funcSummary (f : Func) : String × FuncKind × Silmaril.Wasm.Wit.Binary.Sig :=
  (f.name, f.kind, ⟨f.async, f.params.map fun p => (p.1, Ty.unver p.2), Ty.unverOpt f.result⟩)

/-- The named types and the functions of an interface. -/
abbrev IfaceBody : Type :=
  List (String × Silmaril.Wasm.Wit.Binary.TyDefKind) ×
    List (String × Silmaril.Wasm.Wit.Binary.FuncKind × Silmaril.Wasm.Wit.Binary.Sig)

/-- The summary of an interface: its name, its named types and its functions. -/
abbrev IfaceSummary : Type := String × IfaceBody

/-- The summary of a package: its name and its interfaces (docs, gates, worlds dropped). -/
abbrev PackageSummary : Type := Silmaril.Wasm.Wit.Binary.PackageName × List IfaceSummary

-- the instance search does not find these through the nested products by itself
instance : DecidableEq IfaceBody := inferInstance
instance : DecidableEq IfaceSummary := inferInstanceAs (DecidableEq (String × IfaceBody))
instance : DecidableEq PackageSummary :=
  inferInstanceAs (DecidableEq (Silmaril.Wasm.Wit.Binary.PackageName × List IfaceSummary))

/-- The summary of a WIT package. -/
def summary (p : Silmaril.Wasm.Wit.Binary.Package) : PackageSummary :=
  (p.name, p.interfaces.map fun (n, i) =>
    (n, i.types.map (fun t => (t.name, kindSummary t.kind)), i.funcs.map funcSummary))

/-- **`s₂` is an upgrade of `s₁`**: one package, a compatible version that does not precede,
and each interface of `s₁` is in `s₂` with at least its types and functions. -/
def SummaryUpgrade (s₁ s₂ : PackageSummary) : Prop :=
  s₁.1.ns = s₂.1.ns ∧ s₁.1.name = s₂.1.name ∧
    (match binVersion? s₁.1, binVersion? s₂.1 with
      | some u, some u' => Upgrade u u'
      | _, _ => False) ∧
    ∀ i ∈ s₁.2, ∃ j ∈ s₂.2, i.1 = j.1 ∧ i.2.1 ⊆ j.2.1 ∧ i.2.2 ⊆ j.2.2

instance (s₁ s₂ : PackageSummary) : Decidable (SummaryUpgrade s₁ s₂) := by
  unfold SummaryUpgrade
  cases binVersion? s₁.1 <;> cases binVersion? s₂.1 <;> infer_instance

/-- **A WIT package release is an upgrade of another** (see the module docstring). -/
@[problem "silmaril.shapes.component.wit_upgrade"
  (title := "A WIT package release is upgrade-compatible with an earlier one")]
def WitUpgrade (X₁ X₂ : Value Silmaril.Wasm.Wit.Binary.Package) : Prop :=
  X₁.Satisfies fun p₁ => X₂.Satisfies fun p₂ => SummaryUpgrade (summary p₁) (summary p₂)

end Silmaril.Project.Shapes.Component

end
