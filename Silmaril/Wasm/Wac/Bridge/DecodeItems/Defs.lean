module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs

/-!
# WAC bridge: WIT packages of several items

`Bridge.DecodeNamed.decodePkg_world` reads the binary of the WIT package of *one* world
back. A WIT package in general (`Wit.Project.itemsPackage`, wit-component's layout) has
several items, each an interface or a world: item `k` is the type `2 k`, a component
type that exports the interface (an instance type) or the world (a component type) under
its identifier, exported under the item's name as the type `2 k + 1`.

* `PItem`: an item of such a package, an interface `iface id es` or a world
  `world id is es`, over items of the named fragment (`PItem.Ok`);
* `itemDef N it`: its wrapper component type as the WAC encoder writes it, the body of
  `ifaceDef` and `worldDef` (an interface's exports in an instance scope, a world's
  imports and exports in a component scope without sharing, both with nominal table
  `N`); `itemsDefs` for a list;
* `PItem.kind`, `itemsPkg`: what `decodePkg` should read back, the package whose
  definitions are the items, by the name after `/` (`defName`), as `.inst (some id) …`
  and `.comp (some id) …` (`unwrapDef`).

The theorems are in `Bridge.DecodeItems.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeNamed (EsOk extend dks)

namespace DecodeItems

/-- An item of a WIT package: an interface or a world, with its identifier. -/
inductive PItem where
  | iface (id : String) (es : Externs)
  | world (id : String) (is es : Externs)

/-- The items of the fragment `DecodeNamed.EsOk`, closed (the encoder starts a fresh
scope for an interface or a world). -/
def PItem.Ok (N : NomTable) : PItem → Prop
  | .iface _ es => EsOk N [] es
  | .world _ is es => EsOk N [] is ∧ EsOk N (extend [] is) es

/-- **An item's wrapper component type**, as the encoder writes it (`ifaceDef`,
`worldDef`). -/
def itemDef (N : NomTable) : PItem → Except String DefType
  | .iface id es => do
    let ds ← (nested false (exportDecls es)).run' { nom := N }
    pure (.component [.inst (.type (.instance (instDecls ds))), .inst (.export ⟨id, .plain0⟩ (.instance 0))])
  | .world id is es => do
    let ds ← (nested false (do importDecls is; exportDecls es)).run' { nom := N }
    pure (.component [.inst (.type (.component ds)), .inst (.export ⟨id, .plain0⟩ (.component 0))])

/-- The wrapper component types of a list of named items. -/
def itemsDefs (N : NomTable) : List (String × PItem) → Except String (List (String × DefType))
  | [] => pure []
  | (n, it) :: rest => do
    let d ← itemDef N it
    let ds ← itemsDefs N rest
    pure ((n, d) :: ds)

/-- The kind `decodePkg` reads an item back as. -/
def PItem.kind : PItem → Kind
  | .iface id es => .inst (some id) (dks es)
  | .world id is es => .comp (some id) (dks is) (dks es)

/-- The package `decodePkg` reads a WIT package of named items back as. -/
def itemsPkg (items : List (String × PItem)) : PkgType :=
  { imports := [], exports := [], defs := items.map fun p => (defName p.1, .type p.2.kind) }

end DecodeItems

end Silmaril.Wasm.Wac.Bridge
