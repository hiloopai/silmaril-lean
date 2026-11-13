module

public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeRefVal.Defs

/-!
# WAC bridge: WIT packages of several items over the fragment `EsOkR`

`Bridge.DecodeItems` reads WIT packages of interfaces and worlds (`DecodeItems.PItem`,
`Wit.Project.itemsPackage`) back, for items of `DecodeNamed.EsOk`. This module states
the same for items of `DecodeRefVal.EsOkR` (resources used as `ref a`, aliases as
`own<a>`, alias type items of resources and aliases written either way, value items,
at every level), read back up to `DecodeRefVal.rdEs`:

* `okR N`: an interface's items, or a world's imports and exports, in `EsOkR`;
* `kindR`, `itemsPkgR`: what `decodePkg` reads back.

The theorems are in `Bridge.DecodeItemsR.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeNamed (dks)
open DecodeRefVal (EsOkR rdEs extendR)
open DecodeItems (PItem)

namespace DecodeItemsR

/-- The items of the fragment `EsOkR`, closed. -/
def okR (N : NomTable) : PItem → Prop
  | .iface _ es => EsOkR N [] es
  | .world _ is es => EsOkR N [] is ∧ EsOkR N (extendR [] is) es

/-- The kind `decodePkg` reads an item back as. -/
def kindR : PItem → Kind
  | .iface id es => .inst (some id) (dks (rdEs [] es))
  | .world id is es => .comp (some id) (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es))

/-- The package `decodePkg` reads a WIT package of named items back as. -/
def itemsPkgR (items : List (String × PItem)) : PkgType :=
  { imports := [], exports := [], defs := items.map fun p => (defName p.1, .type (kindR p.2)) }

end DecodeItemsR

end Silmaril.Wasm.Wac.Bridge
