module

public import Silmaril.Wasm.Wac.Graph.Defs

/-!
# WAC statement shapes as operators on composition graphs

The statements of a WAC document that do not instantiate a package act on the exports of the
composition graph. This module names them as graph operators, so that
`Silmaril.Wasm.Component.Algebra.WacShapes.Thms` can give each its algebra operator:

* `Graph.renameExps f g`: every export `n` of `g` is exported as `f n` (`export e as n`, and
  the `x#f` naming of `export i...`);
* `Graph.keepExps keep g`: the exports of indices `keep`, in that order (a document exports
  only what it names; hiding).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-- Rename every export of a graph. -/
def Graph.renameExps (f : String → String) (g : Graph) : Graph :=
  { g with exports := g.exports.map fun p => (f p.1, p.2) }

/-- Keep the exports of indices `keep`, in that order (indices out of range are dropped). -/
def Graph.keepExps (keep : List Nat) (g : Graph) : Graph :=
  { g with exports := keep.filterMap fun j => g.exports[j]? }

end Silmaril.Wasm.Wac
