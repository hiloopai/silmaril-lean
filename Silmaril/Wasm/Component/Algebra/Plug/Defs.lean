module

public import Silmaril.Wasm.Component.Algebra.Ops.Defs
public import Silmaril.Wasm.Wac.Seq.Defs

/-!
# Plugging by name and positional plugging: definitions

`wac plug` plugs the exports of a *plug* package into the imports of a *socket* package **by
name** (`Silmaril.Wasm.Wac.Graph.seq`); the algebra's `seq c₁ c₂` plugs **by position**. To
compare them:

* `pkgGraph k E`: the composition graph with one instance of package `k` that exports the
  functions `E` of its interface by name.
* `plugGraph S`: `wac plug` of the socket (package `1`) by the plug (package `0`), as WAC builds
  it: `Graph.seq S (pkgGraph 0 …) (pkgGraph 1 …)`.
* `byName E I`: the positional wiring that the names give: import `p` of `I` reads the function
  of `E` with the name of `p` (the first one, as `List.lookup` does).

Theorems in `Silmaril.Wasm.Component.Algebra.Plug.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

/-- One instance of package `k`, exporting the functions `E` by name. -/
def pkgGraph (k : Nat) (E : Iface) : Graph :=
  { nodes := [⟨k, []⟩], exports := E.map fun p => (p.1, .out 0 p.1) }

/-- **`wac plug`**: the socket (package `1`) plugged by the plug (package `0`), by name. -/
def plugGraph (S : Nat → PkgSig) : Graph :=
  Graph.seq S (pkgGraph 0 (S 0).exports) (pkgGraph 1 (S 1).exports)

/-- The positional wiring given by names: import `p` of `I` reads the first function of `E`
named like `p`. -/
def byName (E I : Iface) : List Nat := I.map fun p => (names E).idxOf p.1

end Silmaril.Wasm.Component.Algebra
