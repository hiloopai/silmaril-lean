module

public import Silmaril.Wasm.Wac.Nest.Defs
public import Silmaril.Wasm.Wac.NestOrder.Defs

/-!
# WAC: unused imports are promotion

A composition graph can declare an import that no instance and no export uses (a declared
but unused import; nesting = inlining excludes it, `Wac.NestOk.used`, because inlining loses
it). Its component still lists it among its imports. In the algebra it is **promotion**
(`Algebra.reimport`): the component over the imports `I` is the component over a smaller
list `J`, containing every import the graph refers to, with its imports re-read by name in
`I` (`Algebra.byName I J`).

* `Graph.RefsIn S g U`: every reference of `g` to an import, from an instance or an export,
  names an import in `U`.

Theorems in `Silmaril.Wasm.Wac.Unused.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

/-- Every reference of the graph to an import names one of `U`. -/
def Graph.RefsIn (S : Nat → PkgSig) (g : Graph) (U : List String) : Prop :=
  (∀ n ∈ g.nodes, ∀ p ∈ (S n.pkg).imports, ∀ x, n.src p.1 = .imp x → x ∈ U) ∧
    ∀ p ∈ g.exports, ∀ x, p.2 = .imp x → x ∈ U

end Silmaril.Wasm.Wac
