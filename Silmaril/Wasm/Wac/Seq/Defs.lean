module

public import Silmaril.Wasm.Wac.Graph.Defs

/-!
# WAC: sequential composition of composition graphs (plugging)

`Graph.seq S g₁ g₂` puts the composition `g₂` after `g₁` and satisfies the imports of
`g₂` by the exports of `g₁`, by name (`wac plug`: the exports of a plug satisfy the
imports of the socket of the same name):

* the instances are those of `g₁`, then those of `g₂` with **every argument made
  explicit** (`Graph.explicate`: an unsatisfied import `q` becomes the reference
  `imp q`), renumbered after `g₁` and with every `imp x` replaced by the export `x` of
  `g₁` when there is one (`Graph.plugSrc`);
* the exports are those of `g₂` (substituted), then those of `g₁` (an export of `g₂`
  shadows one of `g₁`, `List.lookup` takes the first);
* the declared imports are those of `g₁`, then those of `g₂` that `g₁` does not export.

Imports of `g₂` that `g₁` does not export stay imports (**promotion**); imports of the
same name are merged by `Graph.iface`. `Silmaril.Wasm.Wac.Seq.Thms` proves that `seq` is
**associative**, syntactically (hence so are the composed components).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-- The substitution of `g₁` into a reference of `g₂`: an import is replaced by the export
of `g₁` of the same name, if any; an instance is renumbered after the instances of `g₁`. -/
def Graph.plugSrc (g₁ : Graph) : Src → Src
  | .imp x => (g₁.exports.lookup x).getD (.imp x)
  | .out k q => .out (k + g₁.nodes.length) q

/-- Substitute in the arguments of an instance. -/
def Inst.mapSrc (f : Src → Src) (n : Inst) : Inst :=
  { n with args := n.args.map fun a => (a.1, f a.2) }

/-- **Sequential composition** (plugging `g₁` into `g₂`). -/
def Graph.seq (S : Nat → PkgSig) (g₁ g₂ : Graph) : Graph where
  imports := g₁.imports ++ g₂.imports.filter fun p => (g₁.exports.lookup p.1).isNone
  nodes := g₁.nodes ++ (g₂.explicate S).nodes.map (Inst.mapSrc g₁.plugSrc)
  exports := g₂.exports.map (fun a => (a.1, g₁.plugSrc a.2)) ++ g₁.exports

end Silmaril.Wasm.Wac
