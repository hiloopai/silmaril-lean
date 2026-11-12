module

public import Silmaril.Wasm.Component.IR.Defs

/-!
# Adapter fusion: the transformation

`fuseChain` rewrites a chain of canonical-ABI adapters, left to right:

* `lower ft, lift ft` ↦ `canon ft` — a core function calling, through a
  component-level function, another core function of the same interface type
  becomes a direct core-to-core call with canonicalisation;
* `lift ft, lower ft` ↦ `check ft` — a component function implemented by a
  round trip through core values becomes a type check;
* `check ft, lift ft` ↦ `lift ft` and `lower ft, check ft` ↦ `lower ft` —
  redundant checks;
* `canon ft` ↦ `flatCheck` when all the types of `ft` are trivially
  represented (32/64-bit integers, floats, records of these).

These patterns arise when components are linked: the `canon lower` of the
consumer component and the `canon lift` of the provider component become
adjacent after flattening (`Silmaril.Wasm.Component.Passes.Flatten`).
`fuseComponent` applies `fuseChain` to every wiring program, at every nesting
depth.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

/-- Rewrite a chain of adapters (see the module documentation). -/
def fuseChain : List Adapter → List Adapter
  | .lower ft :: .lift ft' :: c =>
    if ft = ft' then fuseChain (.canon ft :: c) else .lower ft :: fuseChain (.lift ft' :: c)
  | .lift ft :: .lower ft' :: c =>
    if ft = ft' then fuseChain (.check ft :: c) else .lift ft :: fuseChain (.lower ft' :: c)
  | .check ft :: .lift ft' :: c =>
    if ft = ft' then fuseChain (.lift ft :: c) else .check ft :: fuseChain (.lift ft' :: c)
  | .lower ft :: .check ft' :: c =>
    if ft = ft' then fuseChain (.lower ft :: c) else .lower ft :: fuseChain (.check ft' :: c)
  | .canon ft :: c =>
    if ValTy.trivialList ft.params && ValTy.trivialList ft.results then
      .flatCheck ft.flat.params ft.flat.results :: fuseChain c
    else .canon ft :: fuseChain c
  | a :: c => a :: fuseChain c
  | [] => []
termination_by c => c.length

/-- Fuse the adapters of a wiring program. -/
def Impl.fuse (im : Impl) : Impl := { im with chain := fuseChain im.chain }

/-- Adapter fusion on a component (all nesting depths). -/
def fuseComponent {M : Type} (c : Comp M) : Comp M := c.mapImpls Impl.fuse

/-- Adapter fusion on a flat component. -/
def fuseLinked {M : Type} (l : Linked M) : Linked M :=
  { l with
    nodes := l.nodes.map fun n => (n.1, n.2.map Impl.fuse)
    exports := l.exports.map fun x => { x with impl := x.impl.fuse } }

end Silmaril.Wasm.Component
