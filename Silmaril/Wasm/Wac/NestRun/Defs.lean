module

public import Silmaril.Wasm.Wac.Nest.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Defs

/-!
# WAC: flattening a composition graph, node by node

The proof of nesting = inlining (`Silmaril.Wasm.Wac.NestInline.Thms`) compares the
`flattenNodes` runs of two compositions. Both are runs over package instances; this
module describes such a run without the index arithmetic of `Graph.resolve`:

* a **valuation** `V : Src → Impl` gives, for each reference of the graph, its
  implementation over the flat environment;
* `gRun P V eB k ns` flattens the instances `ns` (the first of index `k`) of packages
  `P`, over the flat environment size `eB`: the imports of an instance are its
  references under `V`, the package's nodes are flattened by `flattenNodes`, and the
  valuation is extended at the instance's exports (`extV`).

`flatten_buildWith` (in `Silmaril.Proofs.Wasm.Wac.Nest.Run`) says that flattening
`Graph.buildWith` is `gRun` from the valuation `baseV` of the imports. The two sides of
nesting = inlining are then related by a simulation between `gRun` runs (`RenOk`: the
renaming of node indices built by `Graph.inline` sends the exports of an instance of
the nested side to exports of instances of the inlined side).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

variable {M : Type}

/-- The valuation of the composition's imports `I` before any instance: an import is
forwarded to its index, everything else traps. -/
def baseV (I : Iface) : Src → Impl
  | .imp x => if x ∈ names I then .fwd ((names I).idxOf x) else .trap
  | .out _ _ => .trap

/-- The export `q` of the exports `xs`, substituted by `σ` (a trap if absent). -/
def expImpl (xs : List Export) (σ : List Impl) (q : String) : Impl :=
  ((xs.map fun x => x.impl.subst σ)[(xs.map Export.name).idxOf q]?).getD .trap

/-- Extend the valuation `V` at the exports `xs` of instance `k`. -/
def extV (V : Src → Impl) (k : Nat) (xs : List Export) (σ : List Impl) : Src → Impl
  | .imp x => V (.imp x)
  | .out j q => if j = k ∧ q ∈ xs.map Export.name then expImpl xs σ q else V (.out j q)

variable [CoreModule M]

/-- Flatten the instances `ns` (from index `k`) of the packages `P`, over the valuation
`V` and the flat environment size `eB`: the final valuation, environment size and flat
nodes. -/
def gRun (P : Nat → Comp M) :
    (Src → Impl) → Nat → Nat → List Inst → (Src → Impl) × Nat × List (M × List Impl)
  | V, eB, _, [] => (V, eB, [])
  | V, eB, k, n :: ns =>
    let rc := flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes
    let r := gRun P (extV V k (P n.pkg).exports rc.1) rc.2.1 (k + 1) ns
    (r.1, r.2.1, rc.2.2 ++ r.2.2)

/-- The renaming built by inlining, after the first `j` instances of `g₂`, sends every
export `q` of an earlier instance `j'` of `g₂` to an export `q'` of a node `t` of the
inlined graph, of the same type (`S` the package interfaces, `S'` those of the nested
side). -/
def RenOk (S S' : Nat → PkgSig) (g₂ : Graph) (acc : IAcc) (j : Nat) : Prop :=
  acc.ren.length = j ∧
    ∀ j' n q, g₂.nodes[j']? = some n → j' < j → q ∈ names (S' n.pkg).exports →
      ∃ t q' m, renSrc acc.ren (.out j' q) = .out t q' ∧ acc.nodes[t]? = some m ∧
        q' ∈ names (S m.pkg).exports ∧ (S m.pkg).exports.lookup q' = (S' n.pkg).exports.lookup q

/-- The simulation between the nested run (valuation `V`, over the first `j` instances of
`g₂`) and the inlined run (valuation `U`, over the inlined nodes of `acc`): the renaming
is `RenOk`, the imports agree, and every export of an earlier instance has, under `V`,
the value of its renaming under `U`. -/
def SimV (S S' : Nat → PkgSig) (g₂ : Graph) (j : Nat) (acc : IAcc) (V U : Src → Impl) : Prop :=
  RenOk S S' g₂ acc j ∧ (∀ x, V (.imp x) = U (.imp x)) ∧
    ∀ j' n q, g₂.nodes[j']? = some n → j' < j → q ∈ names (S' n.pkg).exports →
      V (.out j' q) = U (renSrc acc.ren (.out j' q))

/-- The lookup in an interface, as a function. -/
def lookupIn (I : Iface) (x : String) : Option FuncTy := I.lookup x

/-- Every entry of `L` has the type `T` gives its name. -/
def TyCons (T : String → Option FuncTy) (L : Iface) : Prop := ∀ p ∈ L, T p.1 = some p.2

/-- The invariant of the imports along inlining: the renaming is `RenOk`, and the imports
used by the inlined nodes so far have the names of those used by the first `j` instances
of `g₂`, with the types `T`. -/
def UsesInv (S S' : Nat → PkgSig) (g₂ : Graph) (T : String → Option FuncTy) (acc : IAcc)
    (j : Nat) : Prop :=
  RenOk S S' g₂ acc j ∧ TyCons T (acc.nodes.flatMap (Inst.uses S)) ∧
    ∀ y, y ∈ names (acc.nodes.flatMap (Inst.uses S)) ↔
      y ∈ names ((g₂.nodes.take j).flatMap (Inst.uses S'))

end Silmaril.Wasm.Wac
