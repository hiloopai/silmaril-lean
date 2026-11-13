module

public import Silmaril.Games.InstFacade.Defs
public import Silmaril.Logic.Inst.Graph.Defs

/-!
# The logic graph of the game institutions

The three game institutions and the two identity-on-signatures comorphisms between them, as a
Hets logic graph presented with the facade's typed builder `Silmaril.Inst.GraphSpec`:

```
GInstRef --toGInst--> GInst --toDGInst--> DGInst
```

* `Node`: `ref`, `plain`, `div`; `inst : Node → Institution₁`.
* `spec : GraphSpec inst`: the edge list `[⟨ref, plain, GInstRef.toGInst⟩,
  ⟨plain, div, GInst.toDGInst⟩]`, each edge type checked against its endpoints; no morphism
  edges.
* `graph : LogicGraph.{0, 0, 1, 0, 0, 0, 0}` is `spec.toLogicGraph`.
* `Edge` names the two edges: `Edge.idx e` is the graph edge of `e`, and `comor_idx` says it acts
  by `comor e`, so paths are written `(Quiver.Path.nil.cons Edge.toGInst.idx).cons …`.
* `allModelExpansive`, `pathModelExpansive`: both edges are model-expansive
  (`GInstRef.toGInst_modelExpansive`, `GInst.toDGInst_modelExpansive`), so every path is
  (`GraphSpec.pathModelExpansive`), and heterogeneous borrowing
  (`LogicGraph.entails_lift_path_iff`) applies along every path.

The graph has the universe levels of the Wasm graphs (`Silmaril.Wasm.Institution.CompGraph`), so it
can be combined with them (`Silmaril.Wasm.Institution.CompGameGraph`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Games.InstGraph

open CategoryTheory Silmaril.Logic.Institution Silmaril.Inst

/-- The nodes: `GInstRef`, `GInst` and `DGInst`. -/
inductive Node : Type
  | ref
  | plain
  | div
  deriving DecidableEq

/-- The institution of a node. -/
def inst : Node → Institution₁
  | .ref => GInstRef
  | .plain => GInst
  | .div => DGInst

/-- **The game institutions as a typed edge list.** -/
def spec : GraphSpec inst where
  comors := [⟨.ref, .plain, GInstRef.toGInst⟩, ⟨.plain, .div, GInst.toDGInst⟩]

/-- **The logic graph of the game institutions.** -/
abbrev graph : LogicGraph.{0, 0, 1, 0, 0, 0, 0} := spec.toLogicGraph

/-- Names for the comorphism edges. -/
inductive Edge : Node → Node → Type
  | toGInst : Edge .ref .plain
  | toDGInst : Edge .plain .div

/-- The comorphism of a named edge. -/
def comor : {a b : Node} → Edge a b → Comorphism (inst a) (inst b)
  | _, _, .toGInst => GInstRef.toGInst
  | _, _, .toDGInst => GInst.toDGInst

/-- The graph edge of a named edge. -/
def Edge.idx : {a b : Node} → Edge a b → graph.Comor a b
  | _, _, .toGInst => spec.coEdge ⟨0, by decide⟩
  | _, _, .toDGInst => spec.coEdge ⟨1, by decide⟩

/-- A named edge acts by its comorphism. -/
@[simp] theorem comor_idx {a b : Node} (e : Edge a b) : graph.comor e.idx = comor e := by
  cases e <;> rfl

/-- Every named edge is model-expansive. -/
theorem edge_modelExpansive : ∀ {a b : Node} (e : Edge a b), (comor e).ModelExpansive
  | _, _, .toGInst => GInstRef.toGInst_modelExpansive
  | _, _, .toDGInst => GInst.toDGInst_modelExpansive

/-- Every listed edge is model-expansive. -/
theorem allModelExpansive : spec.AllModelExpansive := by
  intro e he
  simp only [spec, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact GInstRef.toGInst_modelExpansive
  · exact GInst.toDGInst_modelExpansive

/-- **Every path of the game graph is model-expansive.** -/
theorem pathModelExpansive {a b : graph.Idx} (p : Quiver.Path a b) : graph.PathModelExpansive p :=
  spec.pathModelExpansive allModelExpansive p

end Silmaril.Games.InstGraph
