module

public import Silmaril.Logic.Inst.Graph.Defs
public import Silmaril.Logic.Institution.Hets.StructuredPaths

/-!
# Structured specifications along the paths of a `GraphSpec`

Heterogeneous structured specifications over a logic graph are structured specifications
(`Silmaril.Logic.Institution.StrSpec`: basic, union, translate, hide) over its Grothendieck
institution; `Silmaril.Logic.Institution.Hets.StructuredPaths` translates them along a path `p`
of the graph and proves borrowing when the path is model-expansive. For a graph presented by a
`GraphSpec` whose listed comorphisms are all model-expansive (`GraphSpec.AllModelExpansive`),
every path is model-expansive (`GraphSpec.pathModelExpansive`), so:

* `GraphSpec.entails_translatePath_iff`: a heterogeneous specification entails `φ` iff its
  translation along `p` entails the translated sentence;
* `GraphSpec.refines_translatePath_iff`: translation along `p` preserves and reflects
  refinement;
* `GraphSpec.models_hide_translatePath`: hiding along `p` what was translated along `p` gives
  back the model class.

The statements hold for every universe shape of the nodes; a graph mixing shapes needs its
nodes lifted to one shape first (`Silmaril.Wasi.Spec` lifts `WasiInst` with `ULift`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Inst.GraphSpec

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Hets

universe u₀ u v w m₁ m₂

variable {ι : Type u₀} {inst : ι → Institution.{u, v, w, m₁, m₂}} (G : GraphSpec inst)

/-- **Borrowing of structured entailment along a path of a `GraphSpec`**. -/
theorem entails_translatePath_iff (h : G.AllModelExpansive) {a b : ι}
    (p : Quiver.Path (V := G.toLogicGraph.Idx) a b)
    (S : (IndexedCoInst.inst G.toLogicGraph.indexed (G.toLogicGraph.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat G.toLogicGraph.indexed) (G.toLogicGraph.sigOf a S))
    (φ : ((IndexedCoInst.flat G.toLogicGraph.indexed).obj (G.toLogicGraph.sigOf a S)).Sen) :
    SP.Entails φ ↔
      (StructuredPaths.translate G.toLogicGraph p S SP).Entails
        (((IndexedCoInst.flat G.toLogicGraph.indexed).map
          (StructuredPaths.lift G.toLogicGraph p S)).sen φ) :=
  StructuredPaths.entails_iff G.toLogicGraph p (G.pathModelExpansive h p) S SP φ

/-- **Borrowing of refinement along a path of a `GraphSpec`**. -/
theorem refines_translatePath_iff (h : G.AllModelExpansive) {a b : ι}
    (p : Quiver.Path (V := G.toLogicGraph.Idx) a b)
    (S : (IndexedCoInst.inst G.toLogicGraph.indexed (G.toLogicGraph.pt a)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat G.toLogicGraph.indexed) (G.toLogicGraph.sigOf a S)) :
    SP.Refines SQ ↔
      (StructuredPaths.translate G.toLogicGraph p S SP).Refines
        (StructuredPaths.translate G.toLogicGraph p S SQ) :=
  StructuredPaths.refines_iff G.toLogicGraph p (G.pathModelExpansive h p) S SP SQ

/-- Hiding along a path of a `GraphSpec` undoes translation along it. -/
theorem models_hide_translatePath (h : G.AllModelExpansive) {a b : ι}
    (p : Quiver.Path (V := G.toLogicGraph.Idx) a b)
    (S : (IndexedCoInst.inst G.toLogicGraph.indexed (G.toLogicGraph.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat G.toLogicGraph.indexed) (G.toLogicGraph.sigOf a S)) :
    (StructuredPaths.hide G.toLogicGraph p S
      (StructuredPaths.translate G.toLogicGraph p S SP)).models = SP.models :=
  StructuredPaths.models_hide_translate G.toLogicGraph p (G.pathModelExpansive h p) S SP

end Silmaril.Inst.GraphSpec
