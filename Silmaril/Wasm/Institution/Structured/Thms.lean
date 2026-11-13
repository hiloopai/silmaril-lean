module

public import Silmaril.Logic.Inst.Graph.Thms
public import Silmaril.Wasm.Institution.CompGameGraph.Defs
public import Silmaril.Wasm.Institution.DivGames.Spec.Defs
public import Silmaril.Wasm.Institution.Api.Defs

/-!
# Heterogeneous structured specifications over the Wasm logic graphs

Hets' heterogeneous specification is structured specification over the Grothendieck
institution of a logic graph (`Silmaril.Logic.Institution.Hets.Heterogeneous`). For the Wasm
logic graphs presented with `Silmaril.Inst.GraphSpec` or `ObsGraph`, translation along a path
borrows entailment and refinement of *structured* specifications (unions, translations and
hidings, not only presentations) whenever the path is model-expansive:

* `InstGraph.entails_translatePath_iff`, `InstGraph.refines_translatePath_iff`: every path of
  the game graph `GInstRef → GInst → DGInst` (`Silmaril.Games.InstGraph`);
* `CompGameGraph.entails_translatePath_iff`, `CompGameGraph.refines_translatePath_iff`: every
  path of the component graph with the game institutions, through the cross edge;
* `DivGames.entails_translate_redGame_iff`, `DivGames.refines_translate_redGame_iff`: the
  `red → game` edge of the divergence-aware graph only (its `entry → red` edge is not claimed
  model-expansive, so no statement is made for paths through it);
* `ObsGraph.entails_translatePath_iff`, `ObsGraph.refines_translatePath_iff`: every path of any
  `ObsGraph` (the phase-1 Wasm graph and the reduction/game graph are instances).

All these graphs are `LogicGraph.{0, 0, 1, 0, 0, 0, 0}`: their nodes already share one universe
shape, so no lifting is needed here. A graph with `WasiInst` (`Inst.{0, …}`) lifts it with
`ULift` (`Silmaril.Wasi.Spec`).

A Silmaril addition: corollaries of `Silmaril.Logic.Institution.Hets.StructuredPaths`.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Structured

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Hets

/-! ## The game graph -/

namespace InstGraph

open Silmaril.Games.InstGraph

/-- **Borrowing of structured entailment along every path of the game graph.** -/
theorem entails_translatePath_iff {a b : graph.Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst graph.indexed (graph.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat graph.indexed) (graph.sigOf a S))
    (φ : ((IndexedCoInst.flat graph.indexed).obj (graph.sigOf a S)).Sen) :
    SP.Entails φ ↔ (StructuredPaths.translate graph p S SP).Entails
      (((IndexedCoInst.flat graph.indexed).map (StructuredPaths.lift graph p S)).sen φ) :=
  spec.entails_translatePath_iff allModelExpansive p S SP φ

/-- **Borrowing of refinement along every path of the game graph.** -/
theorem refines_translatePath_iff {a b : graph.Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst graph.indexed (graph.pt a)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat graph.indexed) (graph.sigOf a S)) :
    SP.Refines SQ ↔ (StructuredPaths.translate graph p S SP).Refines
      (StructuredPaths.translate graph p S SQ) :=
  spec.refines_translatePath_iff allModelExpansive p S SP SQ

end InstGraph

/-! ## The component graph with the game institutions -/

namespace CompGameGraph

open Silmaril.Wasm.Institution.CompGameGraph
open Silmaril.Wasm.Component (CoreSem CoreModule)

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- **Borrowing of structured entailment along every path of the component graph with the game
institutions.** -/
theorem entails_translatePath_iff {a b : (graph C).Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst (graph C).indexed ((graph C).pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat (graph C).indexed) ((graph C).sigOf a S))
    (φ : ((IndexedCoInst.flat (graph C).indexed).obj ((graph C).sigOf a S)).Sen) :
    SP.Entails φ ↔ (StructuredPaths.translate (graph C) p S SP).Entails
      (((IndexedCoInst.flat (graph C).indexed).map (StructuredPaths.lift (graph C) p S)).sen φ) :=
  (spec C).entails_translatePath_iff (allModelExpansive C) p S SP φ

/-- **Borrowing of refinement along every path of the component graph with the game
institutions.** -/
theorem refines_translatePath_iff {a b : (graph C).Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst (graph C).indexed ((graph C).pt a)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat (graph C).indexed) ((graph C).sigOf a S)) :
    SP.Refines SQ ↔ (StructuredPaths.translate (graph C) p S SP).Refines
      (StructuredPaths.translate (graph C) p S SQ) :=
  (spec C).refines_translatePath_iff (allModelExpansive C) p S SP SQ

end CompGameGraph

/-! ## The divergence-aware graph: the `red → game` edge -/

namespace DivGames

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Institution.DivGames

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (R : Silmaril.Wasm.Institution.DivGames.BRel)

/-- The one-edge path `red → game` of the divergence-aware graph. -/
noncomputable abbrev redGamePath :
    Quiver.Path (V := (divSpec P host R).toLogicGraph.Idx) DNode.red DNode.game :=
  Quiver.Path.nil.cons ((divSpec P host R).arrow ⟨1, Nat.one_lt_two⟩)

/-- The path `red → game` is model-expansive. -/
theorem redGamePath_modelExpansive :
    (divSpec P host R).toLogicGraph.PathModelExpansive (redGamePath P host R) :=
  ⟨trivial, redGame_modelExpansive' P host R⟩

/-- **Borrowing of structured entailment along `red → game`.** -/
theorem entails_translate_redGame_iff
    (S : (IndexedCoInst.inst (divSpec P host R).toLogicGraph.indexed
      ((divSpec P host R).toLogicGraph.pt DNode.red)).Sign)
    (SP : StrSpec (IndexedCoInst.flat (divSpec P host R).toLogicGraph.indexed)
      ((divSpec P host R).toLogicGraph.sigOf DNode.red S))
    (φ : ((IndexedCoInst.flat (divSpec P host R).toLogicGraph.indexed).obj
      ((divSpec P host R).toLogicGraph.sigOf DNode.red S)).Sen) :
    SP.Entails φ ↔
      (StructuredPaths.translate (divSpec P host R).toLogicGraph (redGamePath P host R) S
        SP).Entails (((IndexedCoInst.flat (divSpec P host R).toLogicGraph.indexed).map
          (StructuredPaths.lift (divSpec P host R).toLogicGraph (redGamePath P host R) S)).sen φ) :=
  StructuredPaths.entails_iff _ _ (redGamePath_modelExpansive P host R) S SP φ

/-- **Borrowing of refinement along `red → game`.** -/
theorem refines_translate_redGame_iff
    (S : (IndexedCoInst.inst (divSpec P host R).toLogicGraph.indexed
      ((divSpec P host R).toLogicGraph.pt DNode.red)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat (divSpec P host R).toLogicGraph.indexed)
      ((divSpec P host R).toLogicGraph.sigOf DNode.red S)) :
    SP.Refines SQ ↔
      (StructuredPaths.translate (divSpec P host R).toLogicGraph (redGamePath P host R) S
        SP).Refines
      (StructuredPaths.translate (divSpec P host R).toLogicGraph (redGamePath P host R) S SQ) :=
  StructuredPaths.refines_iff _ _ (redGamePath_modelExpansive P host R) S SP SQ

end DivGames

/-! ## Graphs of observational semantics -/

namespace ObsGraph

open Silmaril.Wasm.Institution (ObsGraph)

variable {Iface : Type} [Category.{0} Iface] (G : ObsGraph Iface)

/-- **Borrowing of structured entailment along every path of an `ObsGraph`.** -/
theorem entails_translatePath_iff {a b : G.graph.Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst G.graph.indexed (G.graph.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat G.graph.indexed) (G.graph.sigOf a S))
    (φ : ((IndexedCoInst.flat G.graph.indexed).obj (G.graph.sigOf a S)).Sen) :
    SP.Entails φ ↔ (StructuredPaths.translate G.graph p S SP).Entails
      (((IndexedCoInst.flat G.graph.indexed).map (StructuredPaths.lift G.graph p S)).sen φ) :=
  StructuredPaths.entails_iff G.graph p (G.pathModelExpansive p) S SP φ

/-- **Borrowing of refinement along every path of an `ObsGraph`.** -/
theorem refines_translatePath_iff {a b : G.graph.Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst G.graph.indexed (G.graph.pt a)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat G.graph.indexed) (G.graph.sigOf a S)) :
    SP.Refines SQ ↔ (StructuredPaths.translate G.graph p S SP).Refines
      (StructuredPaths.translate G.graph p S SQ) :=
  StructuredPaths.refines_iff G.graph p (G.pathModelExpansive p) S SP SQ

end ObsGraph

end Silmaril.Wasm.Institution.Structured
