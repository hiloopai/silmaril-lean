module

public import Silmaril.Wasm.Institution.Games.Thms
public import Silmaril.Wasm.Institution.Hooks.Defs

@[expose] public section

/-!
# The Wasm logic graph with reduction and game semantics

`gameGraph G E red` has three logics over the same programs `RProg`:

* `red`: the reduction-semantics logic `redSem G E red`;
* `lts`: the transition-system logic of `fun p => (red p).toLTS`;
* `game`: the game-semantics logic `gameSem G E` (programs are strategies).

Comorphism edges `red → lts`, `lts → game` and `red → game` (`p ↦ ofReduction (red p)`; the
satisfaction condition is the adequacy equation `sem_den`) are all model-expansive. Morphism
edges `game → red`, `game → lts` and `lts → red` are their duals (`Translation.toHom`), and they
project the game logic onto the operational ones.

`fullGraph P host Env` is the sum of the phase-1 graph (`Graph.graph`) with the game graph of
the grounded Wasm reduction `wasmRed P host` (interfaces `exportIfaces`, lower signature
`Sig.empty`). There are **no cross edges**: no comorphism from the module-level session or entry
logics into the game logic is proved (see `docs/projects/logic-inst.md`, "Phase 2A"). The
relation that is proved is `finite_beh_of_le`, an implication between validities rather than a
comorphism. Every path of `fullGraph` is model-expansive (`fullGraph_pathModelExpansive`), so
heterogeneous borrowing applies to it.
-/

namespace Silmaril.Wasm.Institution.GameGraph

open CategoryTheory Silmaril.Logic.Institution ObsSemantics Silmaril.Wasm.Institution.Games

/-- Nodes of the game graph. -/
inductive GNode where
  /-- Reduction semantics. -/
  | red
  /-- Transition systems. -/
  | lts
  /-- Game semantics. -/
  | game
  deriving DecidableEq

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0}) {RProg : Type}
  (red : RProg → Silmaril.Games.Reduction E (G.sig G.top))

/-- The semantics of a node. -/
def sem : GNode → ObsSemantics G.I
  | .red => redSem G E red
  | .lts => ltsSem G E fun p => (red p).toLTS
  | .game => gameSem G E

/-- Comorphism edges. -/
inductive GEdge : GNode → GNode → Type where
  | redLts : GEdge .red .lts
  | ltsGame : GEdge .lts .game
  | redGame : GEdge .red .game

/-- Morphism (projection) edges. -/
inductive GProj : GNode → GNode → Type where
  | gameRed : GProj .game .red
  | gameLts : GProj .game .lts
  | ltsRed : GProj .lts .red

/-- The translation of an edge. -/
def edgeT : {a b : GNode} → GEdge a b → Translation (𝟭 G.I) (sem G E red a) (sem G E red b)
  | _, _, .redLts => redToLts G E red
  | _, _, .ltsGame => ltsToGame G E fun p => (red p).toLTS
  | _, _, .redGame => redToGame G E red

theorem edgeT_surjective : ∀ {a b : GNode} (e : GEdge a b) (X : G.I),
    Function.Surjective ((edgeT G E red e).sem X)
  | _, _, .redLts, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .ltsGame, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .redGame, _ => fun σ => ⟨σ, rfl⟩

/-- The morphism of a projection edge. -/
def projHom : {a b : GNode} → GProj a b → Inst.Hom (sem G E red a).inst (sem G E red b).inst
  | _, _, .gameRed => (edgeT G E red .redGame).toHom
  | _, _, .gameLts => (edgeT G E red .ltsGame).toHom
  | _, _, .ltsRed => (edgeT G E red .redLts).toHom

/-- **The reduction/game logic graph.** -/
def gameGraph : Silmaril.Inst.LogicGraph₁ where
  Logics := GNode
  inst a := (sem G E red a).inst
  Comor := GEdge
  comor e := (edgeT G E red e).coHom
  Mor := GProj
  mor e := projHom G E red e

theorem edge_modelExpansive {a b : GNode} (e : GEdge a b) :
    ((gameGraph G E red).comor e).ModelExpansive :=
  (edgeT G E red e).coHom_modelExpansive (edgeT_surjective G E red e)

theorem proj_sound {a b : GNode} (e : GProj a b) : ((gameGraph G E red).mor e).Sound := by
  cases e with
  | gameRed => exact (edgeT G E red .redGame).toHom_sound (edgeT_surjective G E red _)
  | gameLts => exact (edgeT G E red .ltsGame).toHom_sound (edgeT_surjective G E red _)
  | ltsRed => exact (edgeT G E red .redLts).toHom_sound (edgeT_surjective G E red _)

/-! ## The full graph -/

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- **The Wasm logic graph with reduction and game semantics**: the phase-1 graph plus the game
graph of the Core reduction of instantiated modules, with no cross edges. -/
def fullGraph : Silmaril.Inst.LogicGraph₁ :=
  LogicGraph.sum (Graph.graph P host Env)
    (gameGraph exportIfaces Silmaril.Games.Sig.empty (wasmRed P host))
    (fun _ _ => PEmpty) (fun e => e.elim)

/-- Every path of the full graph is model-expansive. -/
theorem fullGraph_pathModelExpansive {a b : (fullGraph P host Env).Idx}
    (p : Quiver.Path a b) : (fullGraph P host Env).PathModelExpansive p :=
  LogicGraph.sum_pathModelExpansive _ _ _ _ (fun e => Graph.edge_modelExpansive P host Env e)
    (fun e => edge_modelExpansive exportIfaces Silmaril.Games.Sig.empty (wasmRed P host) e)
    (fun e => e.elim) p

end Silmaril.Wasm.Institution.GameGraph
