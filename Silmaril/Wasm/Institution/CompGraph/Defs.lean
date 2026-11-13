module

public import Silmaril.Wasm.Institution.Components.Thms
public import Silmaril.Wasm.Institution.GameGraph.Defs

@[expose] public section

/-!
# The Wasm logic graph with modules, components and games

`compGraph C` has five logics over the component interfaces `compIfaces`, for a core semantics
`C : CoreSem M`: `module`, `comp` (nested IR), `linked` (flat IR), `program`, and `game` (the
component game logic).

**Comorphism edges**, all model-expansive (identity semantic maps):

* `linkedComp : linked → comp` (`Linked.toComponent`, satisfaction by `Linked.denU_toComponent`);
* `compProgram : comp → program` (`c ↦ ⟨c, none⟩`, by `rfl`);
* `moduleGame`, `compGame`, `linkedGame`, `programGame`: a program goes to its strategy
  (`modU`, `Comp.denU`, …). The satisfaction condition is `rfl`, since the component logics are
  *defined* by their game semantics;
* `flatten : comp → linked` (`denU_flatten pairLaws`): flattening preserves meaning;
* `wrap : module → comp`: the trivial wrapping component. Its satisfaction condition is the
  adequacy equation `(wrap m).denU C = modU C m` (wrapping preserves meaning, `wrap_denU`).

**Morphism edges** (sound projections, the duals `toHom` of the unconditional comorphisms):
`game → module`, `game → comp`, `game → linked`, `game → program`, `comp → linked`,
`program → comp`, `linked → comp` (dual of `flatten`) and `comp → module` (dual of `wrap`).

`fullGraph₂ P host Env C` joins `GameGraph.fullGraph P host Env` with `compGraph C`. It has **no
cross edges**: the core modules `M` of the component IR are abstract, with no `CoreModule`
instance for silmaril's `Module`/`BModule` and no `CoreSem` built from silmaril's Core semantics,
and the component game signatures (`sigU` with payloads) differ from the export signatures of
part A (`exportSig`, with behaviours). Every path of `fullGraph₂` is model-expansive.
-/

namespace Silmaril.Wasm.Institution.CompGraph

open CategoryTheory Silmaril.Logic.Institution ObsSemantics Silmaril.Wasm.Institution.Games
open Silmaril.Wasm.Institution.Components Silmaril.Wasm.Component

/-- Nodes of the component graph. -/
inductive CNode where
  | module
  | comp
  | linked
  | program
  | game
  deriving DecidableEq

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- The semantics of a node. -/
def sem : CNode → ObsSemantics compIfaces.I
  | .module => moduleSem C
  | .comp => compSem C
  | .linked => linkedSem C
  | .program => programSem C
  | .game => compGameSem

/-- Comorphism edges. -/
inductive CEdge : CNode → CNode → Type where
  | linkedComp : CEdge .linked .comp
  | compProgram : CEdge .comp .program
  | moduleGame : CEdge .module .game
  | compGame : CEdge .comp .game
  | linkedGame : CEdge .linked .game
  | programGame : CEdge .program .game
  /-- Flattening. -/
  | flatten : CEdge .comp .linked
  /-- Wrapping a core module as a component. -/
  | wrap : CEdge .module .comp

/-- Morphism (projection) edges. -/
inductive CProj : CNode → CNode → Type where
  | gameModule : CProj .game .module
  | gameComp : CProj .game .comp
  | gameLinked : CProj .game .linked
  | gameProgram : CProj .game .program
  | compLinked : CProj .comp .linked
  | programComp : CProj .program .comp
  | linkedComp : CProj .linked .comp
  | compModule : CProj .comp .module

/-- The translation of an edge. -/
def edgeT : {a b : CNode} → CEdge a b → Translation (𝟭 compIfaces.I) (sem C a) (sem C b)
  | _, _, .linkedComp => linkedToComp C
  | _, _, .compProgram => compToProgram C
  | _, _, .moduleGame => moduleToGame C
  | _, _, .compGame => compToGame C
  | _, _, .linkedGame => linkedToGame C
  | _, _, .programGame => programToGame C
  | _, _, .flatten => flattenTr C pairLaws
  | _, _, .wrap => wrapTr C (wrapAdequate C)

theorem edgeT_surjective : ∀ {a b : CNode} (e : CEdge a b) (X : compIfaces.I),
    Function.Surjective ((edgeT C e).sem X)
  | _, _, .linkedComp, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .compProgram, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .moduleGame, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .compGame, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .linkedGame, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .programGame, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .flatten, _ => fun σ => ⟨σ, rfl⟩
  | _, _, .wrap, _ => fun σ => ⟨σ, rfl⟩

/-- The morphism of a projection edge. -/
def projHom : {a b : CNode} → CProj a b → Inst.Hom (sem C a).inst (sem C b).inst
  | _, _, .gameModule => (moduleToGame C).toHom
  | _, _, .gameComp => (compToGame C).toHom
  | _, _, .gameLinked => (linkedToGame C).toHom
  | _, _, .gameProgram => (programToGame C).toHom
  | _, _, .compLinked => (linkedToComp C).toHom
  | _, _, .programComp => (compToProgram C).toHom
  | _, _, .linkedComp => (flattenTr C pairLaws).toHom
  | _, _, .compModule => (wrapTr C (wrapAdequate C)).toHom

/-- **The module/component/game logic graph.** -/
def compGraph : Silmaril.Logic.Institution.LogicGraph.{0, 0, 1, 0, 0, 0, 0} where
  Logics := CNode
  inst a := (sem C a).inst
  Comor := CEdge
  comor e := (edgeT C e).coHom
  Mor := CProj
  mor e := projHom C e

theorem edge_modelExpansive {a b : CNode} (e : CEdge a b) :
    ((compGraph C).comor e).ModelExpansive :=
  (edgeT C e).coHom_modelExpansive (edgeT_surjective C e)

theorem proj_sound {a b : CNode} (e : CProj a b) : ((compGraph C).mor e).Sound := by
  cases e with
  | gameModule => exact (moduleToGame C).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | gameComp => exact (compToGame C).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | gameLinked => exact (linkedToGame C).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | gameProgram => exact (programToGame C).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | compLinked => exact (linkedToComp C).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | programComp => exact (compToProgram C).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | linkedComp => exact (flattenTr C pairLaws).toHom_sound (fun _ σ => ⟨σ, rfl⟩)
  | compModule => exact (wrapTr C (wrapAdequate C)).toHom_sound (fun _ σ => ⟨σ, rfl⟩)

/-- **Borrowing along wrapping**: a sentence about core modules is valid iff its translation
about their wrappers is valid in the component logic. -/
theorem valid_wrap_iff {K : Sig compIfaces.I} (s : Sen (moduleSem C) K) :
    (moduleSem C).Valid s ↔ (compSem C).Valid ((wrapTr C (wrapAdequate C)).sen s) :=
  (wrapTr C (wrapAdequate C)).valid_iff (fun _ σ => ⟨σ, rfl⟩) s

/-- Borrowing along flattening: a sentence about nested components is valid iff its translation
about their flattenings is valid in the flat logic. -/
theorem valid_flatten_iff {K : Sig compIfaces.I} (s : Sen (compSem C) K) :
    (compSem C).Valid s ↔ (linkedSem C).Valid ((flattenTr C pairLaws).sen s) :=
  (flattenTr C pairLaws).valid_iff (fun _ σ => ⟨σ, rfl⟩) s

/-! ## The full graph -/

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- **The complete Wasm logic graph**: module-level reduction semantics (phase 1), reduction
versus games (phase 2A), modules versus components (phase 2B). -/
def fullGraph₂ : Silmaril.Logic.Institution.LogicGraph.{0, 0, 1, 0, 0, 0, 0} :=
  LogicGraph.sum (GameGraph.fullGraph P host Env) (compGraph C) (fun _ _ => PEmpty)
    (fun e => e.elim)

/-- Every path of the complete graph is model-expansive, so heterogeneous borrowing applies. -/
theorem fullGraph₂_pathModelExpansive {a b : (fullGraph₂ C P host Env).Idx}
    (p : Quiver.Path a b) : (fullGraph₂ C P host Env).PathModelExpansive p :=
  LogicGraph.sum_pathModelExpansive _ _ _ _
    (fun e => LogicGraph.sum_edge_modelExpansive _ _ _ _
      (fun e => Graph.edge_modelExpansive P host Env e)
      (fun e => GameGraph.edge_modelExpansive exportIfaces Silmaril.Games.Sig.empty
        (wasmRed P host) e) (fun e => e.elim) e)
    (fun e => edge_modelExpansive C e) (fun e => e.elim) p

end Silmaril.Wasm.Institution.CompGraph
