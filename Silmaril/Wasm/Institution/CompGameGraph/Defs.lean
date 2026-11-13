module

public import Silmaril.Games.InstGraph.Defs
public import Silmaril.Wasm.Institution.CompGraph.Defs
public import Silmaril.Wasm.Institution.GameInstMaps.Defs
public import Silmaril.Wasm.Institution.GameReadings.Thms

/-!
# The component graph with the game institutions

`CompGraph.compGraph C` (modules, components, flat components, programs and the component game
logic) and the game graph `Games.InstGraph.graph` (`GInstRef → GInst → DGInst`), joined by one
cross edge: the game reading of the component game logic into `GInst`
(`GameInst.coHom compIfaces sigU`, i.e. `(GameInst.reading compIfaces sigU).coHom`). The graph is
presented with the facade's typed builder `Silmaril.Inst.GraphSpec`:

* `inst C : CNode ⊕ InstGraph.Node → Institution₁`;
* `spec C : GraphSpec (inst C)`: the eight comorphism edges of `compGraph C` (`compEdge`), the
  two of `InstGraph` (`gameEdge`), the cross edge (`crossEdge`), and the eight morphism edges of
  `compGraph C` (`projEdge`); `graph C := (spec C).toLogicGraph`;
* `compIdx`, `gameIdx`, `crossIdx`: the graph edge of a named edge, acting by its comorphism
  (`comor_compIdx`, `comor_gameIdx`, `comor_crossIdx`);
* `compCoHom_eq_path`, `moduleCoHom_eq_path`, `programCoHom_eq_path`: the comorphisms of
  `GameInstMaps` into `GInst` are composites of an edge of `compGraph` with the cross edge, by
  `rfl`;
* `cross_modelExpansive`: the cross edge is model-expansive (`GameInst.coHom_modelExpansive`:
  `GameInst.modOf` is surjective);
* **`pathModelExpansive`**: every path of `graph C` is model-expansive, so heterogeneous
  borrowing (`LogicGraph.entails_lift_path_iff`) applies along every path, through the cross
  edge too.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.CompGameGraph

open CategoryTheory Silmaril.Logic.Institution Silmaril.Inst
open Silmaril.Wasm.Institution.CompGraph
open Silmaril.Wasm.Institution.Components
open Silmaril.Wasm.Component (CoreSem CoreModule)
open Silmaril.Games (GInst)

/-- The cross edges: the component game logic into `GInst`. -/
inductive Cross : CNode → Silmaril.Games.InstGraph.Node → Type
  | toGInst : Cross .game .plain

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- The institution of a node: a node of `compGraph C` or of the game graph. -/
def inst : CNode ⊕ Silmaril.Games.InstGraph.Node → Institution₁
  | .inl a => (compGraph C).inst a
  | .inr b => Silmaril.Games.InstGraph.inst b

/-- The comorphism of a cross edge: the game reading of the component game logic. -/
def cross : ∀ {a b}, Cross a b →
    Comorphism ((compGraph C).inst a) (Silmaril.Games.InstGraph.inst b)
  | _, _, .toGInst => GameInst.coHom compIfaces Silmaril.Wasm.Component.sigU

/-- An edge of `compGraph C`. -/
def compEdge {a b : CNode} (e : CEdge a b) : CoEdge (inst C) := ⟨.inl a, .inl b, (compGraph C).comor e⟩

/-- An edge of the game graph. -/
def gameEdge {a b : Silmaril.Games.InstGraph.Node} (e : Silmaril.Games.InstGraph.Edge a b) :
    CoEdge (inst C) :=
  ⟨.inr a, .inr b, Silmaril.Games.InstGraph.comor e⟩

/-- A cross edge. -/
def crossEdge {a b} (e : Cross a b) : CoEdge (inst C) := ⟨.inl a, .inr b, cross C e⟩

/-- A morphism edge of `compGraph C`. -/
def projEdge {a b : CNode} (e : CProj a b) : MorEdge (inst C) := ⟨.inl a, .inl b, (compGraph C).mor e⟩

/-- **The component graph with the game institutions, as a typed edge list.** -/
def spec : GraphSpec (inst C) where
  comors :=
    [compEdge C .linkedComp, compEdge C .compProgram, compEdge C .moduleGame,
      compEdge C .compGame, compEdge C .linkedGame, compEdge C .programGame, compEdge C .flatten,
      compEdge C .wrap, gameEdge C .toGInst, gameEdge C .toDGInst, crossEdge C .toGInst]
  mors :=
    [projEdge C .gameModule, projEdge C .gameComp, projEdge C .gameLinked,
      projEdge C .gameProgram, projEdge C .compLinked, projEdge C .programComp,
      projEdge C .linkedComp, projEdge C .compModule]

/-- **The component graph with the game institutions.** -/
abbrev graph : LogicGraph.{0, 0, 1, 0, 0, 0, 0} := (spec C).toLogicGraph

theorem length_comors : (spec C).comors.length = 11 := rfl

/-- The position of a listed comorphism edge. -/
def comorFin (i : ℕ) (h : i < 11 := by decide) : Fin (spec C).comors.length :=
  ⟨i, (length_comors C).symm ▸ h⟩

/-- The graph edge of an edge of `compGraph C`. -/
def compIdx : {a b : CNode} → CEdge a b → (graph C).Comor (.inl a) (.inl b)
  | _, _, .linkedComp => (spec C).coEdge (comorFin C 0)
  | _, _, .compProgram => (spec C).coEdge (comorFin C 1)
  | _, _, .moduleGame => (spec C).coEdge (comorFin C 2)
  | _, _, .compGame => (spec C).coEdge (comorFin C 3)
  | _, _, .linkedGame => (spec C).coEdge (comorFin C 4)
  | _, _, .programGame => (spec C).coEdge (comorFin C 5)
  | _, _, .flatten => (spec C).coEdge (comorFin C 6)
  | _, _, .wrap => (spec C).coEdge (comorFin C 7)

/-- The graph edge of an edge of the game graph. -/
def gameIdx : {a b : Silmaril.Games.InstGraph.Node} → Silmaril.Games.InstGraph.Edge a b →
    (graph C).Comor (.inr a) (.inr b)
  | _, _, .toGInst => (spec C).coEdge (comorFin C 8)
  | _, _, .toDGInst => (spec C).coEdge (comorFin C 9)

/-- The graph edge of a cross edge. -/
def crossIdx : ∀ {a b}, Cross a b → (graph C).Comor (.inl a) (.inr b)
  | _, _, .toGInst => (spec C).coEdge (comorFin C 10)

@[simp] theorem comor_compIdx {a b : CNode} (e : CEdge a b) :
    (graph C).comor (compIdx C e) = (compGraph C).comor e := by
  cases e <;> rfl

@[simp] theorem comor_gameIdx {a b : Silmaril.Games.InstGraph.Node}
    (e : Silmaril.Games.InstGraph.Edge a b) :
    (graph C).comor (gameIdx C e) = Silmaril.Games.InstGraph.comor e := by
  cases e <;> rfl

@[simp] theorem comor_crossIdx {a b} (e : Cross a b) : (graph C).comor (crossIdx C e) = cross C e := by
  cases e; rfl

/-- `GameInstMaps.compCoHom` is the edge `compGame` followed by the cross edge. -/
theorem compCoHom_eq_path :
    GameInstMaps.compCoHom C = (compGraph C).comor CEdge.compGame ≫ᶜ cross C .toGInst :=
  rfl

/-- `GameInstMaps.moduleCoHom` is the edge `moduleGame` followed by the cross edge. -/
theorem moduleCoHom_eq_path :
    GameInstMaps.moduleCoHom C = (compGraph C).comor CEdge.moduleGame ≫ᶜ cross C .toGInst :=
  rfl

/-- `GameInstMaps.programCoHom` is the edge `programGame` followed by the cross edge. -/
theorem programCoHom_eq_path :
    GameInstMaps.programCoHom C = (compGraph C).comor CEdge.programGame ≫ᶜ cross C .toGInst :=
  rfl

/-- **The cross edge is model-expansive**: every assignment of strategies to program variables is
read off one strategy on the copies (`GameInst.modOf_surjective`). -/
theorem cross_modelExpansive {a b} (e : Cross a b) : (cross C e).ModelExpansive := by
  cases e
  exact GameInst.coHom_modelExpansive compIfaces Silmaril.Wasm.Component.sigU

theorem compEdge_modelExpansive {a b : CNode} (e : CEdge a b) :
    (compEdge C e).comor.ModelExpansive :=
  edge_modelExpansive C e

theorem gameEdge_modelExpansive {a b : Silmaril.Games.InstGraph.Node}
    (e : Silmaril.Games.InstGraph.Edge a b) : (gameEdge C e).comor.ModelExpansive :=
  Silmaril.Games.InstGraph.edge_modelExpansive e

theorem crossEdge_modelExpansive {a b} (e : Cross a b) : (crossEdge C e).comor.ModelExpansive :=
  cross_modelExpansive C e

/-- Every listed comorphism edge is model-expansive. -/
theorem allModelExpansive : (spec C).AllModelExpansive := by
  intro e he
  simp only [spec, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact compEdge_modelExpansive C _
    | exact gameEdge_modelExpansive C _
    | exact crossEdge_modelExpansive C _

/-- **Every path of the component graph with the game institutions is model-expansive**, so
heterogeneous borrowing applies along every path, through the cross edge too. -/
theorem pathModelExpansive {a b : (graph C).Idx} (p : Quiver.Path a b) :
    (graph C).PathModelExpansive p :=
  (spec C).pathModelExpansive (allModelExpansive C) p

end Silmaril.Wasm.Institution.CompGameGraph
