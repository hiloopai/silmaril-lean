module

public import Silmaril.Wasm.Institution.Api.Defs
public import Silmaril.Wasm.Institution.GameGraph.Defs

@[expose] public section

/-!
# The Wasm logic graphs through the institution API

The phase-1 graph (`Graph.graph`) and the reduction/game graph (`GameGraph.gameGraph`) are
`ObsGraph`s: each is presented here by its nodes, its edges as model-expansive translations and
its projections, and the silmaril logic graph that `ObsGraph.graph` builds from that is the
existing one (`Graph.graph_eq`, `GameGraph.gameGraph_eq`). Model-expansiveness is closed under
the graph sum and the one-node extension of `Silmaril.Wasm.Institution.Hooks`
(`LogicGraph.AllExpansive.sum`, `LogicGraph.AllExpansive.extend`), so borrowing along every
path of `GameGraph.fullGraph` is one line (`GameGraph.fullGraph_entails_path_iff`).
-/

namespace Silmaril.Wasm.Institution

open CategoryTheory Silmaril.Logic.Institution ObsSemantics

/-! ## Closure of `AllExpansive` under sums and extensions -/

namespace LogicGraph

/-- The sum of two graphs with model-expansive edges and model-expansive cross edges. -/
theorem AllExpansive.sum {L₁ L₂ : Silmaril.Inst.LogicGraph₁} (h₁ : AllExpansive L₁)
    (h₂ : AllExpansive L₂)
    (Cross : L₁.Logics → L₂.Logics → Type)
    (cross : ∀ {a b}, Cross a b → Inst.CoHom (L₁.inst a) (L₂.inst b))
    (hc : ∀ {a b} (e : Cross a b), (cross e).ModelExpansive) :
    AllExpansive (LogicGraph.sum L₁ L₂ Cross cross) :=
  ⟨LogicGraph.sum_edge_modelExpansive L₁ L₂ Cross cross h₁.edge h₂.edge hc⟩

/-- The sum of two graphs without cross edges. -/
theorem AllExpansive.sum_empty {L₁ L₂ : Silmaril.Inst.LogicGraph₁} (h₁ : AllExpansive L₁)
    (h₂ : AllExpansive L₂) :
    AllExpansive (LogicGraph.sum L₁ L₂ (fun _ _ => PEmpty) (fun e => e.elim)) :=
  h₁.sum h₂ _ _ (fun e => e.elim)

/-- The extension of a graph by one logic with model-expansive incoming edges. -/
theorem AllExpansive.extend {L : Silmaril.Inst.LogicGraph₁} (h : AllExpansive L)
    (J : Silmaril.Inst.Institution₁)
    (In : L.Logics → Type) (inE : ∀ {a}, In a → Inst.CoHom (L.inst a) J)
    (hIn : ∀ {a} (e : In a), (inE e).ModelExpansive) :
    AllExpansive (LogicGraph.extend L J In inE) :=
  ⟨LogicGraph.extend_edge_modelExpansive L J In inE h.edge hIn⟩

end LogicGraph

/-! ## The phase-1 graph -/

namespace Graph

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- The translation read backwards by a projection edge. -/
def projET : {a b : Node} → Proj a b →
    ExpTranslation (𝟭 (Set String)) (sem P host Env b) (sem P host Env a)
  | _, _, .trapsUB f l => ⟨edgeT P host Env (.close f l), edgeT_surjective P host Env _⟩
  | _, _, .equiv f l => ⟨edgeT P host Env (.equivRef f l), edgeT_surjective P host Env _⟩

/-- **The phase-1 Wasm logic graph as an `ObsGraph`.** -/
def obsGraph : ObsGraph (Set String) where
  Node := Node
  sem := sem P host Env
  Edge := Edge
  edge e := ⟨edgeT P host Env e, edgeT_surjective P host Env e⟩
  Proj := Proj
  proj e := projET P host Env e

theorem projHom_eq {a b : Node} (e : Proj a b) :
    projHom P host Env e = (projET P host Env e).morphism := by
  cases e <;> rfl

/-- The builder gives back the phase-1 graph. -/
theorem graph_eq : graph P host Env = (obsGraph P host Env).graph := by
  simp only [graph, ObsGraph.graph, obsGraph, projHom_eq]
  rfl

theorem allExpansive : LogicGraph.AllExpansive (graph P host Env) :=
  ⟨fun e => edge_modelExpansive P host Env e⟩

end Graph

/-! ## The reduction/game graph -/

namespace GameGraph

variable (G : Games.GameIfaces) (E : Silmaril.Games.Sig.{0}) {RProg : Type}
  (red : RProg → Silmaril.Games.Reduction E (G.sig G.top))

/-- The translation read backwards by a projection edge. -/
def projET : {a b : GNode} → GProj a b →
    ExpTranslation (𝟭 G.I) (sem G E red b) (sem G E red a)
  | _, _, .gameRed => ⟨edgeT G E red .redGame, edgeT_surjective G E red _⟩
  | _, _, .gameLts => ⟨edgeT G E red .ltsGame, edgeT_surjective G E red _⟩
  | _, _, .ltsRed => ⟨edgeT G E red .redLts, edgeT_surjective G E red _⟩

/-- **The reduction/game logic graph as an `ObsGraph`.** -/
def obsGraph : ObsGraph G.I where
  Node := GNode
  sem := sem G E red
  Edge := GEdge
  edge e := ⟨edgeT G E red e, edgeT_surjective G E red e⟩
  Proj := GProj
  proj e := projET G E red e

theorem projHom_eq {a b : GNode} (e : GProj a b) :
    projHom G E red e = (projET G E red e).morphism := by
  cases e <;> rfl

/-- The builder gives back the reduction/game graph. -/
theorem gameGraph_eq : gameGraph G E red = (obsGraph G E red).graph := by
  simp only [gameGraph, ObsGraph.graph, obsGraph, projHom_eq]
  rfl

theorem allExpansive : LogicGraph.AllExpansive (gameGraph G E red) :=
  ⟨fun e => edge_modelExpansive G E red e⟩

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- Every edge of the full reduction/game graph is model-expansive. -/
theorem fullGraph_allExpansive : LogicGraph.AllExpansive (fullGraph P host Env) :=
  (Graph.allExpansive P host Env).sum_empty (allExpansive _ _ _)

/-- **Heterogeneous borrowing along every path of the full reduction/game graph.** -/
theorem fullGraph_entails_path_iff {a b : (fullGraph P host Env).Idx} (p : Quiver.Path a b)
    (S : LogicGraph.Sign (fullGraph P host Env) a)
    (Γ : Set (LogicGraph.FlatRoom (fullGraph P host Env) a S).Sen)
    (φ : (LogicGraph.FlatRoom (fullGraph P host Env) a S).Sen) :
    (LogicGraph.FlatRoom (fullGraph P host Env) a S).Entails Γ φ ↔
      (LogicGraph.FlatRoom (fullGraph P host Env) b
          (LogicGraph.pathSig (fullGraph P host Env) p S)).Entails
        (LogicGraph.pathSen (fullGraph P host Env) p S '' Γ)
        (LogicGraph.pathSen (fullGraph P host Env) p S φ) :=
  (fullGraph_allExpansive P host Env).entails_path_iff p S Γ φ

end GameGraph

end Silmaril.Wasm.Institution
