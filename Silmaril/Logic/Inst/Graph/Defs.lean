module

public import Silmaril.Logic.Inst.Thms

/-!
# A typed logic-graph builder

silmaril's `LogicGraph` asks for a type of logics, an institution per logic, and two families
of edge types with their labels. Most graphs in Silmaril are finite lists of edges between named
logics. `GraphSpec` presents such a graph:

* `inst : ι → Institution`: the institution of each logic;
* `comors : List (CoEdge inst)`: comorphism edges `⟨a, b, f⟩` with `f : Comorphism (inst a)
  (inst b)`, so that each edge is type checked against its endpoints;
* `mors : List (MorEdge inst)`: morphism edges.

`GraphSpec.toLogicGraph` builds the silmaril graph: the edges from `a` to `b` are the indices of
the listed edges with these endpoints. `GraphSpec.comor_edge` says a listed edge acts by its
comorphism, and `GraphSpec.pathModelExpansive` derives the model-expansiveness of every path
(and so heterogeneous borrowing, `LogicGraph.entails_lift_path_iff`) from the listed edges.
-/

@[expose] public section

namespace Silmaril.Inst

open CategoryTheory
open Silmaril.Logic.Institution (Room Corridor Inst LogicGraph IndexedCoInst)

universe u₀ v₀ u v w m₁ m₂

/-! ### Universe shapes of logic graphs

A silmaril `LogicGraph.{u₀, v₀, u, v, w, m₁, m₂}` has logics in `Type u₀`, edges in `Type v₀` and
nodes that are `Inst.{u, v, w, m₁, m₂}`. The shapes used in Silmaril have logics and edges in
`Type`; they are named after the institution shape of their nodes. -/

/-- Logic graphs of `Institution₀`s (`LogicGraph.{0, 0, 0, 0, 0, 0, 0}`). -/
abbrev LogicGraph₀ : Type _ := LogicGraph.{0, 0, 0, 0, 0, 0, 0}

/-- Logic graphs of `Institution₁`s (`LogicGraph.{0, 0, 1, 0, 0, 0, 0}`: the observational
Wasm logics, `Silmaril.Wasm.Institution.Graph.graph`). -/
abbrev LogicGraph₁ : Type _ := LogicGraph.{0, 0, 1, 0, 0, 0, 0}

/-- Logic graphs of `Institution₀₁`s (`LogicGraph.{0, 0, 0, 0, 0, 0, 1}`). -/
abbrev LogicGraph₀₁ : Type _ := LogicGraph.{0, 0, 0, 0, 0, 0, 1}

/-- Logic graphs of `Institution₁₁`s (`LogicGraph.{0, 0, 1, 0, 0, 0, 1}`: silmaril's PL, EQ and
FOL). -/
abbrev LogicGraph₁₁ : Type _ := LogicGraph.{0, 0, 1, 0, 0, 0, 1}

/-! ### Paths as comorphisms, and borrowing with projections

silmaril states borrowing along a path (`LogicGraph.entails_lift_path_iff`) in the Grothendieck
institution, with `IndexedCoInst.flat`, `mkSig` and `lift` written out. A path also *is* a
comorphism between its end nodes (the composite of its edges, `pathComor`), and borrowing along
it is borrowing along that comorphism: `entails_path_iff` states it with the facade projections
`(L.inst a).Entails` and `(L.pathComor p).sen S`. `flat_entails_path_iff` is the same statement
in the Grothendieck institution `L.flatInst`, at the signatures `L.sigOf a S`. -/

namespace LogicGraph

variable (L : LogicGraph.{u₀, v₀, u, v, w, m₁, m₂})

/-- The comorphism of a path: the composite of its edges (`𝟙ᶜ` for the empty path). -/
def pathComor {a b : L.Idx} (p : Quiver.Path a b) : Comorphism (L.inst a) (L.inst b) :=
  IndexedCoInst.coHom L.indexed (L.pathHom p)

variable {L}

@[simp] theorem pathComor_nil (a : L.Idx) :
    pathComor L (Quiver.Path.nil : Quiver.Path a a) = 𝟙ᶜ (L.inst a) :=
  IndexedCoInst.coHom_id L.indexed (L.pt a)

@[simp] theorem pathComor_cons {a b c : L.Idx} (p : Quiver.Path a b) (e : b ⟶ c) :
    pathComor L (p.cons e) = pathComor L p ≫ᶜ L.comor e := by
  change (Paths.lift L.comorPrefunctor).map (p.cons e) = _
  rw [Paths.lift_cons]
  rfl

/-- A path of model-expansive edges is a model-expansive comorphism. -/
theorem pathComor_modelExpansive {a b : L.Idx} {p : Quiver.Path a b}
    (hp : L.PathModelExpansive p) : (pathComor L p).ModelExpansive :=
  L.modelExpansive_path p hp

/-- **Borrowing along a path**, with projections: consequence at `S` in the logic `a` is
consequence of the translated sentences in the logic `b`. -/
theorem entails_path_iff {a b : L.Idx} {p : Quiver.Path a b} (hp : L.PathModelExpansive p)
    (S : (L.inst a).Sign) (Γ : Set ((L.inst a).Sen S)) (φ : (L.inst a).Sen S) :
    (L.inst a).Entails Γ φ ↔
      (L.inst b).Entails ((pathComor L p).sen S '' Γ) ((pathComor L p).sen S φ) :=
  Comorphism.entails_iff _ (pathComor_modelExpansive hp) S Γ φ

/-- **Borrowing validity along a path.** -/
theorem valid_path_iff {a b : L.Idx} {p : Quiver.Path a b} (hp : L.PathModelExpansive p)
    {S : (L.inst a).Sign} (φ : (L.inst a).Sen S) :
    (L.inst a).Valid φ ↔ (L.inst b).Valid ((pathComor L p).sen S φ) :=
  Comorphism.valid_iff _ (pathComor_modelExpansive hp) φ

/-- **Borrowing along a path in the Grothendieck institution**, with projections: silmaril's
`entails_lift_path_iff` at the signatures `L.sigOf a S` and `L.sigOf b (p.sig S)`. -/
theorem flat_entails_path_iff {a b : L.Idx} {p : Quiver.Path a b} (hp : L.PathModelExpansive p)
    (S : (L.inst a).Sign) (Γ : Set ((L.inst a).Sen S)) (φ : (L.inst a).Sen S) :
    Institution.Entails L.flatInst (S := L.sigOf a S) Γ φ ↔
      Institution.Entails L.flatInst (S := L.sigOf b ((pathComor L p).sig S))
        ((pathComor L p).sen S '' Γ) ((pathComor L p).sen S φ) := by
  have h := congrArg Corridor.sen (IndexedCoInst.flat_map_lift L.indexed (L.pathHom p) S)
  exact (L.entails_lift_path_iff p hp S Γ φ).trans (by rw [h]; exact Iff.rfl)

end LogicGraph

/-- A comorphism edge between two logics, typed by their institutions. -/
structure CoEdge {ι : Type u₀} (inst : ι → Institution.{u, v, w, m₁, m₂}) where
  /-- The source logic. -/
  src : ι
  /-- The target logic. -/
  tgt : ι
  /-- The comorphism. -/
  comor : Comorphism (inst src) (inst tgt)

/-- A morphism edge between two logics, typed by their institutions. -/
structure MorEdge {ι : Type u₀} (inst : ι → Institution.{u, v, w, m₁, m₂}) where
  /-- The source logic. -/
  src : ι
  /-- The target logic. -/
  tgt : ι
  /-- The institution morphism. -/
  mor : Morphism (inst src) (inst tgt)

variable {ι : Type u₀} {inst : ι → Institution.{u, v, w, m₁, m₂}}

/-- The comorphism of an edge, transported to given endpoints. -/
def CoEdge.at (e : CoEdge inst) {a b : ι} (ha : e.src = a) (hb : e.tgt = b) :
    Comorphism (inst a) (inst b) := by
  subst ha hb
  exact e.comor

/-- The morphism of an edge, transported to given endpoints. -/
def MorEdge.at (e : MorEdge inst) {a b : ι} (ha : e.src = a) (hb : e.tgt = b) :
    Morphism (inst a) (inst b) := by
  subst ha hb
  exact e.mor

@[simp] theorem CoEdge.at_rfl (e : CoEdge inst) : e.at rfl rfl = e.comor := rfl
@[simp] theorem MorEdge.at_rfl (e : MorEdge inst) : e.at rfl rfl = e.mor := rfl

/-- A logic graph given by lists of typed edges. -/
structure GraphSpec {ι : Type u₀} (inst : ι → Institution.{u, v, w, m₁, m₂}) where
  /-- Comorphism edges. -/
  comors : List (CoEdge inst)
  /-- Morphism edges. -/
  mors : List (MorEdge inst) := []

namespace GraphSpec

variable (G : GraphSpec inst)

/-- The comorphism edges from `a` to `b`: indices of listed edges with these endpoints. -/
def ComorIdx (a b : ι) : Type :=
  {i : Fin G.comors.length // G.comors[i].src = a ∧ G.comors[i].tgt = b}

/-- The morphism edges from `a` to `b`. -/
def MorIdx (a b : ι) : Type :=
  {i : Fin G.mors.length // G.mors[i].src = a ∧ G.mors[i].tgt = b}

set_option linter.checkUnivs false in
/-- The silmaril logic graph of a spec. -/
def toLogicGraph : LogicGraph.{u₀, 0, u, v, w, m₁, m₂} where
  Logics := ι
  inst := inst
  Comor := G.ComorIdx
  comor e := G.comors[e.1].at e.2.1 e.2.2
  Mor := G.MorIdx
  mor e := G.mors[e.1].at e.2.1 e.2.2

/-- The graph edge of the `i`-th listed comorphism. -/
def coEdge (i : Fin G.comors.length) : G.ComorIdx G.comors[i].src G.comors[i].tgt :=
  ⟨i, rfl, rfl⟩

/-- A listed comorphism edge acts by its comorphism. -/
@[simp] theorem comor_coEdge (i : Fin G.comors.length) :
    G.toLogicGraph.comor (G.coEdge i) = G.comors[i].comor := rfl

/-- The graph edge of the `i`-th listed morphism. -/
def morEdge (i : Fin G.mors.length) : G.MorIdx G.mors[i].src G.mors[i].tgt := ⟨i, rfl, rfl⟩

@[simp] theorem mor_morEdge (i : Fin G.mors.length) :
    G.toLogicGraph.mor (G.morEdge i) = G.mors[i].mor := rfl

/-- Every listed comorphism is model-expansive. -/
def AllModelExpansive : Prop := ∀ e ∈ G.comors, e.comor.ModelExpansive

/-- Every graph edge acts by a model-expansive comorphism when every listed one is. -/
theorem comor_modelExpansive (h : G.AllModelExpansive) {a b : ι} (e : G.ComorIdx a b) :
    (G.toLogicGraph.comor e).ModelExpansive := by
  obtain ⟨i, ha, hb⟩ := e
  have hi := h _ (List.getElem_mem i.isLt)
  change (G.comors[i].at ha hb).ModelExpansive
  revert ha hb
  generalize G.comors[i] = c at hi
  rintro rfl rfl
  exact hi

/-- **Every path is model-expansive** when every listed comorphism is; so heterogeneous
borrowing applies along every path of the graph. -/
theorem pathModelExpansive (h : G.AllModelExpansive) {a b : ι}
    (p : Quiver.Path (V := G.toLogicGraph.Idx) a b) :
    G.toLogicGraph.PathModelExpansive p := by
  induction p with
  | nil => trivial
  | cons p e ih => exact ⟨ih, G.comor_modelExpansive h e⟩

/-- `AllModelExpansive` from a check on each listed edge. -/
theorem allModelExpansive_of_forall (h : ∀ i : Fin G.comors.length,
    G.comors[i].comor.ModelExpansive) : G.AllModelExpansive := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact h ⟨i, hi⟩

/-- The `i`-th listed comorphism as an arrow of the graph, ready to form paths
(`Quiver.Path.nil.cons (G.arrow i)`). -/
def arrow (i : Fin G.comors.length) :
    @Quiver.Hom G.toLogicGraph.Idx _ G.comors[i].src G.comors[i].tgt :=
  G.coEdge i

/-- The comorphism of a path of the graph (`LogicGraph.pathComor`). -/
abbrev pathComor {a b : ι} (p : Quiver.Path (V := G.toLogicGraph.Idx) a b) :
    Comorphism (inst a) (inst b) :=
  LogicGraph.pathComor G.toLogicGraph p

/-- A one-edge path acts by the listed comorphism. -/
@[simp] theorem pathComor_arrow (i : Fin G.comors.length) :
    G.pathComor (Quiver.Path.nil.cons (G.arrow i)) = G.comors[i].comor :=
  rfl

/-- **Borrowing along a path of a `GraphSpec`**, with projections: if every listed comorphism is
model-expansive, consequence at `S` in the logic `a` is consequence of the translated
sentences in `b`. -/
theorem entails_path_iff (h : G.AllModelExpansive) {a b : ι}
    (p : Quiver.Path (V := G.toLogicGraph.Idx) a b) (S : (inst a).Sign) (Γ : Set ((inst a).Sen S))
    (φ : (inst a).Sen S) :
    (inst a).Entails Γ φ ↔ (inst b).Entails ((G.pathComor p).sen S '' Γ) ((G.pathComor p).sen S φ) :=
  LogicGraph.entails_path_iff (G.pathModelExpansive h p) S Γ φ

/-- **Borrowing validity along a path of a `GraphSpec`.** -/
theorem valid_path_iff (h : G.AllModelExpansive) {a b : ι}
    (p : Quiver.Path (V := G.toLogicGraph.Idx) a b) {S : (inst a).Sign} (φ : (inst a).Sen S) :
    (inst a).Valid φ ↔ (inst b).Valid ((G.pathComor p).sen S φ) :=
  LogicGraph.valid_path_iff (G.pathModelExpansive h p) φ

end GraphSpec

/-! ### Dot notation on silmaril logic graphs

As for institutions (`Silmaril.Logic.Inst.Defs`), the path lemmas are exported into silmaril's
`LogicGraph` namespace, so `L.pathComor p` and `L.entails_path_iff hp S Γ φ` work on any
`L : LogicGraph`. -/

end Silmaril.Inst

namespace Silmaril.Logic.Institution.LogicGraph

export Silmaril.Inst.LogicGraph (pathComor pathComor_nil pathComor_cons pathComor_modelExpansive
  entails_path_iff valid_path_iff flat_entails_path_iff)

end Silmaril.Logic.Institution.LogicGraph

namespace Silmaril.Inst

end Silmaril.Inst
