module

public import Silmaril.Logic.Institution.Hets.Heterogeneous
public import Mathlib.CategoryTheory.PathCategory.Basic

@[expose] public section

/-!
# Logic graphs

Hets is organised around a *logic graph*: a graph whose nodes are logics (institutions) and
whose edges are comorphisms (logic translations) and morphisms (logic projections). Here:

* `LogicGraph`: a type of logics, an institution for each, and two families of edges:
  comorphisms `Comor a b` labelled with institution comorphisms and morphisms `Mor a b`
  labelled with institution morphisms.
* `LogicGraph.indexed`: the comorphism part as an indexed coinstitution on the free category
  `Paths L.Idx` of the comorphism quiver (Mathlib's `Paths.lift`): composite translations are
  paths, as in Hets, where a comorphism between two logics is found by searching the graph.
* `LogicGraph.flatInst`: the Grothendieck institution of the logic graph, reusing
  `IndexedCoInst.flatInst` (`Grothendieck/Basic.lean`). Heterogeneous specifications and
  development graphs over the logic graph live over this institution
  (`Hets/Heterogeneous.lean`, `Hets/SpecLanguage.lean`).
* `coHom_toPath`: an edge of the graph acts by its own comorphism;
  `modelExpansive_path`: a path of model-expansive comorphisms is model-expansive, so
  entailment is borrowed along it (`entails_lift_path_iff`).
* `IndexedCoInst.toLogicGraph`: every indexed coinstitution (such as `hetLogic`) is a logic
  graph with one comorphism edge per index morphism and no morphism edges;
  `indexed_toLogicGraph` relates the two presentations.

The institution morphisms of a logic graph are used by heterogeneous hiding along a morphism
(`LGSpec.hideMor` in `Hets/SpecLanguage.lean`).

## References

* `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4:
  "Heterogeneous specification is based on some graph of logics and logic translations,
  formalized as institutions and comorphisms"; Fig. 2, the Hets logic graph).
* `mossakowski-2005-habilitation-hets` in `references.bib`, §6.1, Definition 6.1 (printed
  page 149, PDF page 151: 2-indexed coinstitutions `I : Ind* ⟶ CoIns`) and §6.11 (printed pages
  179–180, PDF pages 181–182: heterogeneous hiding along institution morphisms).
* `mossakowski-tarlecki-2009-heterogeneous-logical-environments` in `references.bib`, §2,
  Definition 2.3 (PDF pages 4–5: "a heterogeneous logical environment `HLE` is … a pair of
  diagrams `⟨HLE^μ : G^μ → INS, HLE^ρ : G^ρ → coINS⟩` … [that] coincide on common nodes").
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u₀ v₀ u v w m₁ m₂

set_option linter.checkUnivs false in
/-- A logic graph: logics with their institutions, comorphism edges (logic translations) and
morphism edges (logic projections).

Source: `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4)
and Fig. 2; `mossakowski-tarlecki-2009-heterogeneous-logical-environments` in `references.bib`, §2,
Definition 2.3 (PDF pages 4–5): a logic graph is a heterogeneous logical environment with the
two edge graphs on a common set of nodes. -/
structure LogicGraph where
  /-- The logics (nodes of the graph). -/
  Logics : Type u₀
  /-- The institution of each logic. -/
  inst : Logics → Inst.{u, v, w, m₁, m₂}
  /-- Comorphism edges. -/
  Comor : Logics → Logics → Type v₀
  /-- The comorphism of a comorphism edge. -/
  comor : ∀ {a b : Logics}, Comor a b → Inst.CoHom (inst a) (inst b)
  /-- Morphism edges. -/
  Mor : Logics → Logics → Type v₀
  /-- The institution morphism of a morphism edge. -/
  mor : ∀ {a b : Logics}, Mor a b → Inst.Hom (inst a) (inst b)

namespace LogicGraph

variable (L : LogicGraph.{u₀, v₀, u, v, w, m₁, m₂})

/-- The logics, as the vertices of the quiver of comorphism edges. -/
def Idx : Type u₀ := L.Logics

instance : Quiver L.Idx := ⟨L.Comor⟩

/-- The comorphism edges as a prefunctor into `coINS`. -/
def comorPrefunctor : L.Idx ⥤q CoIns.{u, v, w, m₁, m₂} where
  obj a := L.inst a
  map e := L.comor e

/-- The comorphism part of a logic graph as an indexed coinstitution on the free category of
the comorphism quiver.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.1, Definition 6.1
(printed page 149, PDF page 151), without 2-cells;
`mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4). -/
def indexed : Paths L.Idx ⥤ CoIns.{u, v, w, m₁, m₂} :=
  Paths.lift L.comorPrefunctor

/-- The Grothendieck institution of a logic graph.

Source: `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4:
"This institution is basically a flattening, or disjoint union, of the logic graph");
`mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Definition 3.1 (PDF page 4). -/
def flatInst : Inst := IndexedCoInst.flatInst L.indexed

/-- The Grothendieck signatures of a logic graph. -/
abbrev Sig : Type _ := IndexedCoInst.FlatSig L.indexed

/-- The Grothendieck signature `(a, Σ)` of a signature `Σ` of the logic `a`. -/
abbrev sigOf (a : L.Idx) (S : (L.inst a).Sign) : L.Sig :=
  IndexedCoInst.mkSig L.indexed ((Paths.of L.Idx).obj a) S

/-- A logic as an object of the free category of the comorphism quiver. -/
abbrev pt (a : L.Idx) : Paths L.Idx := (Paths.of L.Idx).obj a

/-- A path of comorphism edges as a morphism of the free category. -/
abbrev pathHom {a b : L.Idx} (p : Quiver.Path a b) : L.pt a ⟶ L.pt b := p

/-- An edge of the graph acts by its own comorphism. -/
theorem coHom_toPath {a b : L.Idx} (e : a ⟶ b) :
    IndexedCoInst.coHom L.indexed ((Paths.of L.Idx).map e) = L.comor e :=
  Paths.lift_toPath L.comorPrefunctor e

/-- Every comorphism along a path of the comorphism quiver is model-expansive. -/
def PathModelExpansive {a : L.Idx} : {b : L.Idx} → Quiver.Path a b → Prop
  | _, .nil => True
  | _, .cons p e => PathModelExpansive p ∧ (L.comor e).ModelExpansive

/-- A path of model-expansive comorphisms acts by a model-expansive comorphism.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6, §4.1. -/
theorem modelExpansive_path {a b : L.Idx} (p : Quiver.Path a b) (hp : L.PathModelExpansive p) :
    (IndexedCoInst.coHom L.indexed (L.pathHom p)).ModelExpansive := by
  induction p with
  | nil =>
    show (IndexedCoInst.coHom L.indexed (𝟙 (L.pt a))).ModelExpansive
    rw [IndexedCoInst.coHom_id]
    exact Inst.CoHom.modelExpansive_id _
  | cons p e ih =>
    obtain ⟨hp, he⟩ := hp
    show (L.indexed.map (p.cons e)).ModelExpansive
    rw [indexed, Paths.lift_cons]
    exact (ih hp).comp he

/-- **Borrowing along a path of the logic graph**: consequence in the Grothendieck institution
is reflected by translation along a path of model-expansive comorphisms.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Theorem 5.3
(printed page 127, PDF page 129) and §6.4 (printed page 161, PDF page 163);
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7. -/
theorem entails_lift_path_iff {a b : L.Idx} (p : Quiver.Path a b) (hp : L.PathModelExpansive p)
    (S : (IndexedCoInst.inst L.indexed (L.pt a)).Sign)
    (Γ : Set ((IndexedCoInst.flat L.indexed).obj (IndexedCoInst.mkSig L.indexed (L.pt a) S)).Sen)
    (φ : ((IndexedCoInst.flat L.indexed).obj (IndexedCoInst.mkSig L.indexed (L.pt a) S)).Sen) :
    ((IndexedCoInst.flat L.indexed).obj (IndexedCoInst.mkSig L.indexed (L.pt a) S)).Entails Γ φ ↔
      ((IndexedCoInst.flat L.indexed).obj (IndexedCoInst.mkSig L.indexed (L.pt b)
          ((IndexedCoInst.coHom L.indexed (L.pathHom p)).Φ.obj S))).Entails
        (((IndexedCoInst.flat L.indexed).map
            (IndexedCoInst.lift L.indexed (L.pathHom p) S)).sen '' Γ)
        (((IndexedCoInst.flat L.indexed).map
            (IndexedCoInst.lift L.indexed (L.pathHom p) S)).sen φ) :=
  IndexedCoInst.entails_lift_iff L.indexed (L.pathHom p) (L.modelExpansive_path p hp) S Γ φ

end LogicGraph

namespace IndexedCoInst

variable {Ind : Type u₀} [Category.{v₀} Ind]

/-- An indexed coinstitution as a logic graph: one comorphism edge per index morphism, no
morphism edges. -/
def toLogicGraph (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂}) : LogicGraph.{u₀, v₀, u, v, w, m₁, m₂} where
  Logics := Ind
  inst := inst F
  Comor a b := a ⟶ b
  comor d := coHom F d
  Mor _ _ := PEmpty
  mor e := e.elim

/-- The comparison functor from the free category of the logic graph of `F` to the index
category, composing paths. -/
def pathComparison (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂}) : Paths (toLogicGraph F).Idx ⥤ Ind :=
  Paths.lift
    { obj := fun a => (a : Ind)
      map := fun {a b} (d : a ⟶ b) => (show (a : Ind) ⟶ b from d) }

/-- The logic graph of `F` presents `F`: its indexed coinstitution is `F` precomposed with path
composition. -/
theorem indexed_toLogicGraph (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂}) :
    (toLogicGraph F).indexed = pathComparison F ⋙ F := by
  refine (Paths.lift_unique _ _ ?_).symm
  refine Prefunctor.ext (fun _ => rfl) (fun a b e => ?_)
  show F.map ((pathComparison F).map (Quiver.Hom.toPath e)) = coHom F e
  exact congrArg F.map (Paths.lift_toPath _ e)

end IndexedCoInst

end Silmaril.Logic.Institution
