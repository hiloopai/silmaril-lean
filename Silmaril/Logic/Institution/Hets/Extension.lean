module

public import Silmaril.Logic.Institution.Hets.DevGraph

@[expose] public section

/-!
# Faithful extensions of development graphs and isolated nodes

Several rules of the development-graph calculus extend the graph: Theorem-Hide-Shift adds a new
isolated node over a colimit of the unfolded subgraph below a node, and the completeness proof
adds a node over a pushout for every hiding link (Mossakowski–Autexier–Hutter, §5.1 and §7;
Mossakowski's habilitation, §5.6.1 rule Faithful-Extension). Here:

* `DevGraph.NewNode G` is the data of one new node: its signature, its local axioms and its
  incoming global, local and hiding definition links, all from old nodes.
* `G.addNode E` is the extended graph, with nodes `Option G.Node` (`none` is the new node). Its
  link relation stays well-founded (`addNode_wf`).
* `models_addNode_some`: the extension is *faithful*: old nodes keep their model classes (new
  links only go into the new node). This is the semantic content of Faithful-Extension.
* `IsolatedBy G P inc`: the node `P` has no local axioms, no local or hiding links into it, and
  its global links are among `inc`. `linkFrom` and `linkFrom₂` name the allowed links.
  `mem_models_of_isolatedBy` says when a model is a model of an isolated node.

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1 (PDF
  pages 10–12: isolated nodes, the new node `C` of Theorem-Hide-Shift) and §7 (PDF pages 17–18:
  "faithful extension `S₁` of `S` (i.e. new nodes and new definition links are added, but the
  latter go only into new nodes)").
* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.1, rule Faithful-Extension
  (printed pages 137–138, PDF pages 139–140), and §5.6.2 (printed page 139, PDF page 141: "an
  isolated node is one with no local axioms and no ingoing definition links other than those
  shown in the rule").
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe n u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace DevGraph

variable (G : DevGraph.{n} I)

/-- The data of one new node of a development graph, with incoming definition links from old
nodes only.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2 (printed page 139,
PDF page 141: the notation `DG' = DG ⊎ {N' with (Σ', Ψ); N ⟶ N'}`). -/
structure NewNode where
  /-- The signature of the new node. -/
  sig : Sign
  /-- Its local axioms. -/
  axioms : Set (I.obj sig).Sen
  /-- Global definition links `K ⟶σ new`. -/
  globalDef : (K : G.Node) → Set (G.sig K ⟶ sig)
  /-- Local definition links `K ⟶σ new`. -/
  localDef : (K : G.Node) → Set (G.sig K ⟶ sig)
  /-- Hiding definition links `K ⟶σ,h new`, with `σ : Σ_new ⟶ Σᴷ`. -/
  hidingDef : (K : G.Node) → Set (sig ⟶ G.sig K)

namespace NewNode

variable {G} (E : G.NewNode)

/-- Signatures of the extended graph. -/
def sigOf : Option G.Node → Sign
  | none => E.sig
  | some K => G.sig K

/-- Local axioms of the extended graph. -/
def axiomsOf : (N : Option G.Node) → Set (I.obj (E.sigOf N)).Sen
  | none => E.axioms
  | some K => G.axioms K

/-- Global definition links of the extended graph. -/
def globalOf : (M N : Option G.Node) → Set (E.sigOf M ⟶ E.sigOf N)
  | some K, some M => G.globalDef K M
  | some K, none => E.globalDef K
  | none, _ => ∅

/-- Local definition links of the extended graph. -/
def localOf : (M N : Option G.Node) → Set (E.sigOf M ⟶ E.sigOf N)
  | some K, some M => G.localDef K M
  | some K, none => E.localDef K
  | none, _ => ∅

/-- Hiding definition links of the extended graph. -/
def hidingOf : (M N : Option G.Node) → Set (E.sigOf N ⟶ E.sigOf M)
  | some K, some M => G.hidingDef K M
  | some K, none => E.hidingDef K
  | none, _ => ∅

end NewNode

/-- The link relation of the extended graph is well-founded: new links only go into the new
node, which has no outgoing links. -/
theorem addNode_wf (E : G.NewNode) : WellFounded fun M N : Option G.Node =>
    (E.globalOf M N).Nonempty ∨ (E.localOf M N).Nonempty ∨ (E.hidingOf M N).Nonempty := by
  have hsome : ∀ K : G.Node, Acc (fun M N : Option G.Node =>
      (E.globalOf M N).Nonempty ∨ (E.localOf M N).Nonempty ∨ (E.hidingOf M N).Nonempty)
      (some K) := by
    intro K
    refine G.wf.induction K (C := fun K => Acc _ (some K)) ?_
    intro K ih
    refine Acc.intro _ fun M hM => ?_
    cases M with
    | none =>
      rcases hM with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
        simp [NewNode.globalOf, NewNode.localOf, NewNode.hidingOf] at h
    | some M => exact ih M hM
  refine ⟨fun a => ?_⟩
  cases a with
  | some K => exact hsome K
  | none =>
    refine Acc.intro _ fun M hM => ?_
    cases M with
    | none =>
      rcases hM with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
        simp [NewNode.globalOf, NewNode.localOf, NewNode.hidingOf] at h
    | some M => exact hsome M

/-- The development graph `G` extended by one new node `none`, whose incoming links all come
from old nodes.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2 (printed page 139,
PDF page 141); `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`,
§7 (PDF page 17: faithful extensions). -/
def addNode (E : G.NewNode) : DevGraph.{n} I where
  Node := Option G.Node
  sig := E.sigOf
  axioms := E.axiomsOf
  globalDef := E.globalOf
  localDef := E.localOf
  hidingDef := E.hidingOf
  wf := G.addNode_wf E

/-- **Faithful extension**: an old node has the same models in the extended graph.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.1, rule
Faithful-Extension, soundness "by Prop. 5.16" (printed page 137, PDF page 139). -/
theorem models_addNode_some (E : G.NewNode) (K : G.Node) :
    (G.addNode E).models (some K) = G.models K := by
  refine G.wf.induction K (C := fun K => (G.addNode E).models (some K) = G.models K) ?_
  intro K ih
  ext n
  refine ((G.addNode E).mem_models_iff (some K) n).trans (Iff.trans ?_ (G.mem_models_iff K n).symm)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun K' σ hσ => ?_, fun K' σ hσ => h3 (some K') σ hσ, fun K' σ hσ => ?_⟩
    · have := h2 (some K') σ hσ
      rwa [ih K' (Or.inl ⟨σ, hσ⟩)] at this
    · obtain ⟨k, hk, hk'⟩ := h4 (some K') σ hσ
      rw [ih K' (Or.inr (Or.inr ⟨σ, hσ⟩))] at hk
      exact ⟨k, hk, hk'⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · intro K' σ hσ
      cases K' with
      | none => exact False.elim hσ
      | some K' =>
        rw [ih K' (Or.inl ⟨σ, hσ⟩)]
        exact h2 K' σ hσ
    · intro K' σ hσ
      cases K' with
      | none => exact False.elim hσ
      | some K' => exact h3 K' σ hσ
    · intro K' σ hσ
      cases K' with
      | none => exact False.elim hσ
      | some K' =>
        obtain ⟨k, hk, hk'⟩ := h4 K' σ hσ
        refine ⟨k, ?_, hk'⟩
        rw [ih K' (Or.inr (Or.inr ⟨σ, hσ⟩))]
        exact hk

/-- The defining equation of the models of the new node. -/
theorem mem_models_addNode_none (E : G.NewNode) (n : (I.obj E.sig).Mod) :
    n ∈ (G.addNode E).models none ↔ (∀ φ ∈ E.axioms, (I.obj E.sig).Sat n φ) ∧
      (∀ K, ∀ σ ∈ E.globalDef K, reduct σ n ∈ G.models K) ∧
      (∀ K, ∀ σ ∈ E.localDef K, ∀ φ ∈ G.axioms K, (I.obj (G.sig K)).Sat (reduct σ n) φ) ∧
      (∀ K, ∀ σ ∈ E.hidingDef K, ∃ k ∈ G.models K, reduct σ k = n) := by
  refine ((G.addNode E).mem_models_iff (none : Option G.Node) n).trans ?_
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun K σ hσ => ?_, fun K σ hσ => h3 (some K) σ hσ, fun K σ hσ => ?_⟩
    · have := h2 (some K) σ hσ
      rwa [models_addNode_some] at this
    · obtain ⟨k, hk, hk'⟩ := h4 (some K) σ hσ
      rw [models_addNode_some] at hk
      exact ⟨k, hk, hk'⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · intro K σ hσ
      cases K with
      | none => exact False.elim hσ
      | some K =>
        rw [models_addNode_some]
        exact h2 K σ hσ
    · intro K σ hσ
      cases K with
      | none => exact False.elim hσ
      | some K => exact h3 K σ hσ
    · intro K σ hσ
      cases K with
      | none => exact False.elim hσ
      | some K =>
        obtain ⟨k, hk, hk'⟩ := h4 K σ hσ
        refine ⟨k, ?_, hk'⟩
        rw [models_addNode_some]
        exact hk

/-! ### Isolated nodes -/

/-- The single link `K₀ ⟶τ P`, as a family of sets of morphisms into `P` indexed by source
nodes. -/
def linkFrom {P : G.Node} (K₀ : G.Node) (τ : G.sig K₀ ⟶ G.sig P) (K : G.Node) :
    Set (G.sig K ⟶ G.sig P) :=
  {σ | ∃ h : K = K₀, σ = eqToHom (congrArg G.sig h) ≫ τ}

/-- The two links `K₁ ⟶τ₁ P` and `K₂ ⟶τ₂ P`. -/
def linkFrom₂ {P : G.Node} (K₁ : G.Node) (τ₁ : G.sig K₁ ⟶ G.sig P) (K₂ : G.Node)
    (τ₂ : G.sig K₂ ⟶ G.sig P) (K : G.Node) : Set (G.sig K ⟶ G.sig P) :=
  G.linkFrom K₁ τ₁ K ∪ G.linkFrom K₂ τ₂ K

/-- `P` is *isolated* with incoming global links among `inc`: no local axioms, no local or
hiding links into `P`, and every global link into `P` is in `inc`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
(PDF page 11: "an isolated node is one with no local axioms and no ingoing definition links
other than those shown in the rule"); `mossakowski-2005-habilitation-hets` in `references.bib`,
§5.6.2 (printed page 139, PDF page 141). -/
def IsolatedBy (P : G.Node) (inc : (K : G.Node) → Set (G.sig K ⟶ G.sig P)) : Prop :=
  G.axioms P = ∅ ∧ (∀ K, G.globalDef K P ⊆ inc K) ∧ (∀ K, G.localDef K P = ∅) ∧
    ∀ K, G.hidingDef K P = ∅

variable {G}

/-- A model of an isolated node is anything whose reducts along the allowed links are models of
their sources. -/
theorem mem_models_of_isolatedBy {P : G.Node} {inc : (K : G.Node) → Set (G.sig K ⟶ G.sig P)}
    (hP : G.IsolatedBy P inc) {n : (I.obj (G.sig P)).Mod}
    (hn : ∀ K, ∀ σ ∈ inc K, reduct σ n ∈ G.models K) : n ∈ G.models P := by
  obtain ⟨hax, hg, hl, hh⟩ := hP
  rw [G.mem_models_iff]
  refine ⟨by simp [hax], fun K σ hσ => hn K σ (hg K hσ), fun K σ hσ => ?_, fun K σ hσ => ?_⟩
  · simp [hl K] at hσ
  · simp [hh K] at hσ

end DevGraph

end Silmaril.Logic.Institution
