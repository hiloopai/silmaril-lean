module

public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

/-!
# Development graphs

Development graphs with hiding (Mossakowski, Autexier and Hutter 2006) over an institution given
as a room functor `I : Sign ⥤ Room`. Over the Grothendieck institution of a logic graph they are
Hets' heterogeneous development graphs (`Hets/Heterogeneous.lean`).

* A development graph (`DevGraph I`) has nodes labelled with a signature and a set of local
  axioms, and three kinds of definition links: global links `M ⟶σ N` and local links
  `M ⟶σ N`, both with `σ : Σᴹ ⟶ Σᴺ`, and hiding links `M ⟶σ,h N` with `σ : Σᴺ ⟶ Σᴹ` against
  the direction of the link. The links between two nodes are given as sets of signature
  morphisms. The graph is acyclic; for possibly infinite graphs we ask that the link relation be
  well-founded.
* The model class `DevGraph.models` of a node (Definition 8) is defined by well-founded
  recursion; `mem_models_iff` is its defining equation.
* Global and local reachability (Definition 5), the theory of a node (Definition 7) and
  flattenable nodes (Definition 6), with Propositions 9 and 10.
* Global and local theorem links, local implications and hiding theorem links (Definition 11),
  and conservative links.
* The decomposition rules of §5.2 and their soundness are in `Hets/Decomposition.lean`.

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`: §4,
  Definitions 4–11 and Propositions 9–10 (PDF pages 6–9); §5.2 and Proposition 13 (PDF
  pages 13–15).
* `mossakowski-2005-habilitation-hets` in `references.bib`: §5.5, Definition 5.8 (printed
  page 132, PDF page 134); §6.4, Definition 6.25 and Figure 6.1 (printed pages 161–162, PDF
  pages 163–164).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe n u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- A development graph with hiding over the institution `I`: nodes `N = (Σᴺ, Φᴺ)` with local
axioms, global, local and hiding definition links, and a well-founded (acyclic) link relation.
`globalDef M N` is the set of morphisms `σ` with a global definition link `M ⟶σ N`;
`hidingDef M N` is the set of `σ : Σᴺ ⟶ Σᴹ` with a hiding link `M ⟶σ,h N`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 4 (PDF page 6); `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5,
Definition 5.8 (printed page 132, PDF page 134). -/
structure DevGraph where
  /-- The nodes. -/
  Node : Type n
  /-- The signature `Σᴺ` of a node. -/
  sig : Node → Sign
  /-- The local axioms `Φᴺ ⊆ Sen(Σᴺ)`. -/
  axioms : (N : Node) → Set (I.obj (sig N)).Sen
  /-- Global definition links `M ⟶σ N`. -/
  globalDef : (M N : Node) → Set (sig M ⟶ sig N)
  /-- Local definition links `M ⟶σ N`. -/
  localDef : (M N : Node) → Set (sig M ⟶ sig N)
  /-- Hiding definition links `M ⟶σ,h N`, annotated with `σ : Σᴺ ⟶ Σᴹ`. -/
  hidingDef : (M N : Node) → Set (sig N ⟶ sig M)
  /-- Acyclicity: the relation "there is a definition link from `M` to `N`" is well-founded. -/
  wf : WellFounded fun M N =>
    (globalDef M N).Nonempty ∨ (localDef M N).Nonempty ∨ (hidingDef M N).Nonempty

namespace DevGraph

variable {I} (G : DevGraph.{n} I)

/-- There is a definition link from `M` to `N`. -/
def Link (M N : G.Node) : Prop :=
  (G.globalDef M N).Nonempty ∨ (G.localDef M N).Nonempty ∨ (G.hidingDef M N).Nonempty

theorem wf_link : WellFounded G.Link := G.wf

/-- The reduct `n|σ` of a model along a signature morphism. -/
abbrev reduct {S S' : Sign} (σ : S ⟶ S') (n : (I.obj S').Mod) : (I.obj S).Mod :=
  (I.map σ).mod.obj n

/-- The defining clauses of the model class of `N`, given the model classes of the nodes with
links into `N`. -/
def modelsStep (N : G.Node) (rec : ∀ K, G.Link K N → Set (I.obj (G.sig K)).Mod) :
    Set (I.obj (G.sig N)).Mod :=
  {n | (∀ φ ∈ G.axioms N, (I.obj (G.sig N)).Sat n φ) ∧
    (∀ K σ (h : σ ∈ G.globalDef K N), reduct σ n ∈ rec K (Or.inl ⟨σ, h⟩)) ∧
    (∀ K, ∀ σ ∈ G.localDef K N, ∀ φ ∈ G.axioms K, (I.obj (G.sig K)).Sat (reduct σ n) φ) ∧
    (∀ K σ (h : σ ∈ G.hidingDef K N), ∃ k ∈ rec K (Or.inr (Or.inr ⟨σ, h⟩)), reduct σ k = n)}

/-- The model class `Mod_S(N)` of a node: the `Σᴺ`-models that satisfy the local axioms of `N`,
whose reducts along global links are models of the source nodes, whose reducts along local links
satisfy the local axioms of the source nodes, and which have an expansion along each hiding link
to a model of its source node.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 8 (PDF page 8). -/
def models : (N : G.Node) → Set (I.obj (G.sig N)).Mod :=
  G.wf.fix G.modelsStep

/-- The defining equation of `models`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 8 (PDF page 8). -/
theorem mem_models_iff (N : G.Node) (n : (I.obj (G.sig N)).Mod) :
    n ∈ G.models N ↔ (∀ φ ∈ G.axioms N, (I.obj (G.sig N)).Sat n φ) ∧
      (∀ K, ∀ σ ∈ G.globalDef K N, reduct σ n ∈ G.models K) ∧
      (∀ K, ∀ σ ∈ G.localDef K N, ∀ φ ∈ G.axioms K, (I.obj (G.sig K)).Sat (reduct σ n) φ) ∧
      (∀ K, ∀ σ ∈ G.hidingDef K N, ∃ k ∈ G.models K, reduct σ k = n) := by
  exact (congrArg (fun s => n ∈ s) (WellFounded.fix_eq G.wf G.modelsStep N)).to_iff

/-- Global reachability `M ⟶σ N` along global definition links: either `M = N` and `σ = id`, or
`M ⟶σ' K` is a global link and `K ⟶σ'' N` with `σ = σ' ; σ''`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 5 (PDF page 7). -/
inductive GlobReach : (M N : G.Node) → (G.sig M ⟶ G.sig N) → Prop
  | refl (M : G.Node) : GlobReach M M (𝟙 _)
  | step {M K N : G.Node} {σ' : G.sig M ⟶ G.sig K} {σ'' : G.sig K ⟶ G.sig N} :
      σ' ∈ G.globalDef M K → GlobReach K N σ'' → GlobReach M N (σ' ≫ σ'')

/-- Local reachability `M ⟶σ N`: global reachability, or a local link `M ⟶σ' K` followed by
global reachability `K ⟶σ'' N`, with `σ = σ' ; σ''`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 5 (PDF page 7). -/
def LocReach (M N : G.Node) (σ : G.sig M ⟶ G.sig N) : Prop :=
  G.GlobReach M N σ ∨ ∃ (K : G.Node) (σ' : G.sig M ⟶ G.sig K) (σ'' : G.sig K ⟶ G.sig N),
    σ' ∈ G.localDef M K ∧ G.GlobReach K N σ'' ∧ σ = σ' ≫ σ''

theorem GlobReach.locReach {M N : G.Node} {σ : G.sig M ⟶ G.sig N} (h : G.GlobReach M N σ) :
    G.LocReach M N σ :=
  Or.inl h

section Helpers

variable {G}

/-- Reducts along a composite are iterated reducts. -/
theorem reduct_comp {S₁ S₂ S₃ : Sign} (σ : S₁ ⟶ S₂) (τ : S₂ ⟶ S₃) (n : (I.obj S₃).Mod) :
    reduct (σ ≫ τ) n = reduct σ (reduct τ n) := by
  rw [reduct, Functor.map_comp]
  rfl

/-- The reduct along the identity is the model itself. -/
theorem reduct_id {S : Sign} (n : (I.obj S).Mod) : reduct (𝟙 S) n = n := by
  rw [reduct, CategoryTheory.Functor.map_id]
  rfl

/-- Sentence translation along a composite is iterated translation. -/
theorem map_comp_sen {S₁ S₂ S₃ : Sign} (σ : S₁ ⟶ S₂) (τ : S₂ ⟶ S₃) (ψ : (I.obj S₁).Sen) :
    (I.map (σ ≫ τ)).sen ψ = (I.map τ).sen ((I.map σ).sen ψ) := by
  rw [Functor.map_comp]
  rfl

/-- Global reachability is transitive. -/
theorem GlobReach.trans {M K N : G.Node} {τ : G.sig M ⟶ G.sig K} {ρ : G.sig K ⟶ G.sig N}
    (h₁ : G.GlobReach M K τ) (h₂ : G.GlobReach K N ρ) : G.GlobReach M N (τ ≫ ρ) := by
  induction h₁ with
  | refl M => simpa only [Category.id_comp] using h₂
  | step hσ _ ih =>
    rw [Category.assoc]
    exact GlobReach.step hσ (ih h₂)

/-- A global definition link gives global reachability. -/
theorem GlobReach.of_globalDef {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (hσ : σ ∈ G.globalDef M N) : G.GlobReach M N σ := by
  simpa only [Category.comp_id] using GlobReach.step hσ (GlobReach.refl N)

/-- Local reachability followed by global reachability is local reachability. -/
theorem LocReach.trans_globReach {M K N : G.Node} {τ : G.sig M ⟶ G.sig K}
    {ρ : G.sig K ⟶ G.sig N} (h₁ : G.LocReach M K τ) (h₂ : G.GlobReach K N ρ) :
    G.LocReach M N (τ ≫ ρ) := by
  rcases h₁ with h₁ | ⟨K', σ', σ'', hl, hg, rfl⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inr ⟨K', σ', σ'' ≫ ρ, hl, hg.trans h₂, Category.assoc _ _ _⟩

end Helpers

/-- A node is flattenable when it is not globally reachable from any node with an incoming
hiding link (the paper also excludes free links, which are not modelled here).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 6 (PDF page 7). -/
def Flattenable (N : G.Node) : Prop :=
  ∀ M : G.Node, (∃ K, (G.hidingDef K M).Nonempty) → ∀ σ, ¬ G.GlobReach M N σ

/-- The theory `Th_S(N) = Φᴺ ∪ ⋃_{K ⟶σ N} σ(Φᴷ)` of a node, over local reachability.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 7 (PDF page 7). -/
def theory (N : G.Node) : Set (I.obj (G.sig N)).Sen :=
  G.axioms N ∪
    {φ | ∃ (K : G.Node) (σ : G.sig K ⟶ G.sig N), G.LocReach K N σ ∧
      ∃ ψ ∈ G.axioms K, (I.map σ).sen ψ = φ}

/-- Reducts along global reachability are models of the source node.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Proposition 9(1) (PDF page 8). -/
theorem GlobReach.reduct_mem_models {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (h : G.GlobReach M N σ) {n : (I.obj (G.sig N)).Mod} (hn : n ∈ G.models N) :
    reduct σ n ∈ G.models M := by
  induction h with
  | refl M => rwa [reduct_id]
  | step hσ _ ih =>
    rw [reduct_comp]
    exact ((G.mem_models_iff _ _).1 (ih hn)).2.1 _ _ hσ

/-- Reducts along local reachability satisfy the local axioms of the source node.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Proposition 9(2) (PDF page 8). -/
theorem LocReach.reduct_sat_axioms {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (h : G.LocReach M N σ) {n : (I.obj (G.sig N)).Mod} (hn : n ∈ G.models N) :
    ∀ φ ∈ G.axioms M, (I.obj (G.sig M)).Sat (reduct σ n) φ := by
  rcases h with h | ⟨K, σ', σ'', hl, hg, rfl⟩
  · exact ((G.mem_models_iff _ _).1 (GlobReach.reduct_mem_models G h hn)).1
  · intro φ hφ
    rw [reduct_comp]
    exact ((G.mem_models_iff _ _).1 (GlobReach.reduct_mem_models G hg hn)).2.2.1 _ _ hl φ hφ

/-- Every model of a node is a model of its theory.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Proposition 10(1) (PDF page 8). -/
theorem models_subset_modelsOf_theory (N : G.Node) :
    G.models N ⊆ (I.obj (G.sig N)).modelsOf (G.theory N) := by
  intro n hn φ hφ
  rcases hφ with hφ | ⟨K, σ, hK, ψ, hψ, rfl⟩
  · exact ((G.mem_models_iff _ _).1 hn).1 φ hφ
  · exact ((I.map σ).sat n ψ).2 (LocReach.reduct_sat_axioms G hK hn ψ hψ)

/-- For flattenable nodes the model class is the model class of the theory.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Proposition 10(2) (PDF pages 8–9). -/
theorem models_eq_modelsOf_theory {N : G.Node} (hN : G.Flattenable N) :
    G.models N = (I.obj (G.sig N)).modelsOf (G.theory N) := by
  refine Set.Subset.antisymm (G.models_subset_modelsOf_theory N) ?_
  revert hN
  refine G.wf_link.induction (C := fun N => G.Flattenable N →
    (I.obj (G.sig N)).modelsOf (G.theory N) ⊆ G.models N) N ?_
  intro N ih hN n hn
  rw [G.mem_models_iff]
  refine ⟨fun φ hφ => hn φ (Or.inl hφ), ?_, ?_, ?_⟩
  · intro K σ hσ
    have hK : G.Flattenable K := fun M hM τ hτ =>
      hN M hM (τ ≫ σ) (hτ.trans (GlobReach.of_globalDef hσ))
    refine ih K (Or.inl ⟨σ, hσ⟩) hK ?_
    intro φ hφ
    rcases hφ with hφ | ⟨K', τ, hτ, ψ, hψ, rfl⟩
    · exact ((I.map σ).sat n φ).1
        (hn _ (Or.inr ⟨K, σ, Or.inl (GlobReach.of_globalDef hσ), φ, hφ, rfl⟩))
    · have := hn _ (Or.inr ⟨K', τ ≫ σ,
        hτ.trans_globReach (GlobReach.of_globalDef hσ), ψ, hψ, rfl⟩)
      rw [map_comp_sen] at this
      exact ((I.map σ).sat n _).1 this
  · intro K σ hσ φ hφ
    exact ((I.map σ).sat n φ).1 (hn _ (Or.inr ⟨K, σ,
      Or.inr ⟨N, σ, 𝟙 _, hσ, GlobReach.refl N, (Category.comp_id σ).symm⟩, φ, hφ, rfl⟩))
  · intro K σ hσ
    exact absurd (GlobReach.refl N) (hN N ⟨K, σ, hσ⟩ (𝟙 _))

/-! ### Theorem links -/

/-- `S ⊨ N ⇢σ M`: the global theorem link holds when the `σ`-reduct of every `M`-model is an
`N`-model.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9). -/
def GlobalThm (N M : G.Node) (σ : G.sig N ⟶ G.sig M) : Prop :=
  ∀ m ∈ G.models M, reduct σ m ∈ G.models N

/-- `S ⊨ N ⇢σ M` (local): the `σ`-reduct of every `M`-model satisfies the local axioms of `N`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9). -/
def LocalThm (N M : G.Node) (σ : G.sig N ⟶ G.sig M) : Prop :=
  ∀ m ∈ G.models M, ∀ φ ∈ G.axioms N, (I.obj (G.sig N)).Sat (reduct σ m) φ

/-- `S ⊨ N ⇒ Γ`: every `N`-model satisfies `Γ`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9). -/
def LocalImpl (N : G.Node) (Γ : Set (I.obj (G.sig N)).Sen) : Prop :=
  ∀ n ∈ G.models N, ∀ φ ∈ Γ, (I.obj (G.sig N)).Sat n φ

/-- The hiding theorem link `N ⇢σ,θ,h M`, with `θ : Σ ⟶ Σᴺ` and `σ : Σ ⟶ Σᴹ`: for every
`M`-model `m`, `m|σ` has a `θ`-expansion to an `N`-model.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9). -/
def HidingThm (N M : G.Node) {S : Sign} (θ : S ⟶ G.sig N) (σ : S ⟶ G.sig M) : Prop :=
  ∀ m ∈ G.models M, ∃ n ∈ G.models N, reduct θ n = reduct σ m

/-- A link `M ⟶σ N` is conservative when every `M`-model has a `σ`-expansion to an `N`-model.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
after Definition 11 (PDF page 9). -/
def Conservative (M N : G.Node) (σ : G.sig M ⟶ G.sig N) : Prop :=
  ∀ m ∈ G.models M, ∃ n ∈ G.models N, reduct σ n = m

/-- Global theorem links compose. -/
theorem GlobalThm.trans {N M K : G.Node} {σ : G.sig N ⟶ G.sig M} {τ : G.sig M ⟶ G.sig K}
    (h₁ : G.GlobalThm N M σ) (h₂ : G.GlobalThm M K τ) : G.GlobalThm N K (σ ≫ τ) := by
  intro m hm
  have := h₁ _ (h₂ m hm)
  simpa [reduct, Functor.map_comp] using this

end DevGraph

end Silmaril.Logic.Institution
