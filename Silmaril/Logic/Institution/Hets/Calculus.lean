module

public import Silmaril.Logic.Institution.Hets.Rules
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

/-!
# The proof calculus for development graphs: soundness and relative completeness

The rules of Mossakowski–Autexier–Hutter (§5) and of Mossakowski's habilitation (§§5.6, 6.4) as
an inductive derivability judgement `DevGraph.Derivable R ent G L`: in the development graph
`G`, the theorem link `L` is derivable using the rules in `R`, with `ent` the entailment
system of the underlying logic (used by Basic Inference). Rules may change the graph: the
premise of Theorem-Hide-Shift lives in an extension of `G`, and Faithful-Extension moves
judgements between `G` and its extensions.

* `ThmLink G`: the judgements: global, local and hiding theorem links, conservativity of a link
  and local implications; `ThmLink.Holds` is their semantics (`Hets/DevGraph.lean`).
* `Rule`: names of rules, so that sub-calculi can be singled out (`Rule.decomposition`).
* `Derivable.sound`: **soundness** of the whole calculus for a sound entailment system
  (Mossakowski–Autexier–Hutter, Propositions 12 and 13; habilitation, Theorem 6.26, soundness).
* `derivable_univ_of_globalThm`: the **full** calculus (all rules, including Borrowing and
  the conservativity oracle) is trivially complete, without any hypothesis: Faithful-Extension
  adds a copy `N'` of `N` with links `N ⟶𝟙 N'` and `M ⟶σ N'`, the oracle makes `N ⟶𝟙 N'`
  conservative exactly when `M ⇢σ N` holds, and Borrowing closes the goal. So completeness of
  the full rule set says nothing about Theorem 16.
* `Rule.mah`: the rule set of Mossakowski–Autexier–Hutter's completeness proof (decomposition,
  Theorem-Hide-Shift, Hide-Theorem-Shift, Cons-Shift, Cons-Composition, the oracle and
  Faithful-Extension), *without* Borrowing. The relative completeness proof uses
  Theorem-Hide-Shift and its cocone for global theorem links into non-flattenable nodes.
* `derivable_of_globalThm`: **relative completeness** (Mossakowski–Autexier–Hutter,
  Theorem 16) for `Rule.mah`: for a complete entailment system, a weakly semi-exact logic with
  pushouts of signatures, a weakly amalgamable cocone for the unfolding below the target node
  and the oracle for conservative extensions, every global theorem link that holds is
  derivable. The standing assumptions of the source ("`Sign` has finite colimits, and `LOG`
  admits finite weak amalgamation") imply these side conditions for finite graphs
  (`derivable_of_globalThm_of_finite`). Our Hide-Theorem-Shift is more general than the
  source's (it does not ask for a definition link `N ⟶θ' N'`), so `Rule.mah` is at least as
  strong as the source's rule set; the completeness proof only applies the rule with such a
  definition link present.
* `derivable_decomposition_of_flattenable`: Corollary 17: between flattenable nodes the
  decomposition rules alone are complete.

No interpolation hypothesis appears: Mossakowski–Autexier–Hutter replace Borzyszkowski's use
of Craig interpolation (for a calculus without an oracle) by the oracle for conservativity and
Theorem-Hide-Shift (§9, PDF page 37).
A Borzyszkowski-style completeness theorem without the oracle, under Craig interpolation, is
not formalized here.

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`: §5 (PDF
  pages 10–15: rules, Propositions 12–13); §7 (PDF pages 16–18: Proposition 14, Lemma 15,
  Theorem 16, Corollary 17).
* `mossakowski-2005-habilitation-hets` in `references.bib`: §5.6 (printed pages 137–146,
  PDF pages 139–148), Theorem 5.23 (printed page 146, PDF page 148); §6.4, Figure 6.1 and
  Theorem 6.26 (printed pages 162–163, PDF pages 164–165).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits

universe n u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace DevGraph

variable (G : DevGraph.{n} I)

/-- Proof goals over a development graph: theorem links of the three kinds, conservativity of a
link, and local implications.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9); `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6
(printed page 137, PDF page 139: "judgements of the form `DG ⊢ L`, where … `L` is a theorem
link (of any kind)"). -/
inductive ThmLink : Type (max n u v w)
  /-- The global theorem link `N ⇢σ M`. -/
  | glob (N M : G.Node) (σ : G.sig N ⟶ G.sig M)
  /-- The local theorem link `N ⇢σ M`. -/
  | loc (N M : G.Node) (σ : G.sig N ⟶ G.sig M)
  /-- The hiding theorem link `N ⇢σ,θ,h M`. -/
  | hide (N M : G.Node) {S : Sign} (θ : S ⟶ G.sig N) (σ : S ⟶ G.sig M)
  /-- Conservativity of `M ⇢σ N`. -/
  | cons (M N : G.Node) (σ : G.sig M ⟶ G.sig N)
  /-- The local implication `N ⇒ Γ`. -/
  | impl (N : G.Node) (Γ : Set (I.obj (G.sig N)).Sen)

variable {G}

/-- The semantics of a proof goal.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9). -/
def ThmLink.Holds : G.ThmLink → Prop
  | .glob N M σ => G.GlobalThm N M σ
  | .loc N M σ => G.LocalThm N M σ
  | .hide N M θ σ => G.HidingThm N M θ σ
  | .cons M N σ => G.Conservative M N σ
  | .impl N Γ => G.LocalImpl N Γ

/-- A proof goal over `G` as a proof goal over an extension of `G`. -/
def ThmLink.lift (E : G.NewNode) : G.ThmLink → (G.addNode E).ThmLink
  | .glob N M σ => .glob (some N) (some M) σ
  | .loc N M σ => .loc (some N) (some M) σ
  | .hide N M θ σ => .hide (some N) (some M) θ σ
  | .cons M N σ => .cons (some M) (some N) σ
  | .impl N Γ => .impl (some N) Γ

/-- Faithful extensions preserve and reflect the semantics of proof goals.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.1, rule
Faithful-Extension (printed pages 137–138, PDF pages 139–140). -/
theorem ThmLink.holds_lift_iff (E : G.NewNode) (L : G.ThmLink) : (L.lift E).Holds ↔ L.Holds := by
  cases L <;>
    simp only [ThmLink.lift, ThmLink.Holds, GlobalThm, LocalThm, HidingThm, Conservative,
      LocalImpl, models_addNode_some] <;>
    rfl

/-- The rules of the calculus.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5 (PDF
pages 10–15); `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6 (printed
pages 137–141, PDF pages 139–143) and §6.4, Figure 6.1 (printed page 162, PDF page 164). -/
inductive Rule
  | globDecomposition
  | subsumption
  | locDecomposition₁
  | locDecomposition₂
  | localInference
  | basicInference
  | theoremHideShift
  | hideTheoremShift
  | borrowing
  | consShift
  | consComposition
  | consOracle
  | modelExpansion
  | localBorrowing
  | composition
  | faithfulExtension
  deriving DecidableEq

/-- The decomposition rules of §5.2 of Mossakowski–Autexier–Hutter.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF pages 13–14). -/
def Rule.decomposition : Set Rule :=
  {.globDecomposition, .subsumption, .locDecomposition₁, .locDecomposition₂, .localInference,
    .basicInference}

/-- The rules used in the relative completeness proof of Mossakowski–Autexier–Hutter
(Theorem 16): the decomposition rules, Theorem-Hide-Shift, Hide-Theorem-Shift, Cons-Shift,
Cons-Composition, the conservativity oracle and Faithful-Extension. Borrowing,
Model-Expansion, Local Borrowing and Composition (the heterogeneous rules of the
habilitation, §6.4) are excluded: with Borrowing and the oracle the calculus is trivially
complete (`derivable_univ_of_globalThm`).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5 and
the proof of Theorem 16 (PDF pages 10–18). -/
def Rule.mah : Set Rule :=
  Rule.decomposition ∪
    {.theoremHideShift, .hideTheoremShift, .consShift, .consComposition, .consOracle,
      .faithfulExtension}

variable (R : Set Rule) (ent : ∀ S : Sign, Set (I.obj S).Sen → (I.obj S).Sen → Prop)

/-- `Derivable R ent G L`: the proof goal `L` over `G` is derivable with the rules in `R`, where
`ent` is the entailment system of the logic.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5 (PDF
pages 10–15); `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6 (printed pages
137–141, PDF pages 139–143) and §6.4, Figure 6.1 (printed page 162, PDF page 164). The
conservativity oracle is the rule `consOracle`. -/
inductive Derivable : (G : DevGraph.{n} I) → G.ThmLink → Prop
  | globDecomposition {G : DevGraph.{n} I} {N M : G.Node} (σ : G.sig N ⟶ G.sig M)
      (hr : Rule.globDecomposition ∈ R)
      (h₁ : ∀ K τ, G.LocReach K N τ → Derivable G (.loc K M (τ ≫ σ)))
      (h₂ : ∀ L K (θ : G.sig K ⟶ G.sig L) τ, θ ∈ G.hidingDef L K → G.GlobReach K N τ →
        Derivable G (.hide L M θ (τ ≫ σ))) :
      Derivable G (.glob N M σ)
  | subsumption {G : DevGraph.{n} I} {N M : G.Node} {σ : G.sig N ⟶ G.sig M}
      (hr : Rule.subsumption ∈ R) (h : G.GlobReach N M σ) : Derivable G (.glob N M σ)
  | locDecomposition₁ {G : DevGraph.{n} I} {K L M : G.Node} {σ : G.sig K ⟶ G.sig L}
      {σ' : G.sig L ⟶ G.sig M} {σ'' : G.sig K ⟶ G.sig M} (hr : Rule.locDecomposition₁ ∈ R)
      (h : Derivable G (.loc K L σ)) (hL : G.GlobReach L M σ')
      (heq : (I.map σ'').sen '' G.axioms K = (I.map σ').sen '' ((I.map σ).sen '' G.axioms K)) :
      Derivable G (.loc K M σ'')
  | locDecomposition₂ {G : DevGraph.{n} I} {N M : G.Node} {σ σ' : G.sig N ⟶ G.sig M}
      (hr : Rule.locDecomposition₂ ∈ R) (h : G.LocReach N M σ')
      (heq : (I.map σ).sen '' G.axioms N = (I.map σ').sen '' G.axioms N) :
      Derivable G (.loc N M σ)
  | localInference {G : DevGraph.{n} I} {M N : G.Node} (σ : G.sig M ⟶ G.sig N)
      (hr : Rule.localInference ∈ R)
      (h : Derivable G (.impl N ((I.map σ).sen '' G.axioms M))) : Derivable G (.loc M N σ)
  | basicInference {G : DevGraph.{n} I} {N : G.Node} {Γ : Set (I.obj (G.sig N)).Sen}
      (hr : Rule.basicInference ∈ R) (h : ∀ φ ∈ Γ, ent (G.sig N) (G.theory N) φ) :
      Derivable G (.impl N Γ)
  | theoremHideShift {G : DevGraph.{n} I} {K N : G.Node} {σ : G.sig K ⟶ G.sig N}
      (c : G.UCocone N) (hr : Rule.theoremHideShift ∈ R) (hc : c.WeaklyAmalgamable)
      (h : Derivable (G.addNode (G.thsNode c)) (.glob (some K) none (σ ≫ c.μ (UObj.root G N)))) :
      Derivable G (.glob K N σ)
  | hideTheoremShift {G : DevGraph.{n} I} {K' N N' : G.Node} {S : Sign} {θ : S ⟶ G.sig K'}
      {σ : S ⟶ G.sig N} {σ' : G.sig K' ⟶ G.sig N'} {θ' : G.sig N ⟶ G.sig N'}
      (hr : Rule.hideTheoremShift ∈ R) (hcomm : θ ≫ σ' = σ ≫ θ')
      (hcons : Derivable G (.cons N N' θ')) (h : Derivable G (.glob K' N' σ')) :
      Derivable G (.hide K' N θ σ)
  | borrowing {G : DevGraph.{n} I} {K K' N N' : G.Node} {σ : G.sig K ⟶ G.sig N}
      {θ : G.sig K ⟶ G.sig K'} {σ' : G.sig K' ⟶ G.sig N'} {θ' : G.sig N ⟶ G.sig N'}
      (hr : Rule.borrowing ∈ R) (hcomm : θ ≫ σ' = σ ≫ θ') (hθ : Derivable G (.glob K K' θ))
      (hcons : Derivable G (.cons N N' θ')) (h : Derivable G (.glob K' N' σ')) :
      Derivable G (.glob K N σ)
  | consShift {G : DevGraph.{n} I} {K K' N N' : G.Node} {σ : G.sig K ⟶ G.sig N}
      {θ : G.sig K ⟶ G.sig K'} {σ' : G.sig K' ⟶ G.sig N'} {θ' : G.sig N ⟶ G.sig N'}
      (hr : Rule.consShift ∈ R) (hcomm : θ ≫ σ' = σ ≫ θ')
      (hamalg : WeakModelAmalgamation I θ σ σ' θ')
      (hiso : G.IsolatedBy N' (G.linkFrom₂ N θ' K' σ'))
      (hcons : Derivable G (.cons K K' θ)) (hσ : Derivable G (.glob K N σ)) :
      Derivable G (.cons N N' θ')
  | consComposition {G : DevGraph.{n} I} {K N N' : G.Node} {σ : G.sig K ⟶ G.sig N}
      {θ : G.sig N ⟶ G.sig N'} (hr : Rule.consComposition ∈ R)
      (h₁ : Derivable G (.cons K N σ)) (h₂ : Derivable G (.cons N N' θ)) :
      Derivable G (.cons K N' (σ ≫ θ))
  | consOracle {G : DevGraph.{n} I} {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
      (hr : Rule.consOracle ∈ R) (h : G.Conservative M N σ) : Derivable G (.cons M N σ)
  | modelExpansion {G : DevGraph.{n} I} {N K : G.Node} {σ : G.sig N ⟶ G.sig K}
      (hr : Rule.modelExpansion ∈ R) (hσ : Corridor.ModelExpansive (I.map σ))
      (hiso : G.IsolatedBy K (G.linkFrom N σ)) : Derivable G (.cons N K σ)
  | localBorrowing {G : DevGraph.{n} I} {N N' K K' : G.Node} {σ : G.sig N ⟶ G.sig K}
      {θ : G.sig N ⟶ G.sig N'} {σ' : G.sig N' ⟶ G.sig K'} {θ' : G.sig K ⟶ G.sig K'}
      (hr : Rule.localBorrowing ∈ R) (hcomm : θ ≫ σ' = σ ≫ θ')
      (hax : (I.map θ).sen '' G.axioms N ⊆ G.axioms N') (hcons : Derivable G (.cons K K' θ'))
      (h : Derivable G (.loc N' K' σ')) : Derivable G (.loc N K σ)
  | composition {G : DevGraph.{n} I} {N K P : G.Node} {σ : G.sig N ⟶ G.sig K}
      {θ : G.sig K ⟶ G.sig P} (hr : Rule.composition ∈ R) (h₁ : Derivable G (.loc N K σ))
      (h₂ : Derivable G (.glob K P θ)) : Derivable G (.loc N P (σ ≫ θ))
  | faithfulExtension {G : DevGraph.{n} I} {L : G.ThmLink} (E : G.NewNode)
      (hr : Rule.faithfulExtension ∈ R) (h : Derivable (G.addNode E) (L.lift E)) :
      Derivable G L

variable {R ent}

/-- **Soundness** of the calculus: for a sound entailment system, every derivable proof goal
holds.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`,
Propositions 12 and 13 (PDF pages 12–15);
`mossakowski-2005-habilitation-hets` in `references.bib`,
§5.6 (printed pages 137–141, PDF pages 139–143) and Theorem 6.26, soundness (printed pages
162–163, PDF pages 164–165). -/
theorem Derivable.sound (hent : ∀ S Γ φ, ent S Γ φ → (I.obj S).Entails Γ φ)
    {G : DevGraph.{n} I} {L : G.ThmLink} (h : Derivable R ent G L) : L.Holds := by
  induction h with
  | globDecomposition σ _ _ _ ih₁ ih₂ => exact DevGraph.globDecomposition _ σ ih₁ ih₂
  | subsumption _ h => exact DevGraph.subsumption _ h
  | locDecomposition₁ _ _ hL heq ih => exact DevGraph.locDecomposition₁ _ ih hL heq
  | locDecomposition₂ _ h heq => exact DevGraph.locDecomposition₂ _ h heq
  | localInference σ _ _ ih => exact DevGraph.localInference _ σ ih
  | basicInference _ h => exact DevGraph.basicInference _ fun φ hφ => hent _ _ _ (h φ hφ)
  | theoremHideShift c _ hc _ ih => exact DevGraph.theoremHideShift _ c hc ih
  | hideTheoremShift _ hcomm _ _ ihc ih => exact DevGraph.hideTheoremShift _ hcomm ihc ih
  | borrowing _ hcomm _ _ _ ihθ ihc ih => exact DevGraph.borrowing _ hcomm ihθ ihc ih
  | consShift _ hcomm hamalg hiso _ _ ihc ihσ =>
    exact DevGraph.consShift _ hcomm hamalg hiso ihc ihσ
  | consComposition _ _ _ ih₁ ih₂ => exact DevGraph.consComposition _ ih₁ ih₂
  | consOracle _ h => exact h
  | modelExpansion _ hσ hiso => exact DevGraph.modelExpansion _ hσ hiso
  | localBorrowing _ hcomm hax _ _ ihc ih => exact DevGraph.localBorrowing _ hcomm hax ihc ih
  | composition _ _ _ ih₁ ih₂ => exact DevGraph.composition _ ih₁ ih₂
  | faithfulExtension E _ _ ih => exact (ThmLink.holds_lift_iff E _).1 ih

/-! ### Helpers for completeness -/

/-- A global theorem link `M ⇢σ P` that holds gives the local theorem links `K ⇢(τ;σ) P` for
every `K` locally reaching `M` via `τ`. -/
theorem GlobalThm.localThm_of_locReach {M P K : G.Node} {σ : G.sig M ⟶ G.sig P}
    {τ : G.sig K ⟶ G.sig M} (h : G.GlobalThm M P σ) (hK : G.LocReach K M τ) :
    G.LocalThm K P (τ ≫ σ) := by
  intro m hm φ hφ
  rw [reduct_comp]
  exact LocReach.reduct_sat_axioms G hK (h m hm) φ hφ

/-- A global theorem link `M ⇢σ P` that holds gives the hiding theorem links
`L ⇢(τ;σ),θ,h P` for every hiding link `L ⟶θ,h K` into a node `K` globally reaching `M` via
`τ`. -/
theorem GlobalThm.hidingThm_of_hidingDef {M P K L : G.Node} {σ : G.sig M ⟶ G.sig P}
    {τ : G.sig K ⟶ G.sig M} {θ : G.sig K ⟶ G.sig L} (h : G.GlobalThm M P σ)
    (hK : G.GlobReach K M τ) (hθ : θ ∈ G.hidingDef L K) : G.HidingThm L P θ (τ ≫ σ) := by
  intro m hm
  obtain ⟨k, hk, he⟩ :=
    ((G.mem_models_iff K _).1 (GlobReach.reduct_mem_models G hK (h m hm))).2.2.2 L θ hθ
  exact ⟨k, hk, by rw [he, reduct_comp]⟩

/-- For a complete entailment system, Local Inference and Basic Inference derive every local
theorem link into a flattenable node that holds. -/
theorem Derivable.loc_of_flattenable (hent : ∀ S Γ φ, (I.obj S).Entails Γ φ → ent S Γ φ)
    (hli : Rule.localInference ∈ R) (hbi : Rule.basicInference ∈ R) {K P : G.Node}
    {τ : G.sig K ⟶ G.sig P} (hP : G.Flattenable P) (h : G.LocalThm K P τ) :
    Derivable R ent G (.loc K P τ) := by
  refine .localInference τ hli (.basicInference hbi fun φ hφ => hent _ _ _ ?_)
  intro n hn
  have hn' : n ∈ G.models P := by
    rw [G.models_eq_modelsOf_theory hP]
    exact hn
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ((I.map τ).sat n ψ).2 (h n hn' ψ hψ)

/-- The new isolated node over a pushout of `θ : S ⟶ Σᴸ` and `ρ : S ⟶ Σᴾ`, with global
definition links `L ⟶inl new` and `P ⟶inr new` (the node `N'` of the completeness proof of
Mossakowski–Autexier–Hutter, Theorem 16). -/
noncomputable def pushoutNode [HasPushouts Sign] {L P : G.Node} {S : Sign} (θ : S ⟶ G.sig L)
    (ρ : S ⟶ G.sig P) : G.NewNode where
  sig := pushout θ ρ
  axioms := ∅
  globalDef K := {τ | ∃ h : K = L, τ = eqToHom (congrArg G.sig h) ≫ pushout.inl θ ρ} ∪
    {τ | ∃ h : K = P, τ = eqToHom (congrArg G.sig h) ≫ pushout.inr θ ρ}
  localDef _ := ∅
  hidingDef _ := ∅

/-- For a weakly semi-exact logic with pushouts, Faithful-Extension, Hide-Theorem-Shift, the
conservativity oracle and Subsumption derive every hiding theorem link that holds: add the
isolated node `N'` over the pushout of `θ` and `ρ`, derive `L ⇢inl N'` by Subsumption and
the conservativity of `P ⟶inr N'` by the oracle (a `P`-model and an expansion of its reduct
to an `L`-model amalgamate).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §7,
proof of Theorem 16 (PDF pages 17–18). -/
theorem Derivable.hide_of_hidingThm [HasPushouts Sign] (hI : WeaklySemiExact I)
    (hhts : Rule.hideTheoremShift ∈ R) (hco : Rule.consOracle ∈ R)
    (hsub : Rule.subsumption ∈ R) (hfe : Rule.faithfulExtension ∈ R) {L P : G.Node} {S : Sign}
    {θ : S ⟶ G.sig L} {ρ : S ⟶ G.sig P} (h : G.HidingThm L P θ ρ) :
    Derivable R ent G (.hide L P θ ρ) := by
  refine .faithfulExtension (L := .hide L P θ ρ) (pushoutNode θ ρ) hfe ?_
  show Derivable R ent (G.addNode (pushoutNode θ ρ)) (.hide (some L) (some P) θ ρ)
  refine @Derivable.hideTheoremShift _ _ _ R ent (G.addNode (pushoutNode θ ρ)) (some L)
    (some P) none S θ ρ (pushout.inl θ ρ) (pushout.inr θ ρ) hhts pushout.condition
    (.consOracle hco ?_) (.subsumption hsub (GlobReach.of_globalDef (Or.inl ⟨rfl, by simp⟩)))
  intro m hm
  rw [models_addNode_some] at hm
  obtain ⟨l, hl, hle⟩ := h m hm
  obtain ⟨n, hn₁, hn₂⟩ := hI _ _ _ _ (IsPushout.of_hasPushout θ ρ) l m hle
  refine ⟨n, (G.mem_models_addNode_none (pushoutNode θ ρ) n).2
    ⟨fun _ h => False.elim h, ?_, fun _ _ h => False.elim h,
      fun _ _ h => False.elim h⟩, hn₂⟩
  rintro K τ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · simp only [eqToHom_refl, Category.id_comp]
    rw [← hn₁] at hl
    exact hl
  · simp only [eqToHom_refl, Category.id_comp]
    rw [← hn₂] at hm
    exact hm

/-- Finite weak amalgamation gives weak semi-exactness: a pushout square is the colimit of a
span, a finite diagram.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §3 (PDF
page 5). -/
theorem FiniteWeakAmalgamation.weaklySemiExact (hI : FiniteWeakAmalgamation I) :
    WeaklySemiExact I := by
  intro S S₁ S₂ S' f₁ f₂ g₁ g₂ hpo M₁ M₂ he
  obtain ⟨m, hm⟩ := hI WalkingSpan (span f₁ f₂) hpo.cocone hpo.isColimit
    (fun j => match j with
      | none => reduct f₁ M₁
      | some .left => M₁
      | some .right => M₂) (by
      intro j j' l
      cases l with
      | id =>
        show reduct ((span f₁ f₂).map (𝟙 _)) _ = _
        rw [CategoryTheory.Functor.map_id]
        exact reduct_id _
      | init j₀ =>
        cases j₀
        · rfl
        · exact he.symm)
  exact ⟨m, hm (some .left), hm (some .right)⟩

/-- The node `N'` of the trivial completeness proof: signature `Σᴺ`, no axioms, global
definition links `N ⟶𝟙 N'` and `M ⟶σ N'`. -/
def borrowNode {M N : G.Node} (σ : G.sig M ⟶ G.sig N) : G.NewNode where
  sig := G.sig N
  axioms := ∅
  globalDef K := {τ | ∃ h : K = N, τ = eqToHom (congrArg G.sig h)} ∪
    {τ | ∃ h : K = M, τ = eqToHom (congrArg G.sig h) ≫ σ}
  localDef _ := ∅
  hidingDef _ := ∅

/-- **Trivial completeness of the full calculus**: with all rules, every global theorem link
that holds is derivable, for any entailment system and any logic. Proof: Faithful-Extension
adds a node `N'` with signature `Σᴺ`, no axioms and global definition links `N ⟶𝟙 N'` and
`M ⟶σ N'`; there `N ⟶𝟙 N'` is conservative (an `N`-model is an `N'`-model because its
`σ`-reduct is an `M`-model, by `h`), so the oracle derives it; Subsumption derives `M ⇢𝟙 M`
and `M ⇢σ N'`, and Borrowing (`𝟙 ; σ = σ ; 𝟙`) derives `M ⇢σ N`.

This is why the relative completeness theorem `derivable_of_globalThm` is stated for
`Rule.mah`, which excludes Borrowing. In the rendered habilitation the Borrowing premise is
likewise a `cons` theorem link (printed page 140, PDF page 142) and Faithful-Extension is a
rule (printed page 137, PDF page 139), so the observation applies to the source too. -/
theorem derivable_univ_of_globalThm {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (h : G.GlobalThm M N σ) : Derivable Set.univ ent G (.glob M N σ) := by
  refine .faithfulExtension (L := .glob M N σ) (borrowNode σ) (Set.mem_univ _) ?_
  show Derivable Set.univ ent (G.addNode (borrowNode σ)) (.glob (some M) (some N) σ)
  refine @Derivable.borrowing _ _ _ Set.univ ent (G.addNode (borrowNode σ)) (some M) (some M)
    (some N) none σ (𝟙 (G.sig M)) σ (𝟙 (G.sig N)) (Set.mem_univ _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (.subsumption (Set.mem_univ _) (GlobReach.refl _)) (.consOracle (Set.mem_univ _) ?_)
    (.subsumption (Set.mem_univ _) (GlobReach.of_globalDef (Or.inr ⟨rfl, by simp⟩)))
  intro m hm
  rw [models_addNode_some] at hm
  refine ⟨m, (G.mem_models_addNode_none (borrowNode σ) m).2
    ⟨fun _ h => False.elim h, ?_, fun _ _ h => False.elim h,
      fun _ _ h => False.elim h⟩, reduct_id m⟩
  rintro K τ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · simp only [eqToHom_refl]
    exact (congrArg (· ∈ G.models K) (reduct_id (S := G.sig K) m)).mpr hm
  · simp only [eqToHom_refl, Category.id_comp]
    exact h m hm

/-- **Relative completeness** (Theorem 16 of Mossakowski–Autexier–Hutter): if the entailment
system is complete, pushouts of signatures exist and are weakly amalgamable, and the unfolding
below `N` has a weakly amalgamable cocone, then every global theorem link `M ⇢σ N` that holds
is derivable with the rules of `Rule.mah` (in particular with the conservativity oracle, but
without Borrowing).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §7,
Theorem 16 and its proof (PDF pages 17–18);
`mossakowski-2005-habilitation-hets` in `references.bib`,
§5.6.5, Theorem 5.23 (printed page 146, PDF page 148). -/
theorem derivable_of_globalThm (hent : ∀ S Γ φ, (I.obj S).Entails Γ φ → ent S Γ φ)
    [HasPushouts Sign] (hI : WeaklySemiExact I) {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (c : G.UCocone N) (hc : c.WeaklyAmalgamable) (h : G.GlobalThm M N σ) :
    Derivable Rule.mah ent G (.glob M N σ) := by
  refine .theoremHideShift c (by simp [Rule.mah, Rule.decomposition]) hc ?_
  have h' : (G.addNode (G.thsNode c)).GlobalThm (some M) (some N) σ :=
    (ThmLink.holds_lift_iff (G.thsNode c) (.glob M N σ)).2 h
  have hC : (G.addNode (G.thsNode c)).GlobalThm (some M) none (σ ≫ c.μ (UObj.root G N)) :=
    GlobalThm.trans _ h' (G.globalThm_thsNode c)
  refine .globDecomposition _ (by simp [Rule.mah, Rule.decomposition])
    (fun K τ hK => ?_) (fun L K θ τ hθ hK => ?_)
  · exact Derivable.loc_of_flattenable hent (by simp [Rule.mah, Rule.decomposition])
      (by simp [Rule.mah, Rule.decomposition]) (G.flattenable_thsNode c)
      (hC.localThm_of_locReach hK)
  · exact Derivable.hide_of_hidingThm hI (by simp [Rule.mah, Rule.decomposition]) (by simp [Rule.mah, Rule.decomposition])
      (by simp [Rule.mah, Rule.decomposition]) (by simp [Rule.mah, Rule.decomposition])
      (hC.hidingThm_of_hidingDef hK hθ)

/-- Relative completeness (for `Rule.mah`) under the standing assumptions of
Mossakowski–Autexier–Hutter: a complete entailment system, finite colimits of signatures and finite weak amalgamation, for a
finite graph with finitely many links between any two nodes.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §3 (PDF
page 5: the standing assumptions) and §7, Theorem 16 (PDF pages 17–18). -/
theorem derivable_of_globalThm_of_finite (hent : ∀ S Γ φ, (I.obj S).Entails Γ φ → ent S Γ φ)
    [HasFiniteColimits Sign] (hfin : FiniteWeakAmalgamation I) [Finite G.Node]
    (hg : ∀ K M, (G.globalDef K M).Finite) (hl : ∀ K M, (G.localDef K M).Finite)
    (hh : ∀ K M, (G.hidingDef K M).Finite) {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (h : G.GlobalThm M N σ) : Derivable Rule.mah ent G (.glob M N σ) := by
  obtain ⟨c, hc⟩ :=
    G.exists_weaklyAmalgamable_uCocone hfin (G.unfoldingFinite_of_finite hg hl hh N)
  exact derivable_of_globalThm hent (FiniteWeakAmalgamation.weaklySemiExact hfin) c hc h

/-- **Corollary 17** of Mossakowski–Autexier–Hutter: for a complete entailment system, the
decomposition rules are complete for global theorem links between flattenable nodes.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §7,
Corollary 17 (PDF page 18). -/
theorem derivable_decomposition_of_flattenable
    (hent : ∀ S Γ φ, (I.obj S).Entails Γ φ → ent S Γ φ) {M N : G.Node} {σ : G.sig M ⟶ G.sig N}
    (hM : G.Flattenable M) (hN : G.Flattenable N) (h : G.GlobalThm M N σ) :
    Derivable Rule.decomposition ent G (.glob M N σ) := by
  refine .globDecomposition σ (by simp [Rule.decomposition]) (fun K τ hK => ?_)
    (fun L K θ τ hθ hK => ?_)
  · exact Derivable.loc_of_flattenable hent (by simp [Rule.decomposition])
      (by simp [Rule.decomposition]) hN (h.localThm_of_locReach hK)
  · exact absurd hK (hM K ⟨L, θ, hθ⟩ τ)

/-- Derivability is monotone in the set of rules. -/
theorem Derivable.mono {R R' : Set Rule} (hRR' : R ⊆ R') {G : DevGraph.{n} I} {L : G.ThmLink}
    (h : Derivable R ent G L) : Derivable R' ent G L := by
  induction h with
  | globDecomposition σ hr _ _ ih₁ ih₂ => exact .globDecomposition σ (hRR' hr) ih₁ ih₂
  | subsumption hr h => exact .subsumption (hRR' hr) h
  | locDecomposition₁ hr _ hL heq ih => exact .locDecomposition₁ (hRR' hr) ih hL heq
  | locDecomposition₂ hr h heq => exact .locDecomposition₂ (hRR' hr) h heq
  | localInference σ hr _ ih => exact .localInference σ (hRR' hr) ih
  | basicInference hr h => exact .basicInference (hRR' hr) h
  | theoremHideShift c hr hc _ ih => exact .theoremHideShift c (hRR' hr) hc ih
  | hideTheoremShift hr hcomm _ _ ihc ih => exact .hideTheoremShift (hRR' hr) hcomm ihc ih
  | borrowing hr hcomm _ _ _ ihθ ihc ih => exact .borrowing (hRR' hr) hcomm ihθ ihc ih
  | consShift hr hcomm hamalg hiso _ _ ihc ihσ =>
    exact .consShift (hRR' hr) hcomm hamalg hiso ihc ihσ
  | consComposition hr _ _ ih₁ ih₂ => exact .consComposition (hRR' hr) ih₁ ih₂
  | consOracle hr h => exact .consOracle (hRR' hr) h
  | modelExpansion hr hσ hiso => exact .modelExpansion (hRR' hr) hσ hiso
  | localBorrowing hr hcomm hax _ _ ihc ih => exact .localBorrowing (hRR' hr) hcomm hax ihc ih
  | composition hr _ _ ih₁ ih₂ => exact .composition (hRR' hr) ih₁ ih₂
  | faithfulExtension E hr _ ih => exact .faithfulExtension E (hRR' hr) ih

end DevGraph

end Silmaril.Logic.Institution
