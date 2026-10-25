module

public import Silmaril.Logic.Institution.Hets.DevGraph

@[expose] public section

/-!
# Soundness of the development-graph decomposition rules

The proof rules of §5.2 of Mossakowski–Autexier–Hutter for development graphs with hiding
(`Hets/DevGraph.lean`), with their soundness (Proposition 13): Glob-Decomposition, Subsumption,
Loc-Decomposition I and II, Local Inference and Basic Inference. Basic Inference is stated with
semantic consequence in place of a sound entailment system. Also the heterogeneous rule
Model-Expansion (Mossakowski's habilitation, Figure 6.1): a global link along a model-expansive
corridor into an isolated node is conservative.

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`: §5.2 and
  Proposition 13 (PDF pages 13–15).
* `mossakowski-2005-habilitation-hets` in `references.bib`: §6.4, Figure 6.1 and
  Theorem 6.26 (printed pages 161–162, PDF pages 163–164).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe n u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace DevGraph

variable (G : DevGraph.{n} I)

/-! ### Soundness of the decomposition rules -/

/-- **Glob-Decomposition** is sound: a global theorem link `N ⇢σ M` follows from the local
theorem links `K ⇢(τ;σ) M` for every `K` locally reaching `N` via `τ`, and the hiding theorem
links `L ⇢(τ;σ),θ,h M` for every hiding link `L ⟶θ,h K` into a node `K` globally reaching `N`
via `τ`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 13) and Proposition 13 (PDF page 14). -/
theorem globDecomposition {N M : G.Node} (σ : G.sig N ⟶ G.sig M)
    (h₁ : ∀ K τ, G.LocReach K N τ → G.LocalThm K M (τ ≫ σ))
    (h₂ : ∀ L K (θ : G.sig K ⟶ G.sig L) τ, θ ∈ G.hidingDef L K → G.GlobReach K N τ →
      G.HidingThm L M θ (τ ≫ σ)) :
    G.GlobalThm N M σ := by
  intro m hm
  have H : ∀ K τ, G.GlobReach K N τ → reduct (τ ≫ σ) m ∈ G.models K := by
    intro K
    refine G.wf.induction
      (C := fun K => ∀ τ, G.GlobReach K N τ → reduct (τ ≫ σ) m ∈ G.models K) K ?_
    intro K ih τ hτ
    rw [mem_models_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact h₁ K τ (GlobReach.locReach G hτ) m hm
    · intro K' ρ hρ
      have := ih K' (Or.inl ⟨ρ, hρ⟩) (ρ ≫ τ) (GlobReach.step hρ hτ)
      simpa [reduct, Functor.map_comp] using this
    · intro K' ρ hρ φ hφ
      have := h₁ K' (ρ ≫ τ) (Or.inr ⟨K, ρ, τ, hρ, hτ, rfl⟩) m hm φ hφ
      simpa [reduct, Functor.map_comp] using this
    · intro K' θ hθ
      exact h₂ K' K θ τ hθ hτ m hm
  simpa using H N (𝟙 _) (GlobReach.refl N)

/-- **Subsumption** is sound: global reachability `N ⟶σ M` proves the global theorem link
`N ⇢σ M`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 13) and Proposition 13 (PDF page 14). -/
theorem subsumption {N M : G.Node} {σ : G.sig N ⟶ G.sig M} (h : G.GlobReach N M σ) :
    G.GlobalThm N M σ :=
  fun _ hm => GlobReach.reduct_mem_models G h hm

/-- **Loc-Decomposition I** is sound: from `K ⇢σ L` (local), `L ⟶σ' M` (global reachability)
and `σ''(Φᴷ) = σ'(σ(Φᴷ))` infer `K ⇢σ'' M` (local).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 13) and Proposition 13 (PDF page 14). -/
theorem locDecomposition₁ {K L M : G.Node} {σ : G.sig K ⟶ G.sig L} {σ' : G.sig L ⟶ G.sig M}
    {σ'' : G.sig K ⟶ G.sig M} (h : G.LocalThm K L σ) (hL : G.GlobReach L M σ')
    (heq : (I.map σ'').sen '' G.axioms K = (I.map σ').sen '' ((I.map σ).sen '' G.axioms K)) :
    G.LocalThm K M σ'' := by
  intro m hm φ hφ
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, he⟩ :
      (I.map σ'').sen φ ∈ (I.map σ').sen '' ((I.map σ).sen '' G.axioms K) :=
    heq ▸ ⟨φ, hφ, rfl⟩
  refine ((I.map σ'').sat m φ).1 (he ▸ ((I.map σ').sat m _).2 (((I.map σ).sat _ ψ).2 ?_))
  exact h _ (GlobReach.reduct_mem_models G hL hm) ψ hψ

/-- **Loc-Decomposition II** is sound: from local reachability `N ⟶σ' M` and
`σ(Φᴺ) = σ'(Φᴺ)` infer `N ⇢σ M` (local).

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 13) and Proposition 13 (PDF page 15). -/
theorem locDecomposition₂ {N M : G.Node} {σ σ' : G.sig N ⟶ G.sig M} (h : G.LocReach N M σ')
    (heq : (I.map σ).sen '' G.axioms N = (I.map σ').sen '' G.axioms N) :
    G.LocalThm N M σ := by
  intro m hm φ hφ
  obtain ⟨ψ, hψ, he⟩ : (I.map σ).sen φ ∈ (I.map σ').sen '' G.axioms N :=
    heq ▸ ⟨φ, hφ, rfl⟩
  exact ((I.map σ).sat m φ).1
    (he ▸ ((I.map σ').sat m ψ).2 (LocReach.reduct_sat_axioms G h hm ψ hψ))

/-- **Local Inference** is sound: `N ⇒ σ(Φᴹ)` proves the local theorem link `M ⇢σ N`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 14) and Proposition 13 (PDF page 15). -/
theorem localInference {M N : G.Node} (σ : G.sig M ⟶ G.sig N)
    (h : G.LocalImpl N ((I.map σ).sen '' G.axioms M)) : G.LocalThm M N σ :=
  fun n hn φ hφ => ((I.map σ).sat n φ).1 (h n hn _ ⟨φ, hφ, rfl⟩)

/-- **Basic Inference** is sound: if every sentence of `Γ` is a semantic consequence of the
theory of `N`, then `N ⇒ Γ`. (The paper uses a sound entailment relation `⊢`; any sound `⊢`
factors through semantic consequence.)

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 14) and Proposition 13 (PDF page 15). -/
theorem basicInference {N : G.Node} {Γ : Set (I.obj (G.sig N)).Sen}
    (h : ∀ φ ∈ Γ, (I.obj (G.sig N)).Entails (G.theory N) φ) : G.LocalImpl N Γ :=
  fun n hn φ hφ => h φ hφ n (G.models_subset_modelsOf_theory N hn)

/-- **Model-Expansion** is sound: a global definition link `N ⟶σ K` along a model-expansive
corridor, into a node `K` that has no local axioms and no other incoming links, is conservative.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Figure 6.1 (rule
Model-Expansion) and Theorem 6.26 (printed pages 161–162, PDF pages 163–164). -/
theorem conservative_of_modelExpansive {N K : G.Node} {σ : G.sig N ⟶ G.sig K}
    (hσ : Corridor.ModelExpansive (I.map σ)) (hax : G.axioms K = ∅)
    (hglob : ∀ M τ, τ ∈ G.globalDef M K → ∃ h : M = N, τ = eqToHom (congrArg G.sig h) ≫ σ)
    (hloc : ∀ M, G.localDef M K = ∅) (hhide : ∀ M, G.hidingDef M K = ∅) :
    G.Conservative N K σ := by
  intro m hm
  obtain ⟨n, rfl⟩ := hσ m
  refine ⟨n, (G.mem_models_iff K n).2 ⟨?_, ?_, ?_, ?_⟩, rfl⟩
  · simp [hax]
  · intro M τ hτ
    obtain ⟨rfl, rfl⟩ := hglob M τ hτ
    simpa using hm
  · intro M τ hτ
    simp [hloc] at hτ
  · intro M τ hτ
    simp [hhide] at hτ

end DevGraph

end Silmaril.Logic.Institution
