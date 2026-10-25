module

public import Silmaril.Logic.Institution.Hets.Decomposition
public import Silmaril.Logic.Institution.Hets.Unfolding
public import Silmaril.Logic.Institution.Grothendieck.Amalgamation

@[expose] public section

/-!
# Soundness of the hiding, conservativity and borrowing rules

The rules of the development-graph calculus that are not decomposition rules
(`Hets/Decomposition.lean` has those), with their soundness:

* **Theorem-Hide-Shift** (`theoremHideShift`): to prove `K ⇢σ N` when hiding links occur below
  `N`, pass to the new isolated node `C` over a weakly amalgamable cocone of the unfolding of
  `N` and prove `K ⇢(σ;μ⟨N⟩) C`;
* **Hide-Theorem-Shift** (`hideTheoremShift`): a hiding theorem link follows from a global
  theorem link into a conservative extension;
* **Borrowing** (`borrowing`): shift a global theorem link along conservative extensions;
* **Cons-Shift** (`consShift`): conservativity is preserved along weakly amalgamable squares
  into isolated nodes; **Cons-Composition** (`consComposition`);
* **Local Borrowing** and **Composition** (`localBorrowing`, `composition`), the rules for
  heterogeneous proofs of Fig. 6.1 of the habilitation (Model-Expansion is
  `DevGraph.conservative_of_modelExpansive` in `Hets/Decomposition.lean`).

Weak amalgamation of a single square (`WeakModelAmalgamation`) and weak semi-exactness
(`WeaklySemiExact`) are the existence halves of `ModelAmalgamation` and `SemiExact`
(`Grothendieck/Amalgamation.lean`).

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1 and
  Proposition 12 (PDF pages 10–13): Theorem-Hide-Shift, Hide-Theorem-Shift, Cons-Shift.
* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2 (printed pages 138–140,
  PDF pages 140–142: Hide-Theorem-Shift, Theorem-Hide-Shift, Borrowing), §5.6.3 (printed
  page 141, PDF page 143: Cons-Shift, Cons-Composition), §6.4, Figure 6.1 and Theorem 6.26
  (printed pages 162–163, PDF pages 164–165: Local Borrowing, Composition).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe n u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign]

section Amalgamation

variable (I : Sign ⥤ Room.{w, m₁, m₂})

/-- **Weak model amalgamation** for a square: models agreeing on the common part have some
(not necessarily unique) amalgamation.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "weakly amalgamable", existence without uniqueness);
`mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.3 (printed page 141, PDF
page 143: side condition of Cons-Shift). -/
def WeakModelAmalgamation {S S₁ S₂ S' : Sign} (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂) (g₁ : S₁ ⟶ S')
    (g₂ : S₂ ⟶ S') : Prop :=
  ∀ (M₁ : (I.obj S₁).Mod) (M₂ : (I.obj S₂).Mod),
    (I.map f₁).mod.obj M₁ = (I.map f₂).mod.obj M₂ →
      ∃ M' : (I.obj S').Mod, (I.map g₁).mod.obj M' = M₁ ∧ (I.map g₂).mod.obj M' = M₂

/-- A room functor is *weakly semi-exact* when every pushout square of signatures has weak
model amalgamation.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "(weakly) semi-exact, if any pushout of signatures is (weakly) amalgamable"). -/
def WeaklySemiExact : Prop :=
  ∀ ⦃S S₁ S₂ S' : Sign⦄ (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂) (g₁ : S₁ ⟶ S') (g₂ : S₂ ⟶ S'),
    IsPushout f₁ f₂ g₁ g₂ → WeakModelAmalgamation I f₁ f₂ g₁ g₂

variable {I}

/-- Model amalgamation implies weak model amalgamation. -/
theorem ModelAmalgamation.weak {S S₁ S₂ S' : Sign} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂} {g₁ : S₁ ⟶ S'}
    {g₂ : S₂ ⟶ S'} (h : ModelAmalgamation I f₁ f₂ g₁ g₂) :
    WeakModelAmalgamation I f₁ f₂ g₁ g₂ := fun M₁ M₂ hM =>
  (h M₁ M₂ hM).exists

/-- Semi-exact room functors are weakly semi-exact. -/
theorem SemiExact.weaklySemiExact (h : SemiExact I) : WeaklySemiExact I :=
  fun _ _ _ _ f₁ f₂ g₁ g₂ hp => (h f₁ f₂ g₁ g₂ hp).modelAmalgamation.weak

end Amalgamation

variable {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace DevGraph

variable (G : DevGraph.{n} I)

/-! ### The consistent family of a model below a node

For Theorem-Hide-Shift: an `N`-model `m` extends to a family of models consistent with the
unfolding of `N`, reducing along global and local links and choosing an expansion along hiding
links (Mossakowski–Autexier–Hutter, proof of Proposition 12). -/

/-- Models along a path of non-local links into `N`, starting from an `N`-model: reducts along
global links, chosen expansions along hiding links. -/
noncomputable def hidingExpansion {N : G.Node} (m : (I.obj (G.sig N)).Mod)
    (hm : m ∈ G.models N) :
    ∀ {K : G.Node}, G.NPath N K → {x : (I.obj (G.sig K)).Mod // x ∈ G.models K}
  | _, .nil => ⟨m, hm⟩
  | _, .glob σ hσ p => ⟨reduct σ (hidingExpansion m hm p).1,
      ((G.mem_models_iff _ _).1 (hidingExpansion m hm p).2).2.1 _ σ hσ⟩
  | _, .hide σ hσ p =>
      ⟨Classical.choose (((G.mem_models_iff _ _).1 (hidingExpansion m hm p).2).2.2.2 _ σ hσ),
        (Classical.choose_spec
          (((G.mem_models_iff _ _).1 (hidingExpansion m hm p).2).2.2.2 _ σ hσ)).1⟩

theorem reduct_hidingExpansion_hide {N : G.Node} (m : (I.obj (G.sig N)).Mod)
    (hm : m ∈ G.models N) {K M : G.Node} (σ : G.sig M ⟶ G.sig K) (hσ : σ ∈ G.hidingDef K M)
    (p : G.NPath N M) :
    reduct σ (G.hidingExpansion m hm (.hide σ hσ p)).1 = (G.hidingExpansion m hm p).1 :=
  (Classical.choose_spec
    (((G.mem_models_iff _ _).1 (G.hidingExpansion m hm p).2).2.2.2 _ σ hσ)).2

/-- The model at each object of the unfolding of `N`. -/
noncomputable def hidingFamilyMod {N : G.Node} (m : (I.obj (G.sig N)).Mod)
    (hm : m ∈ G.models N) : ∀ {K : G.Node}, G.UObj N K → (I.obj (G.sig K)).Mod
  | _, .npath p => (G.hidingExpansion m hm p).1
  | _, .loc σ _ p => reduct σ (G.hidingExpansion m hm p).1

/-- The family of models consistent with the unfolding of `N` induced by an `N`-model. -/
noncomputable def hidingFamily {N : G.Node} (m : (I.obj (G.sig N)).Mod)
    (hm : m ∈ G.models N) : G.UFamily N where
  mod := G.hidingFamilyMod m hm
  glob_eq _ _ _ := rfl
  loc_eq _ _ _ := rfl
  hide_eq σ hσ p := G.reduct_hidingExpansion_hide m hm σ hσ p

/-- Each model of the family satisfies the local axioms of its node. -/
theorem hidingFamilyMod_sat {N : G.Node} (m : (I.obj (G.sig N)).Mod) (hm : m ∈ G.models N)
    {K : G.Node} (i : G.UObj N K) :
    ∀ φ ∈ G.axioms K, (I.obj (G.sig K)).Sat (G.hidingFamilyMod m hm i) φ := by
  cases i with
  | npath p => exact ((G.mem_models_iff _ _).1 (G.hidingExpansion m hm p).2).1
  | loc σ hσ p =>
    exact ((G.mem_models_iff _ _).1 (G.hidingExpansion m hm p).2).2.2.1 _ σ hσ

/-- **Theorem-Hide-Shift** is sound: if `c` is a weakly amalgamable cocone for the unfolding of
`N` and `K ⇢(σ;μ⟨N⟩) C` holds in the graph extended by the isolated node `C` over `c`, then
`K ⇢σ N` holds.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
and Proposition 12 (PDF pages 11–13); `mossakowski-2005-habilitation-hets` in `references.bib`,
§5.6.2 (printed pages 138–140, PDF pages 140–142). -/
theorem theoremHideShift {K N : G.Node} {σ : G.sig K ⟶ G.sig N} (c : G.UCocone N)
    (hc : c.WeaklyAmalgamable)
    (h : (G.addNode (G.thsNode c)).GlobalThm (some K) none (σ ≫ c.μ (UObj.root G N))) :
    G.GlobalThm K N σ := by
  intro m hm
  obtain ⟨m', hm'⟩ := hc (G.hidingFamily m hm)
  have hmem : m' ∈ (G.addNode (G.thsNode c)).models none := by
    refine (G.mem_models_addNode_none (G.thsNode c) m').2 ⟨fun _ h => False.elim h,
      fun _ _ h => False.elim h, ?_, fun _ _ h => False.elim h⟩
    rintro K' τ ⟨i, rfl⟩ φ hφ
    change (I.obj (G.sig K')).Sat (reduct (I := I) (S := G.sig K') (c.μ i) m') φ
    rw [hm' K' i]
    exact G.hidingFamilyMod_sat m hm i φ hφ
  have := h m' hmem
  rw [models_addNode_some] at this
  have hroot : reduct (c.μ (UObj.root G N)) m' = m := hm' N (UObj.root G N)
  change reduct (I := I) (S := G.sig K) (σ ≫ c.μ (UObj.root G N)) m' ∈ G.models K at this
  have e : reduct (I := I) (σ ≫ c.μ (UObj.root G N)) m' = reduct σ m := by
    rw [reduct_comp, hroot]
  rwa [e] at this

/-- **Hide-Theorem-Shift** is sound: from `K' ⇢σ' N'`, a conservative `N ⇢θ' N'` and
`θ ; σ' = σ ; θ'` infer the hiding theorem link `K' ⇢σ,θ,h N`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
and Proposition 12 (PDF pages 12–13); `mossakowski-2005-habilitation-hets` in `references.bib`,
§5.6.2 (printed page 138, PDF page 140). The source also asks for a definition link
`N ⟶θ' N'`; only its conservativity is used. -/
theorem hideTheoremShift {K' N N' : G.Node} {S : Sign} {θ : S ⟶ G.sig K'} {σ : S ⟶ G.sig N}
    {σ' : G.sig K' ⟶ G.sig N'} {θ' : G.sig N ⟶ G.sig N'} (hcomm : θ ≫ σ' = σ ≫ θ')
    (hcons : G.Conservative N N' θ') (h : G.GlobalThm K' N' σ') : G.HidingThm K' N θ σ := by
  intro m hm
  obtain ⟨n', hn', rfl⟩ := hcons m hm
  exact ⟨reduct σ' n', h n' hn', by rw [← reduct_comp, hcomm, reduct_comp]⟩

/-- **Borrowing** is sound: from `K ⇢θ K'`, a conservative `N ⇢θ' N'`, `K' ⇢σ' N'` and
`θ ; σ' = σ ; θ'` infer `K ⇢σ N`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2, rule Borrowing
(printed page 140, PDF page 142). -/
theorem borrowing {K K' N N' : G.Node} {σ : G.sig K ⟶ G.sig N} {θ : G.sig K ⟶ G.sig K'}
    {σ' : G.sig K' ⟶ G.sig N'} {θ' : G.sig N ⟶ G.sig N'} (hcomm : θ ≫ σ' = σ ≫ θ')
    (hθ : G.GlobalThm K K' θ) (hcons : G.Conservative N N' θ') (h : G.GlobalThm K' N' σ') :
    G.GlobalThm K N σ := by
  intro m hm
  obtain ⟨n', hn', rfl⟩ := hcons m hm
  have := hθ _ (h n' hn')
  rwa [← reduct_comp, hcomm, reduct_comp] at this

/-- **Cons-Shift** is sound: if `K ⇢θ K'` is conservative, `K ⇢σ N` holds, the square
`θ ; σ' = σ ; θ'` has weak model amalgamation and `N'` is isolated with incoming links
`N ⟶θ' N'` and `K' ⟶σ' N'`, then `N ⇢θ' N'` is conservative.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.3, rule Cons-Shift
(printed page 141, PDF page 143);
`mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`,
§5.1 and Proposition 12 (PDF pages 12–13). -/
theorem consShift {K K' N N' : G.Node} {σ : G.sig K ⟶ G.sig N} {θ : G.sig K ⟶ G.sig K'}
    {σ' : G.sig K' ⟶ G.sig N'} {θ' : G.sig N ⟶ G.sig N'} (hcomm : θ ≫ σ' = σ ≫ θ')
    (hamalg : WeakModelAmalgamation I θ σ σ' θ') (hiso : G.IsolatedBy N' (G.linkFrom₂ N θ' K' σ'))
    (hcons : G.Conservative K K' θ) (hσ : G.GlobalThm K N σ) : G.Conservative N N' θ' := by
  intro m hm
  obtain ⟨k', hk', hk'eq⟩ := hcons _ (hσ m hm)
  obtain ⟨M', h₁, h₂⟩ := hamalg k' m hk'eq
  refine ⟨M', (G.mem_models_iff _ _).2 ⟨?_, ?_, ?_, ?_⟩, h₂⟩
  · simp [hiso.1]
  · intro L τ hτ
    rcases hiso.2.1 L hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change reduct (𝟙 _ ≫ θ') M' ∈ _
      rw [Category.id_comp]
      rw [show reduct θ' M' = m from h₂]; exact hm
    · change reduct (𝟙 _ ≫ σ') M' ∈ _
      rw [Category.id_comp]
      rw [show reduct σ' M' = k' from h₁]; exact hk'
  · intro L τ hτ
    simp [hiso.2.2.1 L] at hτ
  · intro L τ hτ
    simp [hiso.2.2.2 L] at hτ

/-- **Cons-Composition** is sound: conservative links compose.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.3, rule
Cons-Composition (printed page 141, PDF page 143). -/
theorem consComposition {K N N' : G.Node} {σ : G.sig K ⟶ G.sig N} {θ : G.sig N ⟶ G.sig N'}
    (h₁ : G.Conservative K N σ) (h₂ : G.Conservative N N' θ) : G.Conservative K N' (σ ≫ θ) := by
  intro m hm
  obtain ⟨n, hn, rfl⟩ := h₁ m hm
  obtain ⟨n', hn', rfl⟩ := h₂ n hn
  exact ⟨n', hn', reduct_comp σ θ n'⟩

/-- **Local Borrowing** is sound: if `K ⇢θ' K'` is conservative, `N' ⇢σ' K'` is a local theorem
link, `θ : Σᴺ ⟶ Σᴺ'` maps the local axioms of `N` into those of `N'` and `θ ; σ' = σ ; θ'`,
then `N ⇢σ K` is a local theorem link.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Figure 6.1 (rule
Local Borrowing) and the soundness part of Theorem 6.26 (printed pages 162–163, PDF pages
164–165). The source also asks `K'` to be isolated; only the conservativity of `θ'` is used. -/
theorem localBorrowing {N N' K K' : G.Node} {σ : G.sig N ⟶ G.sig K} {θ : G.sig N ⟶ G.sig N'}
    {σ' : G.sig N' ⟶ G.sig K'} {θ' : G.sig K ⟶ G.sig K'} (hcomm : θ ≫ σ' = σ ≫ θ')
    (hax : (I.map θ).sen '' G.axioms N ⊆ G.axioms N') (hcons : G.Conservative K K' θ')
    (h : G.LocalThm N' K' σ') : G.LocalThm N K σ := by
  intro m hm φ hφ
  obtain ⟨k', hk', rfl⟩ := hcons m hm
  have := ((I.map θ).sat _ φ).1 (h k' hk' _ (hax ⟨φ, hφ, rfl⟩))
  change (I.obj (G.sig N)).Sat (reduct θ (reduct σ' k')) φ at this
  rwa [← reduct_comp, hcomm, reduct_comp] at this

/-- **Composition** is sound: from the local theorem link `N ⇢σ K` and the global theorem link
`K ⇢θ P` infer the local theorem link `N ⇢(σ;θ) P`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Figure 6.1 (rule
Composition) and Theorem 6.26 (printed pages 162–163, PDF pages 164–165). -/
theorem composition {N K P : G.Node} {σ : G.sig N ⟶ G.sig K} {θ : G.sig K ⟶ G.sig P}
    (h₁ : G.LocalThm N K σ) (h₂ : G.GlobalThm K P θ) : G.LocalThm N P (σ ≫ θ) := by
  intro m hm φ hφ
  rw [reduct_comp]
  exact h₁ _ (h₂ m hm) φ hφ

/-- **Model-Expansion** with an isolated target, in the `IsolatedBy` form: a link along a
model-expansive corridor into a node isolated by that single link is conservative. This
restates `DevGraph.conservative_of_modelExpansive`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4, Figure 6.1 (rule
Model-Expansion) and Theorem 6.26 (printed pages 162–163, PDF pages 164–165). -/
theorem modelExpansion {N K : G.Node} {σ : G.sig N ⟶ G.sig K}
    (hσ : Corridor.ModelExpansive (I.map σ)) (hiso : G.IsolatedBy K (G.linkFrom N σ)) :
    G.Conservative N K σ :=
  G.conservative_of_modelExpansive hσ hiso.1 (fun M _ hτ => hiso.2.1 M hτ) hiso.2.2.1
    hiso.2.2.2

end DevGraph

end Silmaril.Logic.Institution
