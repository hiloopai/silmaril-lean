module

public import Silmaril.Logic.Institution.Hets.Extension
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.FinCategory.AsType
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Sigma

@[expose] public section

/-!
# The unfolding of a development graph below a node

Theorem-Hide-Shift (Mossakowski–Autexier–Hutter §5.1; Mossakowski's habilitation §5.6.2)
unfolds the subgraph below a node `N` into a tree and takes a weakly amalgamable cocone of the
resulting diagram of signatures. The objects of the diagram are paths into `N`:

* `NPath N K`: a chain `K ⟶ ⋯ ⟶ N` of global and hiding definition links (the non-local links);
* `UObj N K`: such a chain, or a local definition link `K ⟶σ M` followed by a chain from `M`
  (local links only occur at the head of a path, as in the source).

The morphisms of the diagram are the links: a global or local link `K ⟶σ M` gives a morphism
from the longer path to the shorter one, labelled `σ`; a hiding link `K ⟶σ,h M` (with
`σ : Σᴹ ⟶ Σᴷ`) gives one from the shorter path to the longer one. We do not build the indexing
category; a cocone (`UCocone`) and a consistent family of models (`UFamily`) are given by
their components and the compatibility equations along the links.

* `UCocone.WeaklyAmalgamable`: every consistent family has an amalgamation on the apex.
* `thsNode c`: the new isolated node of Theorem-Hide-Shift over the apex of `c`, with an
  incoming *local* definition link `G(i) ⟶μᵢ C` for every object `i`.
* `globalThm_thsNode` (Lemma 15 of Mossakowski–Autexier–Hutter; the induction in the proof of
  Lemma 6.27 of the habilitation): the reduct of every `C`-model along `μ⟨N⟩` is an `N`-model.
* `FiniteWeakAmalgamation I`: Mossakowski–Autexier–Hutter's standing assumption that the model
  functor maps finite colimits to weak limits; with finite colimits of signatures it gives a
  weakly amalgamable cocone for the (finite) unfolding of a finite graph
  (`exists_weaklyAmalgamable_uCocone`).

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`: §3 (PDF
  page 5: "`LOG` admits finite weak amalgamation, i.e. `Mod` maps finite colimits to weak
  limits", and its reformulation by consistent families); §5.1 (PDF pages 10–11: the diagram
  associated with `N` and the rule Theorem-Hide-Shift); §7, Lemma 15 (PDF page 17).
* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2 (printed pages 138–139,
  PDF pages 140–141: `Diag_N`, weakly amalgamable cocones, Theorem-Hide-Shift); §6.4, Lemma 6.27
  (printed page 163, PDF page 165: the related statement that models of `Th(P)` are `P`-models,
  our `flattenable_thsNode` with Proposition 10).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits

universe n u v w m₁ m₂ w₁

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace DevGraph

variable (G : DevGraph.{n} I)

/-- Chains `K ⟶ ⋯ ⟶ N` of global and hiding definition links ending in `N`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
(PDF page 10: objects `⟨M ⟶l₁ ⋯ ⟶lₙ N⟩` "with `l₁, …, lₙ` non-local links"). -/
inductive NPath (N : G.Node) : G.Node → Type (max n v)
  /-- The trivial path `⟨N⟩`. -/
  | nil : NPath N N
  /-- A global definition link `K ⟶σ M` in front of a path from `M`. -/
  | glob {K M : G.Node} (σ : G.sig K ⟶ G.sig M) (hσ : σ ∈ G.globalDef K M) (p : NPath N M) :
      NPath N K
  /-- A hiding definition link `K ⟶σ,h M` (with `σ : Σᴹ ⟶ Σᴷ`) in front of a path from `M`. -/
  | hide {K M : G.Node} (σ : G.sig M ⟶ G.sig K) (hσ : σ ∈ G.hidingDef K M) (p : NPath N M) :
      NPath N K

/-- The objects of the diagram associated with `N`, over the node `K = G(i)`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
(PDF page 10). -/
inductive UObj (N : G.Node) : G.Node → Type (max n v)
  /-- A path of non-local links. -/
  | npath {K : G.Node} (p : G.NPath N K) : UObj N K
  /-- A local definition link `K ⟶σ M` in front of a path of non-local links from `M`. -/
  | loc {K M : G.Node} (σ : G.sig K ⟶ G.sig M) (hσ : σ ∈ G.localDef K M) (p : G.NPath N M) :
      UObj N K

/-- The root object `⟨N⟩`. -/
abbrev UObj.root (N : G.Node) : G.UObj N N := .npath .nil

/-- A cocone over the diagram associated with `N`: an apex signature and a morphism from the
signature of every object, compatible with the links.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2 (printed page 139,
PDF page 141: "a weakly amalgamable cocone `(Σ, (μᵢ : Diag_N(i) ⟶ Σ)_{i ∈ |J|})`"). -/
structure UCocone (N : G.Node) where
  /-- The apex `Σ`. -/
  apex : Sign
  /-- The injections `μᵢ`. -/
  μ : ∀ {K : G.Node}, G.UObj N K → (G.sig K ⟶ apex)
  /-- Compatibility along a global link. -/
  glob_comm : ∀ {K M : G.Node} (σ : G.sig K ⟶ G.sig M) (hσ : σ ∈ G.globalDef K M)
    (p : G.NPath N M), μ (.npath (.glob σ hσ p)) = σ ≫ μ (.npath p)
  /-- Compatibility along a local link. -/
  loc_comm : ∀ {K M : G.Node} (σ : G.sig K ⟶ G.sig M) (hσ : σ ∈ G.localDef K M)
    (p : G.NPath N M), μ (.loc σ hσ p) = σ ≫ μ (.npath p)
  /-- Compatibility along a hiding link (which points the other way in the diagram). -/
  hide_comm : ∀ {K M : G.Node} (σ : G.sig M ⟶ G.sig K) (hσ : σ ∈ G.hidingDef K M)
    (p : G.NPath N M), μ (.npath p) = σ ≫ μ (.npath (.hide σ hσ p))

/-- A family of models consistent with the diagram associated with `N`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §3 (PDF
page 5: "a family `(mᵢ)` consistent with `I`, if … for each `l : i → j`, `mⱼ|D(l) = mᵢ`"). -/
structure UFamily (N : G.Node) where
  /-- The model at each object. -/
  mod : ∀ {K : G.Node}, G.UObj N K → (I.obj (G.sig K)).Mod
  /-- Consistency along a global link. -/
  glob_eq : ∀ {K M : G.Node} (σ : G.sig K ⟶ G.sig M) (hσ : σ ∈ G.globalDef K M)
    (p : G.NPath N M), mod (.npath (.glob σ hσ p)) = reduct σ (mod (.npath p))
  /-- Consistency along a local link. -/
  loc_eq : ∀ {K M : G.Node} (σ : G.sig K ⟶ G.sig M) (hσ : σ ∈ G.localDef K M)
    (p : G.NPath N M), mod (.loc σ hσ p) = reduct σ (mod (.npath p))
  /-- Consistency along a hiding link. -/
  hide_eq : ∀ {K M : G.Node} (σ : G.sig M ⟶ G.sig K) (hσ : σ ∈ G.hidingDef K M)
    (p : G.NPath N M), reduct σ (mod (.npath (.hide σ hσ p))) = mod (.npath p)

variable {G}

/-- A cocone is *weakly amalgamable* when every consistent family of models has an
amalgamation (not necessarily unique) over the apex.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.6.2 (printed pages
139–140, PDF pages 141–142: "Since … `(Σ, (μᵢ))` is a weakly amalgamable cocone, there is a
`Σᴾ`-model `M_K` with `M_K|μᵢ = Mᵢ`"). -/
def UCocone.WeaklyAmalgamable {N : G.Node} (c : G.UCocone N) : Prop :=
  ∀ f : G.UFamily N, ∃ m : (I.obj c.apex).Mod, ∀ (K : G.Node) (i : G.UObj N K),
    reduct (c.μ i) m = f.mod i

variable (G)

/-- The new isolated node `C` of Theorem-Hide-Shift: signature the apex of `c`, no local
axioms, and a local definition link `G(i) ⟶μᵢ C` for every object `i` of the diagram.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.1
(PDF page 11: "`C` is a new isolated node with signature `Colim D`, and with ingoing local
definition links `G(i) ⟶μᵢ C`"). The habilitation (§5.6.2, printed page 139, PDF page 141)
uses global links, which are only sound for nodes reached without local links; we follow the
journal version. -/
def thsNode {N : G.Node} (c : G.UCocone N) : G.NewNode where
  sig := c.apex
  axioms := ∅
  globalDef _ := ∅
  localDef K := {τ | ∃ i : G.UObj N K, τ = c.μ i}
  hidingDef _ := ∅

/-- **Lemma 15** of Mossakowski–Autexier–Hutter: in the graph extended by the node `C` of
Theorem-Hide-Shift, `N ⇢μ⟨N⟩ C` is a global theorem link.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §7,
Lemma 15 (PDF page 17); `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4,
Lemma 6.27 and its proof (printed page 163, PDF page 165), which proves this by the same
induction. -/
theorem globalThm_thsNode {N : G.Node} (c : G.UCocone N) :
    (G.addNode (G.thsNode c)).GlobalThm (some N) none (c.μ (UObj.root G N)) := by
  intro m hm
  rw [models_addNode_some]
  have hloc := ((G.mem_models_addNode_none (G.thsNode c) m).1 hm).2.2.1
  have hmem : ∀ {K : G.Node} (i : G.UObj N K), c.μ i ∈ (G.thsNode c).localDef K :=
    fun i => show ∃ j, _ = _ from ⟨i, rfl⟩
  have key : ∀ (M : G.Node) (p : G.NPath N M), reduct (c.μ (.npath p)) m ∈ G.models M := by
    intro M
    refine G.wf.induction M
      (C := fun M => ∀ p : G.NPath N M, reduct (c.μ (.npath p)) m ∈ G.models M) ?_
    intro M ih p
    rw [G.mem_models_iff]
    refine ⟨fun φ hφ => hloc M _ (hmem (.npath p)) φ hφ, fun K σ hσ => ?_,
      fun K σ hσ φ hφ => ?_, fun K σ hσ => ?_⟩
    · have := ih K (Or.inl ⟨σ, hσ⟩) (.glob σ hσ p)
      rw [c.glob_comm] at this
      exact (congrArg (· ∈ G.models K) (reduct_comp σ (c.μ (.npath p)) m)).mp this
    · have := hloc K _ (hmem (.loc σ hσ p)) φ hφ
      rw [c.loc_comm] at this
      exact (congrArg (fun n => (I.obj (G.sig K)).Sat n φ)
        (reduct_comp σ (c.μ (.npath p)) m)).mp this
    · refine ⟨reduct (c.μ (.npath (.hide σ hσ p))) m, ih K (Or.inr (Or.inr ⟨σ, hσ⟩)) _, ?_⟩
      exact (reduct_comp σ (c.μ (.npath (.hide σ hσ p))) m).symm.trans
        (congrArg (fun τ => reduct τ m) (c.hide_comm σ hσ p).symm)
  exact key N .nil

/-- The node `C` of Theorem-Hide-Shift is flattenable (its only incoming links are local). -/
theorem flattenable_thsNode {N : G.Node} (c : G.UCocone N) :
    (G.addNode (G.thsNode c)).Flattenable none := by
  intro M hM σ hσ
  have key : ∀ {A B : (G.addNode (G.thsNode c)).Node}
      {τ : (G.addNode (G.thsNode c)).sig A ⟶ (G.addNode (G.thsNode c)).sig B},
      (G.addNode (G.thsNode c)).GlobReach A B τ → B = none → A = none := by
    intro A B τ h
    induction h with
    | refl => exact id
    | @step A' K' _ σ' _ hσ' _ ih =>
      intro hB
      have := ih hB
      subst this
      cases A' with
      | none => rfl
      | some K => exact False.elim hσ'
  have := key hσ rfl
  subst this
  obtain ⟨K, τ, hτ⟩ := hM
  cases K with
  | none => exact False.elim hτ
  | some K => exact False.elim hτ

/-! ### Finite weak amalgamation -/

variable (I) in
/-- **Finite weak amalgamation**: the model functor maps colimits of finite diagrams of
signatures to weak limits; every family of models consistent with a finite diagram has an
amalgamation over a colimit.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §3 (PDF
page 5: "`LOG` admits finite weak amalgamation iff for each finite diagram `D : I → Sign` and
each family `(mᵢ)` consistent with `I`, there exists a model `m ∈ Colim D` with `m|μᵢ = mᵢ`"). -/
def FiniteWeakAmalgamation : Prop :=
  ∀ (J : Type) [SmallCategory J] [FinCategory J] (D : J ⥤ Sign) (c : Cocone D), IsColimit c →
    ∀ mods : ∀ j, (I.obj (D.obj j)).Mod,
      (∀ ⦃j j' : J⦄ (l : j ⟶ j'), reduct (D.map l) (mods j') = mods j) →
        ∃ m : (I.obj c.pt).Mod, ∀ j, reduct (c.ι.app j) m = mods j

/-! ### Encodings of paths (finiteness) -/

/-- Decompose a path by its first link (used to bound the number of paths). -/
def NPath.enc {N K : G.Node} : G.NPath N K →
    Unit ⊕ ((Σ M, ↥(G.globalDef K M) × G.NPath N M) ⊕ (Σ M, ↥(G.hidingDef K M) × G.NPath N M))
  | .nil => .inl ()
  | .glob σ hσ p => .inr (.inl ⟨_, ⟨σ, hσ⟩, p⟩)
  | .hide σ hσ p => .inr (.inr ⟨_, ⟨σ, hσ⟩, p⟩)

theorem NPath.enc_injective {N K : G.Node} :
    Function.Injective (NPath.enc G (N := N) (K := K)) := by
  intro a b h
  cases a <;> cases b <;>
    first
    | rfl
    | (simp only [NPath.enc, Sum.inr.injEq, Sum.inl.injEq] at h
       obtain ⟨rfl, h⟩ := Sigma.mk.inj h
       simp only [heq_eq_eq, Prod.mk.injEq, Subtype.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       rfl)
    | (simp [NPath.enc] at h)

/-- Decompose an object of the unfolding by its head link. -/
def UObj.enc {N K : G.Node} :
    G.UObj N K → G.NPath N K ⊕ (Σ M, ↥(G.localDef K M) × G.NPath N M)
  | .npath p => .inl p
  | .loc σ hσ p => .inr ⟨_, ⟨σ, hσ⟩, p⟩

theorem UObj.enc_injective {N K : G.Node} :
    Function.Injective (UObj.enc G (N := N) (K := K)) := by
  intro a b h
  cases a <;> cases b <;>
    first
    | (simp only [UObj.enc, Sum.inl.injEq] at h
       subst h
       rfl)
    | (simp only [UObj.enc, Sum.inr.injEq] at h
       obtain ⟨rfl, h⟩ := Sigma.mk.inj h
       simp only [heq_eq_eq, Prod.mk.injEq, Subtype.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       rfl)
    | (simp [UObj.enc] at h)

/-! ### The unfolding as a multispan

Every object of the unfolding other than the root has exactly one *parent* link (its head
link), oriented either way. The unfolding is therefore presented by the multispan with one left
object per object `i` of the unfolding, mapped to `i` and to its parent. -/

/-- The objects of the unfolding below `N`. -/
abbrev UIdx (N : G.Node) : Type (max n v) := Σ K : G.Node, G.UObj N K

/-- The parent of an object of the unfolding (the root is its own parent). -/
def uPar (N : G.Node) : G.UIdx N → G.UIdx N
  | ⟨_, .npath .nil⟩ => ⟨N, .npath .nil⟩
  | ⟨_, .npath (.glob (M := M) _ _ p)⟩ => ⟨M, .npath p⟩
  | ⟨_, .npath (.hide (M := M) _ _ p)⟩ => ⟨M, .npath p⟩
  | ⟨_, .loc (M := M) _ _ p⟩ => ⟨M, .npath p⟩

/-- The source signature of the head link of an object. -/
def uLeft (N : G.Node) : G.UIdx N → Sign
  | ⟨_, .npath .nil⟩ => G.sig N
  | ⟨K, .npath (.glob _ _ _)⟩ => G.sig K
  | ⟨_, .npath (.hide (M := M) _ _ _)⟩ => G.sig M
  | ⟨K, .loc _ _ _⟩ => G.sig K

/-- The head link, seen from the object. -/
def uFst (N : G.Node) : (x : G.UIdx N) → (G.uLeft N x ⟶ G.sig x.1)
  | ⟨_, .npath .nil⟩ => 𝟙 _
  | ⟨_, .npath (.glob _ _ _)⟩ => 𝟙 _
  | ⟨_, .npath (.hide σ _ _)⟩ => σ
  | ⟨_, .loc _ _ _⟩ => 𝟙 _

/-- The head link, seen from the parent. -/
def uSnd (N : G.Node) : (x : G.UIdx N) → (G.uLeft N x ⟶ G.sig (G.uPar N x).1)
  | ⟨_, .npath .nil⟩ => 𝟙 _
  | ⟨_, .npath (.glob σ _ _)⟩ => σ
  | ⟨_, .npath (.hide _ _ _)⟩ => 𝟙 _
  | ⟨_, .loc σ _ _⟩ => σ

/-- The multispan shape of the unfolding. -/
def uShape (N : G.Node) : MultispanShape.{max n v, max n v} where
  L := G.UIdx N
  R := G.UIdx N
  fst := id
  snd := G.uPar N

/-- The right object of the multispan for an object of the unfolding. -/
abbrev uRight (N : G.Node) (x : G.UIdx N) : WalkingMultispan (G.uShape N) := .right x

/-- The model of a consistent family at an object of the unfolding. -/
abbrev UFamily.modAt {N : G.Node} (f : G.UFamily N) (x : G.UIdx N) :
    (I.obj (G.sig x.1)).Mod :=
  f.mod x.2

/-- The multispan diagram of signatures of the unfolding. -/
def uIndex (N : G.Node) : MultispanIndex (G.uShape N) Sign where
  left := G.uLeft N
  right x := G.sig x.1
  fst := G.uFst N
  snd := G.uSnd N

theorem finite_walkingMultispan (S : MultispanShape.{w₁, w₁}) [Finite S.L] [Finite S.R] :
    Finite (WalkingMultispan S) :=
  Finite.of_injective (fun j => match j with
    | .left a => (Sum.inl a : S.L ⊕ S.R)
    | .right b => Sum.inr b) (by rintro (a | a) (b | b) h <;> simp_all)

theorem finite_walkingMultispan_hom {S : MultispanShape.{w₁, w₁}} [Finite S.L]
    [Finite (WalkingMultispan S)] (j j' : WalkingMultispan S) : Finite (j ⟶ j') := by
  have hT : Finite (Σ (a b : WalkingMultispan S), a ⟶ b) := by
    refine Finite.of_surjective (α := WalkingMultispan S ⊕ (Bool × S.L)) (fun x => match x with
      | .inl a => ⟨a, a, 𝟙 a⟩
      | .inr (true, a) => ⟨.left a, .right (S.fst a), WalkingMultispan.Hom.fst a⟩
      | .inr (false, a) => ⟨.left a, .right (S.snd a), WalkingMultispan.Hom.snd a⟩) ?_
    rintro ⟨a, b, f⟩
    cases f with
    | id => exact ⟨.inl _, rfl⟩
    | fst x => exact ⟨.inr (true, x), rfl⟩
    | snd x => exact ⟨.inr (false, x), rfl⟩
  refine Finite.of_injective
    (fun f : j ⟶ j' => (⟨j, j', f⟩ : Σ (a b : WalkingMultispan S), a ⟶ b)) ?_
  intro f g h
  have h2 := eq_of_heq (Sigma.mk.inj h).2
  exact eq_of_heq (Sigma.mk.inj h2).2

/-- A multispan with finite index types is a finite category. -/
@[instance_reducible]
noncomputable def finCategoryWalkingMultispan (S : MultispanShape.{w₁, w₁}) [Finite S.L]
    [Finite S.R] : FinCategory (WalkingMultispan S) :=
  haveI := finite_walkingMultispan S
  { fintypeObj := Fintype.ofFinite _
    fintypeHom := fun j j' =>
      haveI := finite_walkingMultispan_hom j j'
      Fintype.ofFinite _ }

/-- Finite weak amalgamation transfers from finite categories in `Type` to finite categories in
any universe. -/
theorem FiniteWeakAmalgamation.amalgamate (hI : FiniteWeakAmalgamation I) {J : Type w₁}
    [SmallCategory J] [FinCategory J] (D : J ⥤ Sign) (c : Cocone D) (hc : IsColimit c)
    (mods : ∀ j, (I.obj (D.obj j)).Mod)
    (hm : ∀ ⦃j j' : J⦄ (l : j ⟶ j'), reduct (D.map l) (mods j') = mods j) :
    ∃ m : (I.obj c.pt).Mod, ∀ j, reduct (c.ι.app j) m = mods j := by
  let e := FinCategory.equivAsType J
  obtain ⟨m, hm'⟩ := hI (FinCategory.AsType J) (e.functor ⋙ D) (c.whisker e.functor)
    (hc.whiskerEquivalence e) (fun j => mods (e.functor.obj j))
    (fun _ _ l => hm (e.functor.map l))
  refine ⟨m, fun j => ?_⟩
  have h1 : reduct (c.ι.app (e.functor.obj (e.inverse.obj j))) m =
      mods (e.functor.obj (e.inverse.obj j)) := hm' (e.inverse.obj j)
  have h2 : c.ι.app j = D.map (e.counitIso.inv.app j) ≫
      c.ι.app (e.functor.obj (e.inverse.obj j)) := (c.w _).symm
  rw [h2, reduct_comp, h1]
  exact hm _

/-- The unfolding below `N` is finite. -/
def UnfoldingFinite (N : G.Node) : Prop :=
  Finite (Σ K : G.Node, G.UObj N K)

/-- A finite graph with finitely many links between any two nodes has a finite unfolding
(acyclicity bounds the length of paths). -/
theorem unfoldingFinite_of_finite [Finite G.Node]
    (hg : ∀ K M, (G.globalDef K M).Finite) (hl : ∀ K M, (G.localDef K M).Finite)
    (hh : ∀ K M, (G.hidingDef K M).Finite) (N : G.Node) : G.UnfoldingFinite N := by
  have hirr : ∀ a, ¬ Relation.TransGen G.Link a a := by
    intro a h
    have hacc := G.wf_link.transGen.apply a
    revert h
    induction hacc with
    | intro x _ ih => exact fun h => ih x h h
  have hwf : WellFounded (fun A B : G.Node => Relation.TransGen G.Link B A) := by
    have : IsTrans G.Node (fun A B => Relation.TransGen G.Link B A) :=
      ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
    have : Std.Irrefl (fun A B : G.Node => Relation.TransGen G.Link B A) := ⟨hirr⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  have hp : ∀ K, Finite (G.NPath N K) := by
    intro K
    refine hwf.induction K (C := fun K => Finite (G.NPath N K)) ?_
    intro K ih
    have fg : ∀ M, Finite (↥(G.globalDef K M) × G.NPath N M) := by
      intro M
      by_cases h : (G.globalDef K M).Nonempty
      · have := ih M (Relation.TransGen.single (Or.inl h))
        have := (hg K M).to_subtype
        infer_instance
      · have : IsEmpty ↥(G.globalDef K M) := ⟨fun x => h ⟨x.1, x.2⟩⟩
        infer_instance
    have fh : ∀ M, Finite (↥(G.hidingDef K M) × G.NPath N M) := by
      intro M
      by_cases h : (G.hidingDef K M).Nonempty
      · have := ih M (Relation.TransGen.single (Or.inr (Or.inr h)))
        have := (hh K M).to_subtype
        infer_instance
      · have : IsEmpty ↥(G.hidingDef K M) := ⟨fun x => h ⟨x.1, x.2⟩⟩
        infer_instance
    exact Finite.of_injective _ (NPath.enc_injective G)
  have hu : ∀ K, Finite (G.UObj N K) := by
    intro K
    have := hp
    have : ∀ M, Finite ↥(G.localDef K M) := fun M => (hl K M).to_subtype
    exact Finite.of_injective _ (UObj.enc_injective G)
  show Finite (Σ K, G.UObj N K)
  infer_instance

/-- **Weakly amalgamable cocones exist** for finite unfoldings when signatures have finite
colimits and the logic has finite weak amalgamation: Mossakowski–Autexier–Hutter's standing
assumptions supply the side condition of Theorem-Hide-Shift.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §3 (PDF
page 5) and §5.1 (PDF pages 10–11: `C` has signature `Colim D`). -/
theorem exists_weaklyAmalgamable_uCocone [HasFiniteColimits Sign]
    (hI : FiniteWeakAmalgamation I) {N : G.Node} (hN : G.UnfoldingFinite N) :
    ∃ c : G.UCocone N, c.WeaklyAmalgamable := by
  have : Finite (G.uShape N).L := hN
  have : Finite (G.uShape N).R := hN
  let _ := finCategoryWalkingMultispan (G.uShape N)
  let D := (G.uIndex N).multispan
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  have hw : ∀ x : G.UIdx N, G.uFst N x ≫ c.ι.app (G.uRight N x) =
      G.uSnd N x ≫ c.ι.app (G.uRight N (G.uPar N x)) := fun x =>
    (c.w (WalkingMultispan.Hom.fst (J := G.uShape N) x)).trans
      (c.w (WalkingMultispan.Hom.snd (J := G.uShape N) x)).symm
  refine ⟨{ apex := c.pt, μ := fun {K} i => c.ι.app (G.uRight N ⟨K, i⟩),
            glob_comm := ?_, loc_comm := ?_, hide_comm := ?_ }, ?_⟩
  · intro K M σ hσ p
    have e : 𝟙 _ ≫ c.ι.app (G.uRight N ⟨K, .npath (.glob σ hσ p)⟩) =
        σ ≫ c.ι.app (G.uRight N ⟨M, .npath p⟩) :=
      hw ⟨K, .npath (.glob σ hσ p)⟩
    rw [Category.id_comp] at e
    exact e
  · intro K M σ hσ p
    have e : 𝟙 _ ≫ c.ι.app (G.uRight N ⟨K, .loc σ hσ p⟩) =
        σ ≫ c.ι.app (G.uRight N ⟨M, .npath p⟩) :=
      hw ⟨K, .loc σ hσ p⟩
    rw [Category.id_comp] at e
    exact e
  · intro K M σ hσ p
    have e : σ ≫ c.ι.app (G.uRight N ⟨K, .npath (.hide σ hσ p)⟩) =
        𝟙 _ ≫ c.ι.app (G.uRight N ⟨M, .npath p⟩) :=
      hw ⟨K, .npath (.hide σ hσ p)⟩
    rw [Category.id_comp] at e
    exact e.symm
  · intro f
    let mods : ∀ j, (I.obj (D.obj j)).Mod := fun j => match j with
      | .left x => reduct (G.uFst N x) (UFamily.modAt G f x)
      | .right x => UFamily.modAt G f x
    have hcons : ∀ ⦃j j' : WalkingMultispan (G.uShape N)⦄ (l : j ⟶ j'),
        reduct (D.map l) (mods j') = mods j := by
      intro j j' l
      cases l with
      | id A =>
        change reduct (D.map (𝟙 _)) _ = _
        rw [D.map_id, reduct_id]
      | fst x => rfl
      | snd x =>
        obtain ⟨K, i⟩ := x
        cases i with
        | npath p =>
          cases p with
          | nil => rfl
          | glob σ hσ p => exact (f.glob_eq σ hσ p).symm.trans (reduct_id _).symm
          | hide σ hσ p => exact (reduct_id _).trans (f.hide_eq σ hσ p).symm
        | loc σ hσ p => exact (f.loc_eq σ hσ p).symm.trans (reduct_id _).symm
    obtain ⟨m, hm⟩ := hI.amalgamate D c hc mods hcons
    exact ⟨m, fun K i => hm (G.uRight N ⟨K, i⟩)⟩

end DevGraph

end Silmaril.Logic.Institution
