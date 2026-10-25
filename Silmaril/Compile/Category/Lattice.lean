module

public import Silmaril.Compile.Category.Compiler
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.Data.Set.Lattice.Indexed

@[expose] public section

/-!
# Lattices of semantics for one syntax

Many semantics can be given to one syntax: for C on typed Ail, an executable C0 interpreter, a
flat-memory C1, …, and the full Cerberus semantics. This file is the institution-theoretic
bookkeeping for such families, in the vocabulary of `Silmaril.Compile.Category`:

* a `Syntax` is a `Language` without its behaviours (interfaces, programs, observations); a
  `Syntax.Sem` assigns a behaviour set to each program, and `X.lang S` is the `Language` of
  semantics `S`. Every language is `L.syntax.lang L.beh` (`Language.syntax_lang`), so nothing
  is duplicated: a semantics family is a family of languages over one syntax;
* semantics are ordered pointwise by inclusion, `S ≤ T ↔ ∀ p, S p ⊆ T p`: the complete lattice
  `X.Prog → Set X.Obs`, so meets (`S ⊓ T`, `⨅`) and joins (`S ⊔ T`, `⨆`) always exist and are
  pointwise intersections and unions. A *sub-family* (the rungs of a ladder) need not be closed
  under them;
* a *fragment* is a set of programs; `S ⊑[F] T` (`RefinesOn F S T`) says that `S` refines `T`
  on `F`: `∀ p ∈ F, S p ⊆ T p`. This is a valid stepping-stone condition: `S` may be more
  defined and more deterministic than `T` (fix evaluation order, implementation-defined
  choices, give undefined behaviour a result), and must never forbid what `T` requires;
* `refinesSet S T` is the largest fragment on which `S ⊑ T` (`refinesOn_iff_subset`), and
  `overlap S T` the fragment on which the two semantics agree; `overlap S T` is the
  intersection of the two refinement fragments (`overlap_eq_inter`);
* institutions: for programs of `F`, every specification `T` proves about `p` holds in `S`
  (`RefinesOn.sat`): `S`'s behavioural institution has more theorems on `F`;
* compilers: `X.cast T S : X.lang T ⟶ X.lang S` is the identity of programs and observations.
  `S ⊑[F] T` says exactly that the identity is a valid compilation from `T` to `S` on `F`
  (`refinesOn_iff_valid_cast`), so by the lax composition law (`valid_comp_le`) a compiler
  valid for `S` on `F` is valid for `T` on `F` at the same convention (`ValidOn.of_refinesOn`):
  `beh(target) ⊆ S p ⊆ T p`. Chains of rungs compose (`ValidOn.of_chain`).

## Main definitions

* `Syntax`, `Syntax.Sem`, `Syntax.lang`, `Language.syntax`.
* `RefinesOn` (notation `S ⊑[F] T`), `refinesSet`, `overlap`.
* `Syntax.cast`, `ValidOn`.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

/-- A syntax: programs with interfaces, and the type of observations of a run, without a
choice of behaviours. -/
structure Syntax : Type (u + 1) where
  /-- Interfaces. -/
  Iface : Type u
  /-- Programs. -/
  Prog : Type u
  /-- The interface of a program. -/
  iface : Prog → Iface
  /-- Observations. -/
  Obs : Type u

namespace Syntax

variable (X : Syntax.{u})

/-- A semantics of a syntax: the behaviour set of each program. Semantics are ordered
pointwise by inclusion and form a complete lattice (the Pi instance). -/
abbrev Sem : Type u := X.Prog → Set X.Obs

/-- The language of a semantics. -/
abbrev lang (S : X.Sem) : Language.{u} := ⟨X.Iface, X.Prog, X.iface, X.Obs, S⟩

@[simp] theorem lang_beh (S : X.Sem) : (X.lang S).beh = S := rfl
@[simp] theorem lang_iface (S : X.Sem) : (X.lang S).iface = X.iface := rfl

end Syntax

/-- The syntax of a language. -/
def Language.syntax (L : Language.{u}) : Syntax.{u} := ⟨L.Iface, L.Prog, L.iface, L.Obs⟩

/-- Every language is the language of its own behaviours over its syntax. -/
theorem Language.syntax_lang (L : Language.{u}) : L.syntax.lang L.beh = L := rfl

namespace Syntax

variable {X : Syntax.{u}}

/-! ## Refinement on a fragment -/

/-- `S ⊑[F] T`: `S` refines `T` on the fragment `F`. -/
def RefinesOn (F : Set X.Prog) (S T : X.Sem) : Prop := ∀ p ∈ F, S p ⊆ T p

@[inherit_doc] scoped notation:50 S " ⊑[" F "] " T => RefinesOn F S T

theorem RefinesOn.refl (F : Set X.Prog) (S : X.Sem) : S ⊑[F] S := fun _ _ => subset_rfl

theorem RefinesOn.trans {F : Set X.Prog} {S T U : X.Sem} (h₁ : S ⊑[F] T) (h₂ : T ⊑[F] U) :
    S ⊑[F] U :=
  fun p hp => (h₁ p hp).trans (h₂ p hp)

/-- Refinement on a fragment holds on every smaller fragment. -/
theorem RefinesOn.mono {F G : Set X.Prog} {S T : X.Sem} (hFG : F ⊆ G) (h : S ⊑[G] T) :
    S ⊑[F] T :=
  fun p hp => h p (hFG hp)

/-- Refinement on the whole syntax is the lattice order. -/
theorem refinesOn_univ_iff {S T : X.Sem} : (S ⊑[Set.univ] T) ↔ S ≤ T :=
  ⟨fun h p => h p trivial, fun h p _ => h p⟩

theorem RefinesOn.of_le {F : Set X.Prog} {S T : X.Sem} (h : S ≤ T) : S ⊑[F] T :=
  fun p _ => h p

/-- Refinement on a union of fragments is refinement on each. -/
theorem refinesOn_union_iff {F G : Set X.Prog} {S T : X.Sem} :
    (S ⊑[F ∪ G] T) ↔ (S ⊑[F] T) ∧ (S ⊑[G] T) :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun ⟨hF, hG⟩ p hp => hp.elim (hF p) (hG p)⟩

theorem refinesOn_iUnion_iff {ι : Sort*} {F : ι → Set X.Prog} {S T : X.Sem} :
    (S ⊑[⋃ i, F i] T) ↔ ∀ i, S ⊑[F i] T :=
  ⟨fun h i => h.mono (le_iSup F i),
    fun h p hp => by obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp; exact h i p hi⟩

/-- A ladder step: refinement on `F` composes with refinement on a larger fragment `G`. -/
theorem RefinesOn.trans_of_subset {F G : Set X.Prog} {S T U : X.Sem} (h₁ : S ⊑[F] T)
    (h₂ : T ⊑[G] U) (hFG : F ⊆ G) : S ⊑[F] U :=
  h₁.trans (h₂.mono hFG)

/-! ## Meets and joins

They exist in the lattice of all semantics and are characterised fragment-wise. -/

theorem refinesOn_inf_iff {F : Set X.Prog} {S T U : X.Sem} :
    (U ⊑[F] S ⊓ T) ↔ (U ⊑[F] S) ∧ (U ⊑[F] T) :=
  ⟨fun h => ⟨fun p hp => (h p hp).trans Set.inter_subset_left,
      fun p hp => (h p hp).trans Set.inter_subset_right⟩,
    fun ⟨h₁, h₂⟩ p hp => Set.subset_inter (h₁ p hp) (h₂ p hp)⟩

theorem sup_refinesOn_iff {F : Set X.Prog} {S T U : X.Sem} :
    (S ⊔ T ⊑[F] U) ↔ (S ⊑[F] U) ∧ (T ⊑[F] U) :=
  ⟨fun h => ⟨fun p hp => Set.subset_union_left.trans (h p hp),
      fun p hp => Set.subset_union_right.trans (h p hp)⟩,
    fun ⟨h₁, h₂⟩ p hp => Set.union_subset (h₁ p hp) (h₂ p hp)⟩

theorem refinesOn_iInf_iff {ι : Sort*} {F : Set X.Prog} {S : ι → X.Sem} {U : X.Sem} :
    (U ⊑[F] ⨅ i, S i) ↔ ∀ i, U ⊑[F] S i := by
  refine ⟨fun h i p hp => (h p hp).trans ?_, fun h p hp => ?_⟩
  · rw [iInf_apply]; exact iInf_le (fun i => S i p) i
  · rw [iInf_apply]; exact le_iInf fun i => h i p hp

theorem iSup_refinesOn_iff {ι : Sort*} {F : Set X.Prog} {S : ι → X.Sem} {U : X.Sem} :
    (⨆ i, S i ⊑[F] U) ↔ ∀ i, S i ⊑[F] U := by
  refine ⟨fun h i p hp => ?_, fun h p hp => ?_⟩
  · refine Set.Subset.trans ?_ (h p hp); rw [iSup_apply]; exact le_iSup (fun i => S i p) i
  · rw [iSup_apply]; exact iSup_le fun i => h i p hp

/-! ## Refinement fragments and overlap -/

/-- The largest fragment on which `S` refines `T`. -/
def refinesSet (S T : X.Sem) : Set X.Prog := {p | S p ⊆ T p}

theorem refinesOn_iff_subset {F : Set X.Prog} {S T : X.Sem} :
    (S ⊑[F] T) ↔ F ⊆ refinesSet S T := Iff.rfl

theorem refinesOn_refinesSet (S T : X.Sem) : S ⊑[refinesSet S T] T := fun _ h => h

theorem refinesSet_self (S : X.Sem) : refinesSet S S = Set.univ :=
  Set.eq_univ_of_forall fun p => (Set.Subset.rfl : S p ⊆ S p)

theorem refinesSet_trans (S T U : X.Sem) :
    refinesSet S T ∩ refinesSet T U ⊆ refinesSet S U :=
  fun _ h => Set.Subset.trans h.1 h.2

/-- The overlap of two semantics: the fragment on which they agree. -/
def overlap (S T : X.Sem) : Set X.Prog := {p | S p = T p}

theorem overlap_comm (S T : X.Sem) : overlap S T = overlap T S :=
  Set.ext fun _ => eq_comm

theorem overlap_self (S : X.Sem) : overlap S S = Set.univ :=
  Set.eq_univ_of_forall fun _ => rfl

theorem overlap_trans (S T U : X.Sem) : overlap S T ∩ overlap T U ⊆ overlap S U :=
  fun _ h => h.1.trans h.2

/-- The overlap is where each semantics refines the other. -/
theorem overlap_eq_inter (S T : X.Sem) : overlap S T = refinesSet S T ∩ refinesSet T S :=
  Set.ext fun _ => ⟨fun h => ⟨h.le, h.ge⟩, fun h => h.1.antisymm h.2⟩

theorem refinesOn_overlap (S T : X.Sem) : S ⊑[overlap S T] T := fun _ h => h.le

/-- Mutual refinement on a fragment puts it inside the overlap. -/
theorem subset_overlap {F : Set X.Prog} {S T : X.Sem} (h₁ : S ⊑[F] T) (h₂ : T ⊑[F] S) :
    F ⊆ overlap S T :=
  fun p hp => (h₁ p hp).antisymm (h₂ p hp)

/-- The overlap of a meet: where `S ⊓ T` is `S`, `S` refines `T`. -/
theorem refinesSet_eq_overlap_inf (S T : X.Sem) : refinesSet S T = overlap (S ⊓ T) S :=
  Set.ext fun _ => ⟨fun h => Set.inter_eq_left.2 h, fun h => Set.inter_eq_left.1 h⟩

/-- A semantics that is deterministic (at most one behaviour) on a fragment. -/
def DeterministicOn (F : Set X.Prog) (S : X.Sem) : Prop := ∀ p ∈ F, (S p).Subsingleton

/-- A refinement of a deterministic semantics that has a behaviour agrees with it. -/
theorem RefinesOn.overlap_of_deterministic {F : Set X.Prog} {S T : X.Sem} (h : S ⊑[F] T)
    (hT : DeterministicOn F T) (hS : ∀ p ∈ F, (S p).Nonempty) : F ⊆ overlap S T := by
  intro p hp
  obtain ⟨o, ho⟩ := hS p hp
  refine (h p hp).antisymm fun o' ho' => ?_
  rw [hT p hp ho' (h p hp ho)]
  exact ho

/-! ## The behavioural institutions -/

/-- On a fragment where `S` refines `T`, every specification that holds of a program in `T`
holds of it in `S`: `S`'s behavioural institution has more theorems there. -/
theorem RefinesOn.sat {F : Set X.Prog} {S T : X.Sem} (h : S ⊑[F] T) {p : X.Prog} (hp : p ∈ F)
    {φ : Set X.Obs} (hT : (X.lang T).Sat p φ) : (X.lang S).Sat p φ :=
  (h p hp).trans hT

/-! ## Casts and compilers -/

variable (X) in
/-- The identity of programs, interfaces and observations, as a convention between two
semantics of the same syntax. -/
def cast (S T : X.Sem) : X.lang S ⟶ X.lang T := ⟨id, Eq⟩

@[simp] theorem cast_Φ (S T : X.Sem) : (X.cast S T).Φ = id := rfl
@[simp] theorem cast_R (S T : X.Sem) : (X.cast S T).R = Eq := rfl

theorem cast_lift (S T : X.Sem) (B : Set X.Obs) : (X.cast S T).lift B = B := by
  ext o
  exact ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨o, h, rfl⟩⟩

/-- `S ⊑ T` at a program iff the identity is a valid compilation from `T` to `S`. -/
theorem valid_cast_iff (S T : X.Sem) (p : X.Prog) :
    Valid (X.cast T S) p p ↔ S p ⊆ T p := by
  rw [valid_iff_beh, cast_lift]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem refinesOn_iff_valid_cast {F : Set X.Prog} {S T : X.Sem} :
    (S ⊑[F] T) ↔ ∀ p ∈ F, Valid (X.cast T S) p p :=
  forall₂_congr fun p _ => (valid_cast_iff S T p).symm

/-- Casts compose. -/
theorem cast_comp (S T U : X.Sem) : X.cast S T ≫ X.cast T U = X.cast S U :=
  Convention.ext rfl Relation.eq_comp

/-- Precomposing a convention with a cast does not change it. -/
theorem cast_comp_eq {L' : Language.{u}} (S T : X.Sem) (c : X.lang T ⟶ L') :
    X.cast S T ≫ c = ⟨c.Φ, c.R⟩ :=
  Convention.ext rfl Relation.eq_comp

/-- A partial translation is valid for semantics `S` on fragment `F` at convention `c`. -/
def ValidOn {L' : Language.{u}} (F : Set X.Prog) (S : X.Sem) (c : X.lang S ⟶ L')
    (run : X.Prog → Option L'.Prog) : Prop :=
  ∀ p ∈ F, ∀ p', run p = some p' → Valid c p p'

/-- The same convention, read from another semantics of the source syntax. -/
def reSource {L' : Language.{u}} {S : X.Sem} (c : X.lang S ⟶ L') (T : X.Sem) :
    X.lang T ⟶ L' := ⟨c.Φ, c.R⟩

/-- **A compiler valid for a stepping stone is valid for what it refines.** If `S ⊑[F] T`,
a compilation valid for `S` on `F` is valid for `T` on `F` at the same convention. The proof
is the lax composition law: the identity is valid from `T` to `S` (`valid_cast_iff`), and
`Valid (cast T S) ∘ Valid c ⊆ Valid (cast T S ≫ c)`. -/
theorem ValidOn.of_refinesOn {L' : Language.{u}} {F : Set X.Prog} {S T : X.Sem}
    {c : X.lang S ⟶ L'} {run : X.Prog → Option L'.Prog} (hv : ValidOn F S c run)
    (h : S ⊑[F] T) : ValidOn F T (reSource c T) run := by
  intro p hp p' hrun
  have := valid_comp_le (X.cast T S) c p p'
    ⟨p, (valid_cast_iff S T p).2 (h p hp), hv p hp p' hrun⟩
  rwa [cast_comp_eq] at this

/-- A ladder: validity for the bottom rung on its fragment transfers to the top through a
chain of refinements on growing fragments. -/
theorem ValidOn.of_chain {L' : Language.{u}} {F G : Set X.Prog} {S T U : X.Sem}
    {c : X.lang S ⟶ L'} {run : X.Prog → Option L'.Prog} (hv : ValidOn F S c run)
    (h₁ : S ⊑[F] T) (h₂ : T ⊑[G] U) (hFG : F ⊆ G) : ValidOn F U (reSource c U) run :=
  hv.of_refinesOn (h₁.trans_of_subset h₂ hFG)

/-- A compiler (`Compiler`) for the language of `S` is valid for `S` on every fragment. -/
theorem _root_.Silmaril.Compile.Category.Compiler.validOn {L' : Language.{u}} {S : X.Sem}
    (C : Compiler (X.lang S) L') (F : Set X.Prog) : ValidOn F S C.conv C.run :=
  fun p _ p' h => C.sound p p' h

/-- What a stepping-stone compiler guarantees about the top semantics:
`beh(target) ⊆ c.lift (T p)`. -/
theorem ValidOn.sound_beh {L' : Language.{u}} {F : Set X.Prog} {S T : X.Sem}
    {c : X.lang S ⟶ L'} {run : X.Prog → Option L'.Prog} (hv : ValidOn F S c run)
    (h : S ⊑[F] T) {p : X.Prog} (hp : p ∈ F) {p' : L'.Prog} (hrun : run p = some p') :
    L'.beh p' ⊆ c.lift (T p) :=
  ((valid_iff_beh _ _ _).1 (hv.of_refinesOn h p hp p' hrun)).2

end Syntax

end Silmaril.Compile.Category
