module

public import Silmaril.Logic.Institution.Hets.StructuredSpec

@[expose] public section

/-!
# Free and cofree model classes

The model classes of Sannella–Tarlecki's `free` construct (CASL's `free { … }`, DOL's
`%free`) and of its dual `cofree`, over an arbitrary institution `I : Sign ⥤ Room`, whose model
categories carry the homomorphisms used here.

For `σ : Σ ⟶ Σ'` and a class `𝓜` of `Σ'`-models, a model `M ∈ 𝓜` is *free over its
`σ`-reduct* within `𝓜` when every homomorphism `M|σ ⟶ N|σ` into the reduct of some `N ∈ 𝓜`
extends uniquely to a homomorphism `M ⟶ N`; `freeModels σ 𝓜` collects these models
(persistent freeness relative to `𝓜`). `cofreeModels` is the dual.

* `freeModels_subset`, `cofreeModels_subset`: free and cofree models are models.
* `freeModels_id`, `cofreeModels_id`: along the identity, every model is free and cofree.

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1 (PDF
  page 19, footnote 2: "[18] provide also further operations such as e.g. data
  (=freeness)").
* `cofi-2004-casl-reference-manual` in `references.bib`: free and cofree specifications.
* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Definition 5.10, clause 5
  (printed page 134, PDF page 136: models of nodes with incoming free definition links).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- `M` is free over its `σ`-reduct within the class `𝓜`: every homomorphism from `M|σ` to the
reduct of a model in `𝓜` extends uniquely along `σ`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Definition 5.10
(printed page 134, PDF page 136: free definition links). -/
def IsFreeOver {S S' : Sign} (σ : S ⟶ S') (𝓜 : Set (I.obj S').Mod) (M : (I.obj S').Mod) :
    Prop :=
  ∀ N ∈ 𝓜, ∀ h : (I.map σ).mod.obj M ⟶ (I.map σ).mod.obj N,
    ∃! h' : M ⟶ N, (I.map σ).mod.map h' = h

/-- `M` is cofree over its `σ`-reduct within `𝓜`: every homomorphism into `M|σ` from the
reduct of a model in `𝓜` extends uniquely along `σ`. -/
def IsCofreeOver {S S' : Sign} (σ : S ⟶ S') (𝓜 : Set (I.obj S').Mod) (M : (I.obj S').Mod) :
    Prop :=
  ∀ N ∈ 𝓜, ∀ h : (I.map σ).mod.obj N ⟶ (I.map σ).mod.obj M,
    ∃! h' : N ⟶ M, (I.map σ).mod.map h' = h

/-- The models of `free 𝓜 along σ`: the models of `𝓜` free over their `σ`-reducts. -/
def freeModels {S S' : Sign} (σ : S ⟶ S') (𝓜 : Set (I.obj S').Mod) : Set (I.obj S').Mod :=
  {M | M ∈ 𝓜 ∧ IsFreeOver I σ 𝓜 M}

/-- The models of `cofree 𝓜 along σ`. -/
def cofreeModels {S S' : Sign} (σ : S ⟶ S') (𝓜 : Set (I.obj S').Mod) : Set (I.obj S').Mod :=
  {M | M ∈ 𝓜 ∧ IsCofreeOver I σ 𝓜 M}

variable {I}

/-- Along a corridor equal to the identity, every homomorphism between reducts lifts uniquely. -/
theorem existsUnique_map_of_eq_id {R : Room.{w, m₁, m₂}} (c : R ⟶ R) (hc : c = 𝟙 R)
    {M N : R.Mod} (h : c.mod.obj M ⟶ c.mod.obj N) : ∃! h' : M ⟶ N, c.mod.map h' = h := by
  subst hc
  exact ⟨h, rfl, fun _ hh => hh⟩

theorem freeModels_subset {S S' : Sign} (σ : S ⟶ S') (𝓜 : Set (I.obj S').Mod) :
    freeModels I σ 𝓜 ⊆ 𝓜 :=
  fun _ h => h.1

theorem cofreeModels_subset {S S' : Sign} (σ : S ⟶ S') (𝓜 : Set (I.obj S').Mod) :
    cofreeModels I σ 𝓜 ⊆ 𝓜 :=
  fun _ h => h.1

/-- Along the identity every model is free. -/
theorem freeModels_id {S : Sign} (𝓜 : Set (I.obj S).Mod) : freeModels I (𝟙 S) 𝓜 = 𝓜 :=
  Set.ext fun _ => ⟨fun h => h.1, fun hM =>
    ⟨hM, fun _ _ h => existsUnique_map_of_eq_id _ (I.map_id S) h⟩⟩

/-- Along the identity every model is cofree. -/
theorem cofreeModels_id {S : Sign} (𝓜 : Set (I.obj S).Mod) : cofreeModels I (𝟙 S) 𝓜 = 𝓜 :=
  Set.ext fun _ => ⟨fun h => h.1, fun hM =>
    ⟨hM, fun _ _ h => existsUnique_map_of_eq_id _ (I.map_id S) h⟩⟩

end Silmaril.Logic.Institution
