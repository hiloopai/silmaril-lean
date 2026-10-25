module

public import Silmaril.Compile.Category.Lattice

@[expose] public section

/-!
# Factorization of valid compilations through an intermediate language

The lax law (`valid_comp_le`) says that composing valid compilations `L → M → N` gives a valid
compilation at the composite convention: `Valid c ∘ Valid d ⊆ Valid (c ≫ d)`. This file is its
converse. Every valid compilation `L → N` factors through `M` as soon as `M` can *express* the
source's behaviours: there is an elaboration `e : L.Prog → M.Prog` with
`M.beh (e p) = c.lift (L.beh p)` (`Realises c F e`, on a fragment `F`). Then

  `Valid (c ≫ d) p r → Valid c p (e p) ∧ Valid d (e p) r`   (`Realises.factor`),

and, through a 2-cell `a ≤ c ≫ d`, every valid compilation at `a` factors (`Realises.factor_of_le`).
On `F` the lax law is an equality (`Realises.valid_comp_iff`). `valid_comp_eq`, the
equality for a realisable `M`, is the special case `F = univ` (`realises_of_realisable`).

For a three-language compiler diagram, if the intermediate language realises the typed
source through an elaboration, the direct and intermediate routes are interchangeable
at the level of validity.

Only the inclusion `c.lift (L.beh p) ⊆ M.beh (e p)` is needed for the second factor, and only
`M.beh (e p) ⊆ c.lift (L.beh p)` for the first (`Realises` asks for both).
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

variable {L M N : Language.{u}}

/-- `e` realises the convention `c : L ⟶ M` on the fragment `F`: the elaborated program has
the translated interface and exactly the translated behaviours. -/
structure Realises (c : L ⟶ M) (F : Set L.Prog) (e : L.Prog → M.Prog) : Prop where
  iface : ∀ p ∈ F, M.iface (e p) = c.Φ (L.iface p)
  beh : ∀ p ∈ F, M.beh (e p) = c.lift (L.beh p)

namespace Realises

variable {c : L ⟶ M} {F : Set L.Prog} {e : L.Prog → M.Prog}

/-- A realising elaboration is a valid compilation on the fragment. -/
theorem valid (h : Realises c F e) {p : L.Prog} (hp : p ∈ F) : Valid c p (e p) :=
  (valid_iff_beh c p (e p)).2 ⟨(h.iface p hp).symm, (h.beh p hp).subset⟩

/-- **Factorization.** On the fragment, a valid compilation at the composite convention
factors through the elaboration. -/
theorem factor (h : Realises c F e) {d : M ⟶ N} {p : L.Prog} (hp : p ∈ F) {r : N.Prog}
    (hv : Valid (c ≫ d) p r) : Valid c p (e p) ∧ Valid d (e p) r := by
  refine ⟨h.valid hp, (valid_iff_beh d (e p) r).2 ⟨?_, ?_⟩⟩
  · rw [h.iface p hp]
    exact hv.1
  · rw [h.beh p hp, ← Convention.lift_comp]
    exact ((valid_iff_beh _ p r).1 hv).2

/-- **Factorization through a 2-cell.** Every valid compilation at a convention `a` below
`c ≫ d` factors through `M`. -/
theorem factor_of_le (h : Realises c F e) {d : M ⟶ N} {a : L ⟶ N} (h2 : a ≤ c ≫ d)
    {p : L.Prog} (hp : p ∈ F) {r : N.Prog} (hv : Valid a p r) :
    ∃ q, Valid c p q ∧ Valid d q r :=
  ⟨e p, h.factor hp (valid_mono h2 p r hv)⟩

/-- On the fragment, the lax law is an equality. -/
theorem valid_comp_iff (h : Realises c F e) (d : M ⟶ N) {p : L.Prog} (hp : p ∈ F)
    (r : N.Prog) : Relation.Comp (Valid c) (Valid d) p r ↔ Valid (c ≫ d) p r :=
  ⟨fun hv => valid_comp_le c d p r hv, fun hv => ⟨e p, h.factor hp hv⟩⟩

/-- Realisation on a smaller fragment. -/
theorem mono (h : Realises c F e) {G : Set L.Prog} (hG : G ⊆ F) : Realises c G e :=
  ⟨fun p hp => h.iface p (hG hp), fun p hp => h.beh p (hG hp)⟩

end Realises

/-- A realisable intermediate language realises every convention on every program. -/
theorem realises_of_realisable (c : L ⟶ M) (hM : M.Realisable) :
    ∃ e, Realises c Set.univ e := by
  choose e he using fun p => hM (c.Φ (L.iface p)) (c.lift (L.beh p))
  exact ⟨e, fun p _ => (he p).1, fun p _ => (he p).2⟩

/-- `valid_comp_eq` recovered from factorization. -/
theorem valid_comp_eq' (c : L ⟶ M) (d : M ⟶ N) (hM : M.Realisable) :
    Relation.Comp (Valid c) (Valid d) = Valid (c ≫ d) := by
  obtain ⟨e, he⟩ := realises_of_realisable c hM
  funext p r
  exact propext (he.valid_comp_iff d (Set.mem_univ p) r)

/-- Realisation composes: elaborating twice realises the composite convention. -/
theorem Realises.comp {c : L ⟶ M} {d : M ⟶ N} {F : Set L.Prog} {G : Set M.Prog}
    {e : L.Prog → M.Prog} {e' : M.Prog → N.Prog} (h : Realises c F e) (h' : Realises d G e')
    (hFG : ∀ p ∈ F, e p ∈ G) : Realises (c ≫ d) F (e' ∘ e) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [Function.comp_apply, Convention.comp_Φ]
    rw [h'.iface _ (hFG p hp), h.iface p hp]
  · simp only [Function.comp_apply]
    rw [h'.beh _ (hFG p hp), h.beh p hp, Convention.lift_comp]

/-- The identity elaboration realises the identity convention everywhere. -/
theorem realises_id (L : Language.{u}) : Realises (𝟙 L) Set.univ id :=
  ⟨fun _ _ => rfl, fun _ _ => (Convention.lift_id _).symm⟩

end Silmaril.Compile.Category
