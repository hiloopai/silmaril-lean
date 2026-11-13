module

public import Silmaril.Machine.CBackend.Behaviour.Observable.Defs
public import Mathlib.Order.Closure
public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Behaviour sets and refinement with undefined behaviour as top

A program denotes a *behaviour set* `B : Set (Observable E V X T F)`: every
observable that some run can show. Refinement is inclusion **up to undefined
behaviour**: undefined behaviour after the events `t` stands for every
observable whose trace extends `t` (CompCert's "going wrong" rule, with the
events before the undefined behaviour preserved). Optionally (`Exhaustion`,
the same axis as in `Outcome.Rel`) a target may also run out of a resource
after any trace prefix that the source can produce.

* `Observable.close x B` adds to `B` everything `B` allows. It is a closure
  operator (`Observable.closure`): extensive, monotone and idempotent.
* `Observable.Refines x tgt src` is `tgt ⊆ close x src`. It is a preorder
  (`refines_refl`, `Refines.trans`), monotone in the exhaustion axis
  (`Refines.mono_exh`) and equivalent to `close x tgt ⊆ close x src`
  (`refines_iff_close_subset`): refinement is the order of the lattice of
  closed behaviour sets.
* Undefined behaviour is absorbing: a source that is undefined from the start
  is refined by every target (`refines_of_undefined_nil`, `close_eq_univ`).
* On a safe source (no undefined behaviour) and with exhaustion forbidden,
  refinement is plain inclusion (`refines_iff_subset_of_safe`).

## The behavioural institution

Sentences over a signature are specifications `φ : Set (Observable …)`, a
program satisfies `φ` when its behaviour set is included (`Sat`). A
specification is *closed* if it contains everything its members allow.
Refinement is exactly preservation of every closed specification
(`refines_iff_sat`): this is the satisfaction condition of the identity
corridor, and the reason refinement is the right notion of correctness.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour

namespace Observable

universe uE uV uX uT uF

variable {E : Type uE} {V : Type uV} {X : Type uX} {T : Type uT} {F : Type uF}


/-! ## What a behaviour set allows -/

/-- `B` allows `o`: `o ∈ B`, or `B` has undefined behaviour after a prefix of
`o`'s trace, or (exhaustion allowed) `o` runs out of a resource after a prefix
of a trace of `B`. -/
def Allowed (x : Exhaustion) (B : Set (Observable E V X T F)) (o : Observable E V X T F) : Prop :=
  o ∈ B ∨ (∃ t, t <+: o.trace ∧ (⟨t, .undefined⟩ : Observable E V X T F) ∈ B) ∨
    (x = .allowed ∧ o.ending = .exhausted ∧ ∃ o' ∈ B, o.trace <+: o'.trace)

/-- The closure of a behaviour set: everything it allows. -/
def close (x : Exhaustion) (B : Set (Observable E V X T F)) : Set (Observable E V X T F) := {o | Allowed x B o}

/-- `tgt` refines `src`: every behaviour of `tgt` is allowed by `src`. -/
def Refines (x : Exhaustion) (tgt src : Set (Observable E V X T F)) : Prop := tgt ⊆ close x src

/-- A behaviour set is safe when it has no undefined behaviour. -/
def Safe (B : Set (Observable E V X T F)) : Prop := ∀ t, (⟨t, .undefined⟩ : Observable E V X T F) ∉ B

variable {x y : Exhaustion} {A B C : Set (Observable E V X T F)} {o : Observable E V X T F}

theorem mem_close : o ∈ close x B ↔ Allowed x B o := Iff.rfl

theorem subset_close (x : Exhaustion) (B : Set (Observable E V X T F)) : B ⊆ close x B := fun _ h => .inl h

theorem close_mono (h : A ⊆ B) : close x A ⊆ close x B := by
  rintro o (ho | ⟨t, ht, hu⟩ | ⟨hx, he, o', ho', hp⟩)
  · exact .inl (h ho)
  · exact .inr (.inl ⟨t, ht, h hu⟩)
  · exact .inr (.inr ⟨hx, he, o', h ho', hp⟩)

theorem close_mono_exh (h : x ≤ y) (B : Set (Observable E V X T F)) : close x B ⊆ close y B := by
  rintro o (ho | hu | ⟨hx, he, hw⟩)
  · exact .inl ho
  · exact .inr (.inl hu)
  · exact .inr (.inr ⟨Exhaustion.eq_allowed_of_le h hx, he, hw⟩)

theorem close_close (x : Exhaustion) (B : Set (Observable E V X T F)) : close x (close x B) = close x B := by
  refine (Set.Subset.antisymm ?_ (subset_close _ _))
  rintro o (ho | ⟨t, ht, hu⟩ | ⟨hx, he, o', ho', hp⟩)
  · exact ho
  · rcases hu with hu | ⟨t', ht', hu'⟩ | ⟨-, he', -⟩
    · exact .inr (.inl ⟨t, ht, hu⟩)
    · exact .inr (.inl ⟨t', ht'.trans ht, hu'⟩)
    · cases he'
  · rcases ho' with ho' | ⟨t, ht, hu⟩ | ⟨-, -, o'', ho'', hp'⟩
    · exact .inr (.inr ⟨hx, he, o', ho', hp⟩)
    · rcases List.prefix_or_prefix_of_prefix ht hp with h | h
      · exact .inr (.inl ⟨t, h, hu⟩)
      · exact .inr (.inr ⟨hx, he, _, hu, h⟩)
    · exact .inr (.inr ⟨hx, he, o'', ho'', hp.trans hp'⟩)

/-- `close x` is a closure operator on behaviour sets. -/
def closure (x : Exhaustion) : ClosureOperator (Set (Observable E V X T F)) :=
  ClosureOperator.mk' (close x) (fun _ _ => close_mono) (subset_close x)
    (fun B => (close_close x B).le)

@[simp] theorem closure_apply (x : Exhaustion) (B : Set (Observable E V X T F)) : closure x B = close x B := rfl

theorem close_union (x : Exhaustion) (A B : Set (Observable E V X T F)) :
    close x (A ∪ B) = close x A ∪ close x B := by
  ext o
  simp only [mem_close, Allowed, Set.mem_union]
  constructor
  · rintro ((h | h) | ⟨t, ht, h | h⟩ | ⟨hx, he, o', h | h, hp⟩)
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inl (.inr (.inl ⟨t, ht, h⟩))
    · exact .inr (.inr (.inl ⟨t, ht, h⟩))
    · exact .inl (.inr (.inr ⟨hx, he, o', h, hp⟩))
    · exact .inr (.inr (.inr ⟨hx, he, o', h, hp⟩))
  · rintro (h | h)
    · exact close_mono Set.subset_union_left h
    · exact close_mono Set.subset_union_right h

theorem close_iUnion {ι : Sort*} (x : Exhaustion) (B : ι → Set (Observable E V X T F)) :
    close x (⋃ i, B i) = ⋃ i, close x (B i) := by
  ext o
  simp only [mem_close, Allowed, Set.mem_iUnion]
  constructor
  · rintro (⟨i, h⟩ | ⟨t, ht, i, h⟩ | ⟨hx, he, o', ⟨i, h⟩, hp⟩)
    · exact ⟨i, .inl h⟩
    · exact ⟨i, .inr (.inl ⟨t, ht, h⟩)⟩
    · exact ⟨i, .inr (.inr ⟨hx, he, o', h, hp⟩)⟩
  · rintro ⟨i, h | ⟨t, ht, h⟩ | ⟨hx, he, o', h, hp⟩⟩
    · exact .inl ⟨i, h⟩
    · exact .inr (.inl ⟨t, ht, i, h⟩)
    · exact .inr (.inr ⟨hx, he, o', ⟨i, h⟩, hp⟩)

@[simp] theorem close_empty (x : Exhaustion) : close x (∅ : Set (Observable E V X T F)) = ∅ := by
  ext o
  simp [mem_close, Allowed]

/-! ## Undefined behaviour is top -/

/-- Undefined behaviour after `t` allows every observable extending `t`. -/
theorem mem_close_of_undefined {t : List E} (hu : (⟨t, .undefined⟩ : Observable E V X T F) ∈ B)
    (ht : t <+: o.trace) : o ∈ close x B :=
  .inr (.inl ⟨t, ht, hu⟩)

/-- A behaviour set that is undefined from the start allows everything. -/
theorem close_eq_univ (hu : (⟨[], .undefined⟩ : Observable E V X T F) ∈ B) : close x B = Set.univ :=
  Set.eq_univ_of_forall fun _ => mem_close_of_undefined hu (List.nil_prefix)

/-- On a safe set with exhaustion forbidden, the closure adds nothing. -/
theorem close_of_safe (hs : Safe B) : close .forbidden B = B := by
  refine Set.Subset.antisymm ?_ (subset_close _ _)
  rintro o (ho | ⟨t, -, hu⟩ | ⟨hx, -, -⟩)
  · exact ho
  · exact absurd hu (hs t)
  · cases hx

/-! ## Refinement -/

theorem refines_iff_close_subset : Refines x A B ↔ close x A ⊆ close x B :=
  (closure x).le_closure_iff

theorem refines_refl (x : Exhaustion) (B : Set (Observable E V X T F)) : Refines x B B := subset_close x B

theorem Refines.trans (h₁ : Refines x A B) (h₂ : Refines x B C) : Refines x A C :=
  refines_iff_close_subset.2 ((refines_iff_close_subset.1 h₁).trans
    (refines_iff_close_subset.1 h₂))

theorem Refines.of_subset (h : A ⊆ B) : Refines x A B := h.trans (subset_close x B)

theorem Refines.mono_exh (hxy : x ≤ y) (h : Refines x A B) : Refines y A B :=
  Set.Subset.trans h (close_mono_exh hxy B)

theorem Refines.mono_left {A' : Set (Observable E V X T F)} (hA : A' ⊆ A) (h : Refines x A B) : Refines x A' B :=
  hA.trans h

theorem Refines.mono_right {B' : Set (Observable E V X T F)} (hB : B ⊆ B') (h : Refines x A B) : Refines x A B' :=
  Set.Subset.trans h (close_mono hB)

theorem refines_union_left : Refines x (A ∪ B) C ↔ Refines x A C ∧ Refines x B C :=
  Set.union_subset_iff

theorem refines_iUnion_left {ι : Sort*} {A : ι → Set (Observable E V X T F)} :
    Refines x (⋃ i, A i) C ↔ ∀ i, Refines x (A i) C :=
  Set.iUnion_subset_iff

/-- **Undefined behaviour is absorbing**: everything refines a source that is
undefined from the start. -/
theorem refines_of_undefined_nil (hu : (⟨[], .undefined⟩ : Observable E V X T F) ∈ B) (A : Set (Observable E V X T F)) :
    Refines x A B := by
  rw [Refines, close_eq_univ hu]
  exact Set.subset_univ _

/-- The source is safe, so is the target. -/
theorem Refines.safe (h : Refines x A B) (hs : Safe B) : Safe A := by
  intro t ht
  rcases h ht with hu | ⟨t', -, hu⟩ | ⟨-, he, -⟩
  · exact hs t hu
  · exact hs t' hu
  · cases he

/-- Target undefined behaviour after `t` is matched by source undefined
behaviour after a prefix of `t`. -/
theorem Refines.undefined (h : Refines x A B) {t : List E} (ht : (⟨t, .undefined⟩ : Observable E V X T F) ∈ A) :
    ∃ t', t' <+: t ∧ (⟨t', .undefined⟩ : Observable E V X T F) ∈ B := by
  rcases h ht with hu | hu | ⟨-, he, -⟩
  · exact ⟨t, List.prefix_refl t, hu⟩
  · exact hu
  · cases he

/-- On a safe source with exhaustion forbidden, refinement is inclusion. -/
theorem refines_iff_subset_of_safe (hs : Safe B) : Refines .forbidden A B ↔ A ⊆ B := by
  rw [Refines, close_of_safe hs]

/-- What a refinement guarantees about one target behaviour on a safe source:
it is a source behaviour, or (exhaustion allowed) exhaustion after a prefix of
a source trace. -/
theorem Refines.mem_of_safe (h : Refines x A B) (hs : Safe B) (ho : o ∈ A) :
    o ∈ B ∨ (x = .allowed ∧ o.ending = .exhausted ∧ ∃ o' ∈ B, o.trace <+: o'.trace) := by
  rcases h ho with h | ⟨t, -, hu⟩ | h
  · exact .inl h
  · exact absurd hu (hs t)
  · exact .inr h

/-- Termination and trap-freedom: on a safe source, a target ending other than
exhaustion is a source ending with the same trace. -/
theorem Refines.mem_of_safe_of_ne (h : Refines x A B) (hs : Safe B) (ho : o ∈ A)
    (he : o.ending ≠ .exhausted) : o ∈ B :=
  (h.mem_of_safe hs ho).resolve_right fun ⟨_, h, _⟩ => he h

/-! ## Specifications: the behavioural institution -/

/-- A behaviour set satisfies a specification when it is included in it. -/
def Sat (B φ : Set (Observable E V X T F)) : Prop := B ⊆ φ

/-- A specification is closed if it contains everything its members allow. -/
def Closed (x : Exhaustion) (φ : Set (Observable E V X T F)) : Prop := close x φ ⊆ φ

theorem closed_close (x : Exhaustion) (B : Set (Observable E V X T F)) : Closed x (close x B) :=
  (close_close x B).le

/-- Refinement transports closed specifications. -/
theorem Refines.sat (h : Refines x A B) {φ : Set (Observable E V X T F)} (hφ : Closed x φ) (hB : Sat B φ) :
    Sat A φ :=
  Set.Subset.trans h ((close_mono hB).trans hφ)

/-- **Refinement is preservation of closed specifications.** -/
theorem refines_iff_sat :
    Refines x A B ↔ ∀ φ : Set (Observable E V X T F), Closed x φ → Sat B φ → Sat A φ :=
  ⟨fun h _ hφ hB => h.sat hφ hB, fun h => h _ (closed_close x B) (subset_close x B)⟩

end Observable

end Silmaril.Machine.Behaviour
