module

public import Silmaril.Semantics.Accept.Bounded.Defs
public import Silmaril.Semantics.Accept.Thms

/-!
# Bounded domains and checkers correct on a domain: laws

* `within`: membership, monotonicity in the bound (`within_mono`), intersection of bounds as a
  bound in the product order (`within_prod`), and the size slices of `Accept.upTo` as
  `L ∩ within size n` (`upTo_eq_inter_within`);
* relative correctness: `decidesOn_iff`, the unrelativised notions as `D = Set.univ`,
  restriction to smaller domains (`SoundOn.anti`, `CompleteOn.anti`, `DecidesOn.anti`) and to
  smaller bounds (`DecidesOn.within_mono`), monotonicity in the language, unions of domains,
  and exhaustion: correctness on every member of a covering family of domains is correctness
  everywhere (`decides_of_forall_within`);
* checkers that also enforce the bound: `decides_inter_iff` relates deciding `L ∩ D` to
  deciding `L` on `D` and rejecting outside `D`, and `DecidesOn.andBound` builds one.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v

variable {α : Type u} {β : Type v}

/-! ## Bounded domains -/

section Within

variable [Preorder β] {μ : α → β} {b c : β} {a : α}

@[simp] theorem mem_within : a ∈ within μ b ↔ μ a ≤ b := Iff.rfl

theorem within_mono (h : b ≤ c) : within μ b ⊆ within μ c := fun _ ha => le_trans ha h

/-- Bounding two measures at once is bounding the pair in the product order. -/
theorem within_prod {γ : Type*} [Preorder γ] {ν : α → γ} {d : γ} :
    within (fun a => (μ a, ν a)) (b, d) = within μ b ∩ within ν d := by
  ext; simp [Prod.mk_le_mk]

end Within

theorem upTo_eq_inter_within {size : α → ℕ} {n : ℕ} {L : Set α} :
    upTo size n L = L ∩ within size n := rfl

/-- Every input lies in some `ℕ`-bounded domain. -/
theorem iUnion_within (μ : α → ℕ) : ⋃ n, within μ n = Set.univ :=
  Set.eq_univ_of_forall fun a => Set.mem_iUnion.2 ⟨μ a, mem_within.2 le_rfl⟩

/-! ## Correctness relative to a domain -/

section Relative

variable {D D' : Set α} {c : α → Bool} {L L' : Set α}

theorem decidesOn_iff : DecidesOn D c L ↔ SoundOn D c L ∧ CompleteOn D c L :=
  ⟨fun h => ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩,
    fun h a ha => ⟨h.1 a ha, h.2 a ha⟩⟩

theorem DecidesOn.soundOn (h : DecidesOn D c L) : SoundOn D c L := (decidesOn_iff.1 h).1

theorem DecidesOn.completeOn (h : DecidesOn D c L) : CompleteOn D c L := (decidesOn_iff.1 h).2

@[simp] theorem soundOn_univ : SoundOn Set.univ c L ↔ Sound c L :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

@[simp] theorem completeOn_univ : CompleteOn Set.univ c L ↔ Complete c L :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

@[simp] theorem decidesOn_univ : DecidesOn Set.univ c L ↔ Decides c L :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

theorem Sound.soundOn (h : Sound c L) (D : Set α) : SoundOn D c L := fun a _ => h a

theorem Complete.completeOn (h : Complete c L) (D : Set α) : CompleteOn D c L := fun a _ => h a

theorem Decides.decidesOn (h : Decides c L) (D : Set α) : DecidesOn D c L := fun a _ => h a

/-- Restricting to a smaller domain keeps soundness. -/
theorem SoundOn.anti (h : SoundOn D c L) (hD : D' ⊆ D) : SoundOn D' c L :=
  fun a ha => h a (hD ha)

/-- Restricting to a smaller domain keeps completeness. -/
theorem CompleteOn.anti (h : CompleteOn D c L) (hD : D' ⊆ D) : CompleteOn D' c L :=
  fun a ha => h a (hD ha)

theorem DecidesOn.anti (h : DecidesOn D c L) (hD : D' ⊆ D) : DecidesOn D' c L :=
  fun a ha => h a (hD ha)

/-- Soundness weakens to larger languages. -/
theorem SoundOn.mono (h : SoundOn D c L) (hL : L ⊆ L') : SoundOn D c L' :=
  fun a ha hc => hL (h a ha hc)

/-- Completeness weakens to smaller languages. -/
theorem CompleteOn.mono (h : CompleteOn D c L') (hL : L ⊆ L') : CompleteOn D c L :=
  fun a ha hl => h a ha (hL hl)

/-- Only the part of the language inside the domain matters. -/
theorem decidesOn_inter_iff : DecidesOn D c (L ∩ D) ↔ DecidesOn D c L :=
  ⟨fun h a ha => (h a ha).trans ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩,
    fun h a ha => (h a ha).trans ⟨fun h => ⟨h, ha⟩, fun h => h.1⟩⟩

/-- A checker correct for a large bound is correct for every smaller one. -/
theorem DecidesOn.within_mono [Preorder β] {μ : α → β} {b b' : β}
    (h : DecidesOn (within μ b') c L) (hb : b ≤ b') : DecidesOn (within μ b) c L :=
  h.anti (Accept.within_mono hb)

theorem SoundOn.union (h : SoundOn D c L) (h' : SoundOn D' c L) : SoundOn (D ∪ D') c L :=
  fun a ha => ha.elim (h a) (h' a)

theorem CompleteOn.union (h : CompleteOn D c L) (h' : CompleteOn D' c L) :
    CompleteOn (D ∪ D') c L := fun a ha => ha.elim (h a) (h' a)

theorem DecidesOn.union (h : DecidesOn D c L) (h' : DecidesOn D' c L) :
    DecidesOn (D ∪ D') c L := fun a ha => ha.elim (h a) (h' a)

/-- Correct on every domain of a family is correct on its union. -/
theorem DecidesOn.iUnion {ι : Sort*} {D : ι → Set α} (h : ∀ i, DecidesOn (D i) c L) :
    DecidesOn (⋃ i, D i) c L := fun a ha =>
  let ⟨i, hi⟩ := Set.mem_iUnion.1 ha; h i a hi

theorem CompleteOn.iUnion {ι : Sort*} {D : ι → Set α} (h : ∀ i, CompleteOn (D i) c L) :
    CompleteOn (⋃ i, D i) c L := fun a ha =>
  let ⟨i, hi⟩ := Set.mem_iUnion.1 ha; h i a hi

/-- Exhaustion: a single checker complete on every `ℕ`-bounded domain is complete. Bounded
completeness for *every* bound is unbounded completeness. -/
theorem complete_of_forall_within {μ : α → ℕ} (h : ∀ n, CompleteOn (within μ n) c L) :
    Complete c L :=
  completeOn_univ.1 (iUnion_within μ ▸ CompleteOn.iUnion h)

theorem decides_of_forall_within {μ : α → ℕ} (h : ∀ n, DecidesOn (within μ n) c L) :
    Decides c L :=
  decidesOn_univ.1 (iUnion_within μ ▸ DecidesOn.iUnion h)

/-! ## Checkers that enforce their domain -/

/-- Deciding the bounded language `L ∩ D` is deciding `L` on `D` while rejecting
outside `D`. -/
theorem decides_inter_iff : Decides c (L ∩ D) ↔ DecidesOn D c L ∧ Sound c D :=
  ⟨fun h => ⟨decidesOn_inter_iff.1 (h.decidesOn D), fun a ha => ((h a).1 ha).2⟩,
    fun ⟨h, hs⟩ a => ⟨fun hc => ⟨(h a (hs a hc)).1 hc, hs a hc⟩, fun hl => (h a hl.2).2 hl.1⟩⟩

/-- A checker correct on `D`, conjoined with a checker for `D`, decides `L ∩ D`. -/
theorem DecidesOn.andBound {d : α → Bool} (h : DecidesOn D c L) (hd : Decides d D) :
    Decides (fun a => d a && c a) (L ∩ D) := fun a => by
  rw [Bool.and_eq_true, hd a, Set.mem_inter_iff]
  exact ⟨fun ⟨hD, hc⟩ => ⟨(h a hD).1 hc, hD⟩, fun ⟨hl, hD⟩ => ⟨hD, (h a hD).2 hl⟩⟩

end Relative

end Silmaril.Accept
