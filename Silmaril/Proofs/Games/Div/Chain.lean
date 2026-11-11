module

public import Silmaril.Games.Div.Defs

/-!
# Chains and infinite plays: proofs

Elementary facts about increasing chains of lists and their limits, and the
canonical chain enumerating an infinite play. Used by `Silmaril.Games.Div.Thms`.
-/

public section

namespace Silmaril.Proofs.Games.Div

open Silmaril.Games

universe v

variable {α : Type v}

theorem mono_le {c : Chain α} (hm : c.Mono) {n m : ℕ} (h : n ≤ m) : c n <+: c m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (hm _)

theorem length_mono {c : Chain α} (hm : c.Mono) {n m : ℕ} (h : n ≤ m) :
    (c n).length ≤ (c m).length :=
  (mono_le hm h).length_le

theorem unbounded_ge {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) (k n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ k ≤ (c n).length := by
  obtain ⟨n, hn⟩ := hu k
  exact ⟨max n n₀, le_max_right _ _, hn.trans (length_mono hm (le_max_left _ _))⟩

theorem lim_total {c : Chain α} (hm : c.Mono) {s t : List α} (hs : s ∈ c.lim) (ht : t ∈ c.lim) :
    s <+: t ∨ t <+: s := by
  obtain ⟨n, hn⟩ := hs
  obtain ⟨m, hm'⟩ := ht
  exact List.prefix_or_prefix_of_prefix (hn.trans (mono_le hm (le_max_left n m)))
    (hm'.trans (mono_le hm (le_max_right n m)))

theorem isInfPlay_lim {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) : IsInfPlay c.lim where
  of_prefix := fun ⟨n, hn⟩ h => ⟨n, h.trans hn⟩
  total := lim_total hm
  unbounded k := by
    obtain ⟨n, hn⟩ := hu k
    exact ⟨c n, ⟨n, List.prefix_refl _⟩, hn⟩

theorem prefix_of_length_le {I : Set (List α)} (h : IsInfPlay I) {s t : List α} (hs : s ∈ I)
    (ht : t ∈ I) (hl : s.length ≤ t.length) : s <+: t := by
  rcases h.total hs ht with h | h
  · exact h
  · rw [h.eq_of_length (le_antisymm h.length_le hl)]; exact List.prefix_refl _

/-- The member of length `n` of an infinite play. -/
noncomputable def seq {I : Set (List α)} (h : IsInfPlay I) : Chain α :=
  fun n => (Classical.choose (h.unbounded n)).take n

theorem seq_mem {I : Set (List α)} (h : IsInfPlay I) (n : ℕ) : seq h n ∈ I :=
  h.of_prefix (Classical.choose_spec (h.unbounded n)).1 (List.take_prefix _ _)

theorem seq_length {I : Set (List α)} (h : IsInfPlay I) (n : ℕ) : (seq h n).length = n := by
  simp only [seq, List.length_take]
  exact Nat.min_eq_left (Classical.choose_spec (h.unbounded n)).2

theorem seq_mono {I : Set (List α)} (h : IsInfPlay I) : (seq h).Mono := fun n =>
  prefix_of_length_le h (seq_mem h n) (seq_mem h (n + 1)) (by simp [seq_length])

theorem seq_unbounded {I : Set (List α)} (h : IsInfPlay I) : (seq h).Unbounded := fun k =>
  ⟨k, (seq_length h k).ge⟩

theorem lim_seq {I : Set (List α)} (h : IsInfPlay I) : (seq h).lim = I := by
  ext q
  constructor
  · rintro ⟨n, hn⟩
    exact h.of_prefix (seq_mem h n) hn
  · intro hq
    exact ⟨q.length, prefix_of_length_le h hq (seq_mem h _) (by simp [seq_length])⟩

/-- Two increasing chains whose members are mutually bounded by prefixes have
the same limit. -/
theorem lim_eq_of {c d : Chain α} (h₁ : ∀ n, ∃ m, c n <+: d m) (h₂ : ∀ n, ∃ m, d n <+: c m) :
    c.lim = d.lim := by
  ext q
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := h₁ n
    exact ⟨m, hn.trans hm⟩
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := h₂ n
    exact ⟨m, hn.trans hm⟩

theorem prefix_lim_iff {c : Chain α} {q : List α} : q ∈ c.lim ↔ ∃ n, q <+: c n := Iff.rfl

theorem mem_lim_self (c : Chain α) (n : ℕ) : c n ∈ c.lim := ⟨n, List.prefix_refl _⟩

private theorem unbounded_of_no_max {c : Chain α}
    (h : ∀ N, ∃ n, (c N).length < (c n).length) : c.Unbounded := by
  intro j
  induction j with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ j ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := h n
    exact ⟨m, by omega⟩

/-- A bounded chain has a member of maximal length. -/
theorem exists_max_length {c : Chain α} (hb : ¬ c.Unbounded) :
    ∃ N, ∀ n, (c n).length ≤ (c N).length := by
  by_contra hne
  push Not at hne
  exact hb (unbounded_of_no_max hne)

/-- A bounded increasing chain is eventually constant. -/
theorem eventually_const {c : Chain α} (hm : c.Mono) (hb : ¬ c.Unbounded) :
    ∃ N, ∀ n, N ≤ n → c n = c N := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ n, (c n).length ≤ (c N).length := exists_max_length hb
  refine ⟨N, fun n hn => ?_⟩
  have hp : c N <+: c n := mono_le hm hn
  exact (hp.eq_of_length (le_antisymm hp.length_le (hN n))).symm

end Silmaril.Proofs.Games.Div
