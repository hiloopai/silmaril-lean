module

public import Silmaril.Semantics.Accept.Items.Defs
import Mathlib.Algebra.Order.BigOperators.Group.List
import Cslib.Foundations.Data.OmegaSequence.Init
import Mathlib.Algebra.Group.Action.Defs

/-! # Proofs: item sequences -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Items

open Cslib Silmaril.Accept

universe u

variable {ι : Type u}

theorem itemsWithin_inter_countWithin_subset {μ : ι → ℕ} {n k : ℕ} :
    itemsWithin μ n ∩ countWithin k ⊆ totalWithin μ (k * n) := by
  rintro s ⟨hs, hk⟩
  have h := List.sum_le_length_nsmul (s.map μ) n fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact hs x hx
  simp only [List.length_map, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right n hk)

theorem itemsWithin_not_subset_totalWithin {μ w : ι → ℕ} {n : ℕ} {x : ι} (hx : μ x ≤ n)
    (hw : 0 < w x) (m : ℕ) : ¬ itemsWithin μ n ⊆ totalWithin w m := by
  intro h
  have hs := h (a := List.replicate (m + 1) x) fun y hy => (List.eq_of_mem_replicate hy) ▸ hx
  have he : totalWeight w (List.replicate (m + 1) x) = (m + 1) * w x := by
    simp [totalWeight, List.map_replicate, List.sum_replicate]
  have h2 : m + 1 ≤ (m + 1) * w x := Nat.le_mul_of_pos_right _ hw
  have h3 : (m + 1) * w x ≤ m := he ▸ hs
  omega

theorem mem_everyItemω_iff_take {L : Set ι} {s : ωSequence ι} :
    s ∈ everyItemω L ↔ ∀ n, s.take n ∈ everyItem L := by
  constructor
  · intro h n
    induction n with
    | zero => simp [everyItem, ωSequence.take_zero]
    | succ n ih =>
      rw [ωSequence.take_succ']
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact ih y hy
      · rw [List.mem_singleton.1 hy]; exact h n
  · intro h k
    have hk := h (k + 1)
    rw [ωSequence.take_succ'] at hk
    exact hk _ (List.mem_append_right _ (List.mem_singleton_self _))

end Silmaril.Proofs.Semantics.Accept.Items
