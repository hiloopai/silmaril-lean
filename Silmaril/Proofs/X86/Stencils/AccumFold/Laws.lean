module

public import Silmaril.X86.Stencils.AccumFold.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Nat.Even

/-!
# Deferred reduction of an accumulator fold: proofs
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Stencils.AccumFold

open Silmaril.X86.Stencils.AccumFold

theorem red_rawStep (M : Nat) (s : Nat × Nat) (b : BitVec 8) :
    red M (rawStep s b) = modStep M (red M s) b := by
  obtain ⟨s1, s2⟩ := s
  simp only [red, rawStep, modStep, Prod.mk.injEq]
  constructor
  · simp only [Nat.mod_add_mod]
  · simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem red_red (M : Nat) (s : Nat × Nat) : red M (red M s) = red M s := by
  simp [red]

theorem rawFold_mod (M : Nat) : ∀ (s : Nat × Nat) (bs : List (BitVec 8)),
    red M (rawFold s bs) = modFold M (red M s) bs
  | _, [] => rfl
  | s, b :: bs => by
    simp only [rawFold, modFold, List.foldl_cons] at *
    rw [show List.foldl rawStep (rawStep s b) bs = rawFold (rawStep s b) bs from rfl,
      rawFold_mod M _ bs, red_rawStep]; rfl

theorem modFold_append (M : Nat) (s : Nat × Nat) (xs ys : List (BitVec 8)) :
    modFold M s (xs ++ ys) = modFold M (modFold M s xs) ys := List.foldl_append

theorem chunked_eq_modFold (M N : Nat) (hN : 0 < N) (s : Nat × Nat) (bs : List (BitVec 8)) :
    chunked M N hN s bs = modFold M (red M s) bs := by
  rw [chunked]
  split
  · exact rawFold_mod M s bs
  · rw [chunked_eq_modFold M N hN _ (bs.drop N), red_red, rawFold_mod, ← modFold_append,
      List.take_append_drop]
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

theorem rawFold_bound : ∀ (s : Nat × Nat) (bs : List (BitVec 8)),
    (rawFold s bs).1 ≤ s.1 + 255 * bs.length ∧
      2 * (rawFold s bs).2 ≤ 2 * s.2 + 2 * bs.length * s.1 + 255 * bs.length * (bs.length + 1)
  | s, [] => by simp [rawFold]
  | s, b :: bs => by
    obtain ⟨h1, h2⟩ := rawFold_bound (rawStep s b) bs
    have hb : b.toNat ≤ 255 := by have := b.isLt; omega
    simp only [rawFold, List.foldl_cons, List.length_cons] at *
    simp only [rawStep] at h1 h2 ⊢
    have hb' : bs.length * b.toNat ≤ bs.length * 255 := Nat.mul_le_mul_left _ hb
    constructor
    · omega
    · nlinarith

theorem rawFold_lt {M N w : Nat} (hB : RawBound M N w) {s : Nat × Nat} (h1 : s.1 < M)
    (h2 : s.2 < M) {bs : List (BitVec 8)} (hn : bs.length ≤ N) :
    (rawFold s bs).1 < 2 ^ w ∧ (rawFold s bs).2 < 2 ^ w := by
  obtain ⟨b1, b2⟩ := rawFold_bound s bs
  have he : 2 * (N * (N + 1) / 2) = N * (N + 1) := by
    have : N * (N + 1) % 2 = 0 := by
      rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
    omega
  unfold RawBound at hB
  set n := bs.length
  have q1 : n * s.1 ≤ N * (M - 1) := Nat.mul_le_mul hn (by omega)
  have q2 : n * (n + 1) ≤ N * (N + 1) := Nat.mul_le_mul hn (by omega)
  have hY : (N + 1) * (M - 1) = N * (M - 1) + (M - 1) := by ring
  have hND : N ≤ N * (N + 1) / 2 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : N * 2 ≤ N * (N + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  have q1' : 2 * n * s.1 ≤ 2 * (N * (M - 1)) := by rw [Nat.mul_assoc]; omega
  have q2' : 255 * n * (n + 1) ≤ 255 * (N * (N + 1)) := by rw [Nat.mul_assoc]; omega
  constructor
  · omega
  · omega

end Silmaril.Proofs.X86.Stencils.AccumFold
