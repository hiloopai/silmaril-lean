module

public import Silmaril.Formats.SExp.EncodingWatLex

/-!
# Uniqueness of WAT bracketing

The token list of a `Tree` is balanced, a balanced list followed by `)` is
determined (`bal_rp_unique`), so trees are prefix-unique and `Trees` is
functional (`trees_functional`).
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

theorem Balanced.append {a b : List Tok} (h₁ : Balanced a) (h₂ : Balanced b) :
    Balanced (a ++ b) := by
  induction h₁ with
  | nil => simpa using h₂
  | @tok t ts hl hr _ ih => exact .tok hl hr ih
  | @group a' b' ha _ _ ih => simpa using Balanced.group ha ih

mutual
  theorem Tree.balanced : ∀ {ts : List Tok} {x : SExp}, Tree ts x → Balanced ts
    | _, _, .atom _ => .tok (by simp) (by simp) .nil
    | _, _, .list h => .group (Trees.balanced h) .nil

  theorem Trees.balanced : ∀ {ts : List Tok} {xs : List SExp}, Trees ts xs → Balanced ts
    | _, _, .nil => .nil
    | _, _, .cons h₁ h₂ => (Tree.balanced h₁).append (Trees.balanced h₂)
end

theorem Tree.ne_nil {ts : List Tok} {x : SExp} (h : Tree ts x) : ts ≠ [] := by
  cases h <;> simp

/-- A balanced list followed by `)` is determined. -/
theorem bal_rp_unique {a a' b b' : List Tok} (h₁ : Balanced a) (h₂ : Balanced a')
    (h : a ++ .rp :: b = a' ++ .rp :: b') : a = a' := by
  rcases List.append_eq_append_iff.mp h with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
  · cases k with
    | nil => simp
    | cons v k =>
      simp only [List.cons_append, List.cons.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact (Balanced.not_append_rp h₁ h₂).elim
  · cases k with
    | nil => simp
    | cons v k =>
      simp only [List.cons_append, List.cons.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact (Balanced.not_append_rp h₂ h₁).elim

theorem tree_unique : ∀ (n : Nat),
    (∀ {a₁ a₂ b₁ b₂ : List Tok} {x₁ x₂ : SExp}, (a₁ ++ b₁).length < n → Tree a₁ x₁ →
      Tree a₂ x₂ → a₁ ++ b₁ = a₂ ++ b₂ → a₁ = a₂ ∧ x₁ = x₂) ∧
    (∀ {l l' : List Tok} {xs₁ xs₂ : List SExp}, l.length < n → l = l' → Trees l xs₁ →
      Trees l' xs₂ → xs₁ = xs₂)
  | 0 => ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨-, ihS⟩ := tree_unique n
    have hT : ∀ {a₁ a₂ b₁ b₂ : List Tok} {x₁ x₂ : SExp}, (a₁ ++ b₁).length < n + 1 →
        Tree a₁ x₁ → Tree a₂ x₂ → a₁ ++ b₁ = a₂ ++ b₂ → a₁ = a₂ ∧ x₁ = x₂ := by
      intro a₁ a₂ b₁ b₂ x₁ x₂ hn h₁ h₂ h
      cases h₁ with
      | atom a =>
        cases h₂ with
        | atom a' =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq, Tok.atom.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨rfl, rfl⟩
        | list _ => simp at h
      | @list ts xs hs =>
        cases h₂ with
        | atom _ => simp at h
        | @list ts' xs' hs' =>
          simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
          have hts : ts = ts' := bal_rp_unique (Trees.balanced hs) (Trees.balanced hs') h
          subst hts
          have hn' : ts.length < n := by
            simp only [List.cons_append, List.length_cons, List.length_append] at hn
            omega
          rw [ihS hn' rfl hs hs']
          exact ⟨rfl, rfl⟩
    refine ⟨hT, ?_⟩
    intro l l' xs₁ xs₂ hn hl h₁ h₂
    cases h₁ with
    | nil =>
      cases h₂ with
      | nil => rfl
      | @cons a b x xs ha _ =>
        have := ha.ne_nil
        simp_all
    | @cons a b x xs ha hb =>
      cases h₂ with
      | nil =>
        have := ha.ne_nil
        simp_all
      | @cons a' b' x' xs' ha' hb' =>
        obtain ⟨rfl, rfl⟩ := hT hn ha ha' hl
        have := List.length_pos_iff.mpr ha.ne_nil
        rw [ihS (by simp only [List.length_append] at hn; omega) (List.append_cancel_left hl)
          hb hb']

/-- Bracketing is unique. -/
theorem trees_functional {ts : List Tok} {xs ys : List SExp} (h₁ : Trees ts xs)
    (h₂ : Trees ts ys) : xs = ys :=
  (tree_unique _).2 (Nat.lt_succ_self _) rfl h₁ h₂

end Silmaril.Formats.SExpEncoding.Wat
