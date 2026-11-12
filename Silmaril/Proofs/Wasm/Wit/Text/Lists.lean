module

public import Silmaril.Proofs.Wasm.Wit.Text.Basic

/-!
# WIT text: lists read back

The combinators `sepBy` (comma lists up to a closing token, with or without a
trailing comma) and `many` (item lists up to `}` or the end) read back what `prSep`,
`prTerm` and `flatMap` print, given that every element reads back.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Parse

macro "unfold_toks" : tactic =>
  `(tactic| simp only [toks_append, toks_cons, toks_nil, List.append_assoc, List.cons_append,
      List.nil_append, List.length_append, List.length_cons, List.length_nil] at *)

/-- What follows an element of a comma list closed by `cl`. -/
abbrev SepFollow (cl : Tok) (r : List Tok) : Prop :=
  r.head? = some (.sym ',') ∨ r.head? = some cl

/-- An element parser that reads back the printed elements of `xs`. -/
def ReadsSep {α : Type} (p : Nat → List Tok → Option (α × List Tok)) (pr : α → List PTok)
    (cl : Tok) (xs : List α) : Prop :=
  ∀ x ∈ xs, 0 < (pr x).length ∧ (∀ r, (toks (pr x) ++ r).head? ≠ some cl) ∧
    ∀ n r, (pr x).length ≤ n → SepFollow cl r → p n (toks (pr x) ++ r) = some (x, r)

theorem ReadsSep.tail {α : Type} {p : Nat → List Tok → Option (α × List Tok)}
    {pr : α → List PTok} {cl : Tok} {x : α} {xs : List α} (h : ReadsSep p pr cl (x :: xs)) :
    ReadsSep p pr cl xs := fun y hy => h y (by simp [hy])

theorem sepBy_prSep {α : Type} {p : Nat → List Tok → Option (α × List Tok)}
    {pr : α → List PTok} {cl : Tok} (hcl : cl ≠ .sym ',') :
    ∀ (xs : List α), ReadsSep p pr cl xs → ∀ n r, (prSep pr xs).length + 1 ≤ n →
      r.head? = some cl → sepBy p cl n (toks (prSep pr xs) ++ r) = some (xs, r)
  | [], _, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [prSep, sepBy, hr]
  | [x], hx, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨_, hh, hp⟩ := hx x (by simp)
    simp only [prSep] at h ⊢
    rw [sepBy]
    simp only [hh, ite_false]
    rw [hp m r (by omega) (.inr hr)]
    simp only
    have : r.head? ≠ some (.sym ',') := by rw [hr]; simpa using hcl
    simp [this]
  | x :: x' :: xs, hx, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hpos, hh, hp⟩ := hx x (by simp)
    simp only [prSep] at h ⊢
    unfold_toks
    rw [sepBy]
    simp only [hh, ite_false]
    rw [hp m _ (by omega) (.inl rfl)]
    simp only [List.head?_cons, List.tail_cons, ite_true]
    rw [sepBy_prSep hcl (x' :: xs) hx.tail m r (by omega) hr]
    rfl

theorem sepBy_prTerm {α : Type} {p : Nat → List Tok → Option (α × List Tok)}
    {pr : α → List PTok} {cl : Tok} :
    ∀ (xs : List α), ReadsSep p pr cl xs → ∀ n r, (prTerm pr xs).length + 1 ≤ n →
      r.head? = some cl → sepBy p cl n (toks (prTerm pr xs) ++ r) = some (xs, r)
  | [], _, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [prTerm, sepBy, hr]
  | x :: xs, hx, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hpos, hh, hp⟩ := hx x (by simp)
    simp only [prTerm] at h ⊢
    unfold_toks
    rw [sepBy]
    simp only [hh, ite_false]
    rw [hp m _ (by omega) (.inl rfl)]
    simp only [List.head?_cons, List.tail_cons, ite_true]
    rw [sepBy_prTerm xs hx.tail m r (by omega) hr]
    rfl

/-- An item parser that reads back the printed items of `xs`. -/
def ReadsMany {α : Type} (p : Nat → List Tok → Option (α × List Tok)) (pr : α → List PTok)
    (g : α → α) (xs : List α) : Prop :=
  ∀ x ∈ xs, 0 < (pr x).length ∧ (∀ r, (toks (pr x) ++ r).head? ≠ some (.sym '}')) ∧
    ∀ n r, (pr x).length ≤ n → p n (toks (pr x) ++ r) = some (g x, r)

theorem many_flatMap {α : Type} {p : Nat → List Tok → Option (α × List Tok)}
    {pr : α → List PTok} {g : α → α} :
    ∀ (xs : List α), ReadsMany p pr g xs → ∀ n r, (xs.flatMap pr).length + 1 ≤ n →
      (r.head? = some (.sym '}') ∨ r = []) →
      many p n (toks (xs.flatMap pr) ++ r) = some (xs.map g, r)
  | [], _, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [many, hr]
  | x :: xs, hx, n, r, h, hr => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hpos, hh, hp⟩ := hx x (by simp)
    simp only [List.flatMap_cons] at h ⊢
    unfold_toks
    have hne : toks (pr x) ++ (toks (xs.flatMap pr) ++ r) ≠ [] := by
      have : (toks (pr x)).length ≠ 0 := by rw [length_toks]; omega
      intro e; apply this; simp_all
    rw [many]
    simp only [hh, hne, false_or, ite_false]
    rw [hp m _ (by omega)]
    simp only
    rw [many_flatMap xs (fun y hy => hx y (by simp [hy])) m r (by omega) hr]
    rfl

end Silmaril.Wasm.Wit.Text
