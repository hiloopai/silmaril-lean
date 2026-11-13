module

public import Silmaril.Wasm.Wac.Text.Parse.Defs

/-!
# WAC text: generic lemmas for the parser round trip

The head token of a token list (`hd?`), the token tests and consumers of the parser on
known heads, and `delim` on comma lists (`commaList`) and on concatenated items.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- The token at the head. -/
def hd? (ts : Toks) : Option Tok := ts.head?.map (·.tok)

@[simp] theorem hd?_cons (a : ATok) (r : Toks) : hd? (a :: r) = some a.tok := rfl
@[simp] theorem hd?_nil : hd? [] = none := rfl

namespace Parse

theorem isTok_eq (t : Tok) (ts : Toks) : isTok t ts = (hd? ts == some t) := by
  cases ts <;> simp [isTok, hd?]

@[simp] theorem isTok_cons (t : Tok) (a : ATok) (r : Toks) : isTok t (a :: r) = (a.tok == t) :=
  rfl

theorem isTok_of_ne {t : Tok} {ts : Toks} (h : hd? ts ≠ some t) : isTok t ts = false := by
  cases ts with
  | nil => rfl
  | cons a r => simpa [isTok] using h

@[simp] theorem expect_cons (t : Tok) (a : ATok) (r : Toks) :
    expect t (a :: r) = if a.tok = t then some r else none := rfl

@[simp] theorem sym_cons (c : Char) (a : ATok) (r : Toks) :
    sym c (a :: r) = if a.tok = .sym c then some r else none := rfl

theorem sym_of_ne {c : Char} {ts : Toks} (h : hd? ts ≠ some (.sym c)) : sym c ts = none := by
  cases ts with
  | nil => rfl
  | cons a r => simpa [sym, expect] using h

@[simp] theorem ident_id (ds : Docs) (s : String) (r : Toks) :
    ident (⟨ds, .id s⟩ :: r) = some (s, r) := rfl

@[simp] theorem str_str (ds : Docs) (s : String) (r : Toks) :
    str (⟨ds, .str s⟩ :: r) = some (s, r) := rfl

end Parse

open Parse


theorem commaList_cons_cons {α : Type} (f : α → Toks) (a b : α) (r : List α) :
    commaList f (a :: b :: r) = f a ++ sy ',' :: commaList f (b :: r) := rfl

/-- `commaList` of a nonempty list starts with its first item. -/
theorem hd?_commaList {α : Type} (f : α → Toks) (a : α) (r : List α) (rest : Toks)
    (h : f a ≠ []) : hd? (commaList f (a :: r) ++ rest) = hd? (f a) := by
  cases r with
  | nil => obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil h; simp [commaList, hx]
  | cons b r => obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil h; simp [commaList, hx]

/-- `delim` with commas reads back a comma list followed by its closing symbol. -/
theorem delim_commaList {α : Type} (p : Toks → Option (α × Toks)) (f : α → Toks)
    (close : Char) (hc : close ≠ ',') :
    ∀ (as : List α) (n : Nat) (rest : Toks),
      (∀ a ∈ as, ∀ r, (hd? r = some (.sym ',') ∨ hd? r = some (.sym close)) →
        p (f a ++ r) = some (a, r)) →
      (∀ a ∈ as, f a ≠ [] ∧ hd? (f a) ≠ some (.sym close)) → as.length < n →
      delim p close true n (commaList f as ++ sy close :: rest) = some (as, sy close :: rest)
  | [], n + 1, rest, _, _, _ => by simp [delim, commaList]
  | [a], n + 1, rest, hp, hne, _ => by
    have h1 : p (f a ++ sy close :: rest) = some (a, sy close :: rest) := hp a (by simp) _ (by simp)
    have h2 : isTok (.sym close) (f a ++ sy close :: rest) = false := by
      rw [isTok_eq]; obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil (hne a (by simp)).1
      have := (hne a (by simp)).2; simp_all
    rw [commaList, delim]; simp only [h1, h2]; simp
  | a :: b :: as, n + 1, rest, hp, hne, hl => by
    have h1 : p (f a ++ sy ',' :: (commaList f (b :: as) ++ sy close :: rest)) =
        some (a, sy ',' :: (commaList f (b :: as) ++ sy close :: rest)) :=
      hp a (by simp) _ (by simp)
    have h2 : isTok (.sym close) (f a ++ sy ',' :: (commaList f (b :: as) ++ sy close :: rest))
        = false := by
      rw [isTok_eq]; obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil (hne a (by simp)).1
      have := (hne a (by simp)).2; simp_all
    have ih := delim_commaList p f close hc (b :: as) n rest
      (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      (by simp at hl ⊢; omega)
    rw [commaList_cons_cons, delim]; simp only [List.append_assoc, List.cons_append, h1, h2]
    simp [ih, Ne.symm hc]

/-- `delim` without commas reads back concatenated items followed by the closing
symbol. -/
theorem delim_flatMap {α : Type} (p : Toks → Option (α × Toks)) (f : α → Toks) (close : Char) :
    ∀ (as : List α) (n : Nat) (rest : Toks),
      (∀ a ∈ as, ∀ r, p (f a ++ r) = some (a, r)) →
      (∀ a ∈ as, f a ≠ [] ∧ hd? (f a) ≠ some (.sym close)) → as.length < n →
      delim p close false n (as.flatMap f ++ sy close :: rest) = some (as, sy close :: rest)
  | [], n + 1, rest, _, _, _ => by simp [delim]
  | a :: as, n + 1, rest, hp, hne, hl => by
    have h1 : p (f a ++ (as.flatMap f ++ sy close :: rest)) =
        some (a, as.flatMap f ++ sy close :: rest) := hp a (by simp) _
    have h2 : isTok (.sym close) (f a ++ (as.flatMap f ++ sy close :: rest)) = false := by
      rw [isTok_eq]; obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil (hne a (by simp)).1
      have := (hne a (by simp)).2; simp_all
    have ih := delim_flatMap p f close as n rest
      (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      (by simp at hl ⊢; omega)
    cases as with
    | nil => rw [delim]; simp only [List.flatMap_nil, List.nil_append] at h1 h2 ⊢; simp [h1, h2]
    | cons b bs =>
      have h3 : isTok (.sym close) ((b :: bs).flatMap f ++ sy close :: rest) = false := by
        rw [isTok_eq]; obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil (hne b (by simp)).1
        have := (hne b (by simp)).2; simp_all
      simp only [List.flatMap_cons, List.append_assoc] at h1 h2 h3 ih ⊢
      rw [delim]; simp [h1, h2, h3, ih]

/-- An item of a comma list is no longer than the list. -/
theorem length_le_commaList {α : Type} (f : α → Toks) :
    ∀ (as : List α) (a : α), a ∈ as → (f a).length ≤ (commaList f as).length
  | [], _, h => by simp at h
  | [b], a, h => by simp at h; subst h; simp [commaList]
  | b :: c :: r, a, h => by
    rw [commaList_cons_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := length_le_commaList f (c :: r) a h; simp; omega

/-- A comma list is at least as long as the list. -/
theorem length_le_commaList' {α : Type} (f : α → Toks) (hf : ∀ a, f a ≠ []) :
    ∀ as : List α, as.length ≤ (commaList f as).length
  | [] => by simp [commaList]
  | [a] => by have := List.length_pos_iff.mpr (hf a); simp [commaList]; omega
  | a :: b :: r => by
    have h1 := length_le_commaList' f hf (b :: r)
    have := List.length_pos_iff.mpr (hf a)
    simp only [List.length_cons] at h1
    rw [commaList_cons_cons]; simp; omega

theorem length_le_flatMap_of_mem {α : Type} (f : α → Toks) {as : List α} {a : α}
    (h : a ∈ as) : (f a).length ≤ (as.flatMap f).length := by
  induction as with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [List.flatMap_cons, List.length_append]; omega
    · have := ih h; simp only [List.flatMap_cons, List.length_append]; omega

theorem length_le_flatMap {α : Type} (f : α → Toks) (hf : ∀ a, f a ≠ []) (as : List α) :
    as.length ≤ (as.flatMap f).length := by
  induction as with
  | nil => simp
  | cons b bs ih =>
    have := List.length_pos_iff.mpr (hf b)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

end Silmaril.Wasm.Wac.Text
