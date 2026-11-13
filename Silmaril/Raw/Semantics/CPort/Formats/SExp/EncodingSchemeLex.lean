module

public import Silmaril.Semantics.CPort.Formats.SExp.EncodingSchemeDefs.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-!
# Scheme S-expression text: the lexical grammar is unambiguous

Prefix uniqueness of comments, intertoken space, string and `|symbol|`
literals, bare tokens and single tokens, giving `lex_functional`.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Scheme

open Silmaril

/-! ## Maximal runs -/

/-- A run of `P`-characters followed by a non-`P` character (or the end) is
determined by the text. -/
theorem run_unique (P : Char → Prop) {w w' x x' : Chars}
    (hw : ∀ c ∈ w, P c) (hw' : ∀ c ∈ w', P c)
    (hx : ∀ c, x.head? = some c → ¬ P c) (hx' : ∀ c, x'.head? = some c → ¬ P c)
    (h : w ++ x = w' ++ x') : w = w' := by
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons c w' =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      exact absurd (hw' c (by simp)) (hx c rfl)
  | cons c w ih =>
    cases w' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      exact absurd (hw c (by simp)) (hx' c rfl)
    | cons c' w' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [ih (fun d hd => hw d (by simp [hd])) (fun d hd => hw' d (by simp [hd])) h]

/-! ## Comments and intertoken space -/

theorem nestedTail_ne_nil {t : Chars} (h : NestedTail t) : t ≠ [] := by
  cases h with
  | close => simp
  | char => simp
  | hash => simp
  | bar => simp
  | nested ha _ =>
    cases ha
    simp

theorem nested_shape {a : Chars} (h : Nested a) : ∃ t, a = '#' :: '|' :: t ∧ NestedTail t := by
  cases h with
  | mk ht => exact ⟨_, rfl, ht⟩

theorem nestedTail_unique (n : Nat) : ∀ t t' r r' : Chars, t.length ≤ n → NestedTail t →
    NestedTail t' → t ++ r = t' ++ r' → t = t' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t t' r r' hn ht ht' he
  cases ht with
  | close =>
    cases ht' with
    | close => rfl
    | char _ h2 _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | hash _ _ => simp at he
    | @bar r₀ hb hr₀ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
      obtain ⟨c, r₁, rfl⟩ := List.exists_cons_of_ne_nil (nestedTail_ne_nil hr₀)
      simp only [List.cons_append, List.cons.injEq] at he
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hb
      exact absurd he.1.symm hb
    | nested ha _ =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp at he
  | @char c r₀ h1 h2 hr₀ =>
    cases ht' with
    | @char c' r₀' _ _ hr₀' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      simp only [List.length_cons] at hn
      rw [ih r₀.length (by omega) r₀ r₀' r r' le_rfl hr₀ hr₀' he]
    | close =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact absurd he.1 h2
    | hash _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h1
    | bar _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h2
    | nested ha _ =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at he
      exact absurd he.1 h1
  | @hash r₀ hb hr₀ =>
    cases ht' with
    | @hash r₀' _ hr₀' =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      simp only [List.length_cons] at hn
      rw [ih r₀.length (by omega) r₀ r₀' r r' le_rfl hr₀ hr₀' he]
    | close => simp at he
    | char h1 _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h1
    | bar _ _ => simp at he
    | nested ha _ =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain ⟨c, r₁, rfl⟩ := List.exists_cons_of_ne_nil (nestedTail_ne_nil hr₀)
      simp only [List.cons_append, List.cons.injEq] at he
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hb
      exact absurd he.1 hb
  | @bar r₀ hb hr₀ =>
    cases ht' with
    | @bar r₀' _ hr₀' =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      simp only [List.length_cons] at hn
      rw [ih r₀.length (by omega) r₀ r₀' r r' le_rfl hr₀ hr₀' he]
    | close =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
      obtain ⟨c, r₁, rfl⟩ := List.exists_cons_of_ne_nil (nestedTail_ne_nil hr₀)
      simp only [List.cons_append, List.cons.injEq] at he
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hb
      exact absurd he.1 hb
    | char _ h2 _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | hash _ _ => simp at he
    | nested ha _ =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp at he
  | @nested a r₀ ha hr₀ =>
    obtain ⟨u, rfl, hu⟩ := nested_shape ha
    simp only [List.length_append, List.length_cons] at hn
    cases ht' with
    | @nested a' r₀' ha' hr₀' =>
      obtain ⟨u', rfl, hu'⟩ := nested_shape ha'
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain rfl := ih u.length (by omega) u u' _ _ le_rfl hu hu' he
      have he' := List.append_cancel_left he
      rw [ih r₀.length (by omega) r₀ r₀' r r' le_rfl hr₀ hr₀' he']
    | close => simp at he
    | char h1 _ _ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at he
      exact absurd he.1.symm h1
    | @hash r₀' hb hr₀' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain ⟨c, r₁, rfl⟩ := List.exists_cons_of_ne_nil (nestedTail_ne_nil hr₀')
      simp only [List.cons_append, List.cons.injEq] at he
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hb
      exact absurd he.1.symm hb
    | bar _ _ => simp at he

theorem nested_unique {a a' r r' : Chars} (h : Nested a) (h' : Nested a')
    (he : a ++ r = a' ++ r') : a = a' := by
  obtain ⟨u, rfl, hu⟩ := nested_shape h
  obtain ⟨u', rfl, hu'⟩ := nested_shape h'
  simp only [List.cons_append, List.cons.injEq, true_and] at he
  rw [nestedTail_unique u.length u u' r r' le_rfl hu hu' he]

/-- Not a line ending. -/
def NotLE (c : Char) : Prop := c ≠ '\n' ∧ c ≠ '\r'

theorem spaceItem_unique {a a' y y' : Chars} (h : SpaceItem a) (h' : SpaceItem a')
    (he : a ++ y = a' ++ y') : a = a' := by
  cases h with
  | @ws c hc =>
    cases h' with
    | ws _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      rw [he.1]
    | line _ _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [IsWs] at hc
    | nested ha =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [IsWs] at hc
  | @line body e hb he1 =>
    cases h' with
    | @ws c hc =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [IsWs] at hc
    | @line body' e' hb' he1' =>
      simp only [List.cons_append, List.append_assoc,
        List.cons.injEq, true_and] at he
      have hnl : ∀ {e : Char}, (e = '\n' ∨ e = '\r') → ¬ NotLE e := by
        rintro e (rfl | rfl) <;> simp [NotLE]
      obtain rfl := run_unique NotLE (fun c hc => hb c hc) (fun c hc => hb' c hc)
        (fun c hc => by simp at hc; subst hc; exact hnl he1)
        (fun c hc => by simp at hc; subst hc; exact hnl he1') he
      have := List.append_cancel_left he
      simp only [List.cons.injEq] at this
      rw [this.1]
    | nested ha =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp at he
  | nested ha =>
    cases h' with
    | @ws c hc =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [IsWs] at hc
    | line _ _ =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp at he
    | nested ha' => exact nested_unique ha ha' he

/-! ## Strings and `|symbols|` -/

theorem escapes_fun {e c c' : Char} (h : (e, c) ∈ escapes) (h' : (e, c') ∈ escapes) :
    c = c' := by
  simp only [escapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h h'
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at h' <;> exact h'.symm

/-- Escape characters are not whitespace and not `x`. -/
def NotWsX (e : Char) : Prop := e ≠ 'x' ∧ ¬ IsIntraline e ∧ e ≠ '\n' ∧ e ≠ '\r'

theorem escapes_key {e c : Char} (h : (e, c) ∈ escapes) : NotWsX e := by
  simp only [escapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [NotWsX, IsIntraline]

theorem not_escapes_x {c : Char} : ('x', c) ∉ escapes := fun h => (escapes_key h).1 rfl

/-- The text after `\` in a line continuation starts with whitespace. -/
theorem cont_head {w₁ le z : Chars} (hw : ∀ c ∈ w₁, IsIntraline c) (hle : LineEnding le) :
    ∃ d tl, w₁ ++ (le ++ z) = d :: tl ∧ (IsIntraline d ∨ d = '\n' ∨ d = '\r') := by
  cases w₁ with
  | cons d w => exact ⟨d, _, rfl, Or.inl (hw d (by simp))⟩
  | nil =>
    rcases hle with rfl | rfl | rfl
    · exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, _, rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨_, _, rfl, Or.inr (Or.inr rfl)⟩

theorem not_intraline_le {d : Char} (h : d = '\n' ∨ d = '\r') : ¬ IsIntraline d := by
  rcases h with rfl | rfl <;> simp [IsIntraline]

theorem le_unique {le le' w₂ w₂' z z' : Chars} (hle : LineEnding le) (hle' : LineEnding le')
    (hw₂ : ∀ c ∈ w₂, IsIntraline c) (hw₂' : ∀ c ∈ w₂', IsIntraline c)
    (hz : le = ['\r'] → z.head? ≠ some '\n') (hz' : le' = ['\r'] → z'.head? ≠ some '\n')
    (h : le ++ (w₂ ++ z) = le' ++ (w₂' ++ z')) : le = le' := by
  have key : ∀ {w z : Chars}, (∀ c ∈ w, IsIntraline c) → z.head? ≠ some '\n' →
      ∀ {y : Chars}, w ++ z ≠ '\n' :: y := by
    intro w z hw hz y he
    cases w with
    | nil => simp only [List.nil_append] at he; subst he; exact hz rfl
    | cons d w =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact not_intraline_le (Or.inl he.1) (hw d (by simp))
  rcases hle with rfl | rfl | rfl <;> rcases hle' with rfl | rfl | rfl <;>
    simp only [List.cons_append, List.nil_append, List.cons.injEq, reduceCtorEq,
      false_and, true_and, Char.reduceEq] at h ⊢
  · exact key hw₂' (hz' rfl) h.symm
  · exact key hw₂ (hz rfl) h

theorem strBody_unique {b : Chars} {l : List Char} (h : StrBody b l) :
    ∀ {b' : Chars} {l' : List Char} {r r' : Chars}, StrBody b' l' →
      b ++ '"' :: r = b' ++ '"' :: r' → b = b' ∧ l = l' := by
  induction h with
  | nil =>
    intro b' l' r r' h' he
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | char h1 _ _ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h1
    | esc _ _ => simp at he
    | hex _ _ => simp at he
    | cont _ _ _ _ _ _ => simp at he
  | @char c rest cs h1 h2 _ ih =>
    intro b' l' r r' h' he
    cases h' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h1
    | char _ _ h' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih h' he
      exact ⟨rfl, rfl⟩
    | esc _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h2
    | hex _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h2
    | cont _ _ _ _ _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h2
  | @esc e c rest cs hec _ ih =>
    intro b' l' r r' h' he
    cases h' with
    | nil => simp at he
    | char _ h2 _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | esc hec' h' =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨rfl, he⟩ := he
      obtain rfl := escapes_fun hec hec'
      obtain ⟨rfl, rfl⟩ := ih h' he
      exact ⟨rfl, rfl⟩
    | hex _ _ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd hec not_escapes_x
    | cont hw₁ hle _ _ _ _ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain ⟨d, tl, hd, hdw⟩ := cont_head (z := _) hw₁ hle
      rw [hd] at he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := escapes_key hec
      rcases hdw with h | h | h
      · exact (this.2.1 h).elim
      · exact (this.2.2.1 h).elim
      · exact (this.2.2.2 h).elim
  | @hex ds rest c cs hds _ ih =>
    intro b' l' r r' h' he
    cases h' with
    | nil => simp at he
    | char _ h2 _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | esc hec' _ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd hec' not_escapes_x
    | @hex ds' rest' c' cs' hds' h' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain rfl := run_unique IsHexDigit hds.2.1 hds'.2.1
        (fun c hc => by simp at hc; subst hc; decide)
        (fun c hc => by simp at hc; subst hc; decide) he
      have he' := List.append_cancel_left he
      simp only [List.cons.injEq, true_and] at he'
      obtain ⟨rfl, rfl⟩ := ih h' he'
      rw [hds.2.2.2, hds'.2.2.2]
      exact ⟨rfl, rfl⟩
    | cont hw₁ hle _ _ _ _ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain ⟨d, tl, hd, hdw⟩ := cont_head (z := _) hw₁ hle
      rw [hd] at he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rcases hdw with h | h | h
      · simp [IsIntraline] at h
      · simp at h
      · simp at h
  | @cont w₁ le w₂ rest cs hw₁ hle hw₂ hcr hri _ ih =>
    intro b' l' r r' h' he
    obtain ⟨d, tl, hd, hdw⟩ := cont_head (z := w₂ ++ (rest ++ '"' :: r)) hw₁ hle
    cases h' with
    | nil => simp at he
    | char _ h2 _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | esc hec' _ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      rw [hd] at he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := escapes_key hec'
      rcases hdw with h | h | h
      · exact (this.2.1 h).elim
      · exact (this.2.2.1 h).elim
      · exact (this.2.2.2 h).elim
    | hex _ _ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      rw [hd] at he
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rcases hdw with h | h | h
      · simp [IsIntraline] at h
      · simp at h
      · simp at h
    | @cont w₁' le' w₂' rest' cs' hw₁' hle' hw₂' hcr' hri' h' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      have hleh : ∀ {le z : Chars}, LineEnding le → ∀ c, (le ++ z).head? = some c →
          ¬ IsIntraline c := by
        intro le z hle c hc
        rcases hle with rfl | rfl | rfl <;> simp at hc <;> subst hc <;> simp [IsIntraline]
      obtain rfl := run_unique IsIntraline hw₁ hw₁' (hleh hle) (hleh hle') he
      have he1 := List.append_cancel_left he
      have hzr : ∀ {rest r : Chars}, (∀ c, rest.head? = some c → ¬ IsIntraline c) →
          ∀ c, (rest ++ '"' :: r).head? = some c → ¬ IsIntraline c := by
        intro rest r hri c hc
        cases rest with
        | nil => simp at hc; subst hc; simp [IsIntraline]
        | cons d rest => simp at hc; subst hc; exact hri d rfl
      have hzn : ∀ {le rest r : Chars}, (le = ['\r'] → rest.head? ≠ some '\n') →
          le = ['\r'] → (rest ++ '"' :: r).head? ≠ some '\n' := by
        intro le rest r hcr hle
        cases rest with
        | nil => simp
        | cons d rest => simpa using hcr hle
      obtain rfl := le_unique hle hle' hw₂ hw₂' (hzn hcr) (hzn hcr') he1
      have he2 := List.append_cancel_left he1
      obtain rfl := run_unique IsIntraline hw₂ hw₂' (hzr hri) (hzr hri') he2
      have he3 := List.append_cancel_left he2
      obtain ⟨rfl, rfl⟩ := ih h' he3
      exact ⟨rfl, rfl⟩

theorem symBody_unique {b : Chars} {l : List Char} (h : SymBody b l) :
    ∀ {b' : Chars} {l' : List Char} {r r' : Chars}, SymBody b' l' →
      b ++ '|' :: r = b' ++ '|' :: r' → b = b' ∧ l = l' := by
  induction h with
  | nil =>
    intro b' l' r r' h' he
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | char h1 _ _ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h1
    | esc _ _ => simp at he
    | hex _ _ => simp at he
  | @char c rest cs h1 h2 _ ih =>
    intro b' l' r r' h' he
    cases h' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h1
    | char _ _ h' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih h' he
      exact ⟨rfl, rfl⟩
    | esc _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h2
    | hex _ _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 h2
  | @esc e c rest cs hec _ ih =>
    intro b' l' r r' h' he
    cases h' with
    | nil => simp at he
    | char _ h2 _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | esc hec' h' =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨rfl, he⟩ := he
      obtain rfl := escapes_fun hec hec'
      obtain ⟨rfl, rfl⟩ := ih h' he
      exact ⟨rfl, rfl⟩
    | hex _ _ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd hec not_escapes_x
  | @hex ds rest c cs hds _ ih =>
    intro b' l' r r' h' he
    cases h' with
    | nil => simp at he
    | char _ h2 _ =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm h2
    | esc hec' _ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd hec' not_escapes_x
    | @hex ds' rest' c' cs' hds' h' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at he
      obtain rfl := run_unique IsHexDigit hds.2.1 hds'.2.1
        (fun c hc => by simp at hc; subst hc; decide)
        (fun c hc => by simp at hc; subst hc; decide) he
      have he' := List.append_cancel_left he
      simp only [List.cons.injEq, true_and] at he'
      obtain ⟨rfl, rfl⟩ := ih h' he'
      rw [hds.2.2.2, hds'.2.2.2]
      exact ⟨rfl, rfl⟩

theorem strLit_unique {c c' rest rest' : Chars} {s s' : String} (h : StrLit c s)
    (h' : StrLit c' s') (he : c ++ rest = c' ++ rest') : c = c' ∧ s = s' := by
  obtain ⟨b, rfl, hb⟩ := h
  obtain ⟨b', rfl, hb'⟩ := h'
  simp only [List.cons_append, List.append_assoc, List.cons.injEq,
    true_and] at he
  obtain ⟨rfl, hl⟩ := strBody_unique hb hb' he
  exact ⟨rfl, String.toList_injective hl⟩

theorem symLit_unique {c c' rest rest' : Chars} {s s' : String} (h : SymLit c s)
    (h' : SymLit c' s') (he : c ++ rest = c' ++ rest') : c = c' ∧ s = s' := by
  obtain ⟨b, rfl, hb⟩ := h
  obtain ⟨b', rfl, hb'⟩ := h'
  simp only [List.cons_append, List.append_assoc, List.cons.injEq,
    true_and] at he
  obtain ⟨rfl, hl⟩ := symBody_unique hb hb' he
  exact ⟨rfl, String.toList_injective hl⟩

/-! ## Bare tokens -/

theorem bare_unique {c c' rest rest' : Chars} (h : Bare c) (h' : Bare c') (hr : DelimNext rest)
    (hr' : DelimNext rest') (he : c ++ rest = c' ++ rest') : c = c' := by
  have hx : ∀ {r : Chars}, DelimNext r → ∀ d, r.head? = some d → ¬ ¬ IsDelim d :=
    fun hr d hd hn => hn (hr d hd)
  have plainChar : ∀ {c rest d r₀ rest' : Chars}, c.take 2 ≠ ['#', '\\'] →
      (c.head? = some '#' → 2 ≤ c.length) → c ≠ [] →
      c ++ rest ≠ '#' :: '\\' :: (d ++ r₀ ++ rest') := by
    intro c rest d r₀ rest' ht hh hne he
    obtain ⟨x, c₁, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    cases c₁ with
    | nil => simp at hh
    | cons y c₂ =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp at ht
  rcases h with ⟨hne, hall, -, -, hh, ht⟩ | ⟨d, r₀, rfl, hall⟩ <;>
    rcases h' with ⟨hne', hall', -, -, hh', ht'⟩ | ⟨d', r₀', rfl, hall'⟩
  · exact run_unique (fun c => ¬ IsDelim c) hall hall' (hx hr) (hx hr') he
  · exact absurd (by simpa using he) (plainChar (d := [d']) ht hh hne)
  · exact absurd (by simpa using he.symm) (plainChar (d := [d]) ht' hh' hne')
  · simp only [List.cons_append, List.cons.injEq, true_and] at he
    obtain ⟨rfl, he⟩ := he
    rw [run_unique (fun c => ¬ IsDelim c) hall hall' (hx hr) (hx hr') he]

/-! ## Single tokens -/

/-- The start of an item of intertoken space. -/
def SpaceStart : Chars → Prop
  | [] => False
  | c :: r => IsWs c ∨ c = ';' ∨ (c = '#' ∧ r.head? = some '|')

open Classical in
/-- A classification of texts by their first characters, determining the kind
of token (or space) they start with. -/
noncomputable def headClass : Chars → Nat
  | [] => 8
  | c :: r =>
    if c = '(' then 0 else if c = ')' then 1 else if c = '\'' ∨ c = '`' ∨ c = ',' then 2
    else if c = '"' then 3 else if c = '|' then 4
    else if c = '#' ∧ r.head? = some ';' then 5
    else if c = '.' ∧ DelimNext r then 6
    else if SpaceStart (c :: r) then 8 else 7

/-- The class of a token. -/
def tokCls (c : Chars) : Tok → Nat
  | .lp => 0
  | .rp => 1
  | .quote _ => 2
  | .atom (.str _) => 3
  | .atom (.sym _) => if c.head? = some '|' then 4 else 7
  | .datumComment => 5
  | .dot => 6
  | .atom (.id _) => 9

theorem headClass_space {x : Chars} (h : SpaceStart x) : headClass x = 8 := by
  cases x with
  | nil => exact h.elim
  | cons c r =>
    rcases h with hw | rfl | ⟨rfl, hr⟩
    · simp only [IsWs] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp [headClass, SpaceStart, IsWs]
    · simp [headClass, SpaceStart]
    · simp [headClass, SpaceStart, hr]

theorem bare_cls {c : Chars} (rest : Chars) (h : Bare c) :
    headClass (c ++ rest) = 7 ∧ ∃ x c₁, c = x :: c₁ ∧ x ≠ '|' := by
  rcases h with ⟨hne, hall, hdot, hq, hhash, -⟩ | ⟨d, r₀, rfl, -⟩
  · obtain ⟨x, c₁, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hx := hall x (by simp)
    simp only [IsDelim, IsWs, not_or] at hx
    obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := hx
    obtain ⟨q1, q2, q3⟩ := hq x rfl
    refine ⟨?_, x, c₁, rfl, h5⟩
    have hhash' : ¬ (x = '#' ∧ (c₁ ++ rest).head? = some ';') := by
      rintro ⟨rfl, hh⟩
      cases c₁ with
      | nil => simp at hhash
      | cons y c₂ =>
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
        subst hh
        exact hall ';' (by simp) (by simp [IsDelim])
    have hdot' : ¬ (x = '.' ∧ DelimNext (c₁ ++ rest)) := by
      rintro ⟨rfl, hh⟩
      cases c₁ with
      | nil => exact hdot rfl
      | cons y c₂ => exact hall y (by simp) (hh y rfl)
    have hsp : ¬ SpaceStart (x :: (c₁ ++ rest)) := by
      rintro (h | h | ⟨rfl, hh⟩)
      · simp only [IsWs] at h
        rcases h with h | h | h | h
        · exact h1 h
        · exact h2 h
        · exact h3 h
        · exact h4 h
      · exact h9 h
      · cases c₁ with
        | nil => simp at hhash
        | cons y c₂ =>
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
          subst hh
          exact hall '|' (by simp) (by simp [IsDelim])
    have hq' : ¬ (x = '\'' ∨ x = '`' ∨ x = ',') := by
      rintro (h | h | h)
      · exact q1 h
      · exact q2 h
      · exact q3 h
    simp only [List.cons_append, headClass]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h6), ite_eq_right_of_eq_false _ _ (eq_false h7),
      ite_eq_right_of_eq_false _ _ (eq_false hq'), ite_eq_right_of_eq_false _ _ (eq_false h8),
      ite_eq_right_of_eq_false _ _ (eq_false h5), ite_eq_right_of_eq_false _ _ (eq_false hhash'),
      ite_eq_right_of_eq_false _ _ (eq_false hdot'), ite_eq_right_of_eq_false _ _ (eq_false hsp)]
  · refine ⟨?_, '#', _, rfl, by decide⟩
    simp [headClass, SpaceStart, IsWs]

theorem tok_cls {c rest : Chars} {t : Tok} (h : Tok1 c t rest) :
    headClass (c ++ rest) = tokCls c t := by
  rcases t with _ | _ | _ | n | _ | (s | bs | n)
  · simp only [Tok1] at h; subst h; simp [headClass, tokCls]
  · simp only [Tok1] at h; subst h; simp [headClass, tokCls]
  · obtain ⟨rfl, hr⟩ := h; simp [headClass, tokCls, hr]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩ <;> simp [headClass, tokCls]
  · simp only [Tok1] at h; subst h; simp [headClass, tokCls]
  · simp only [Tok1] at h
    rcases h with ⟨b, rfl, -⟩ | ⟨hb, -, -, -⟩
    · simp [headClass, tokCls]
    · obtain ⟨h7, x, c₁, rfl, hx⟩ := bare_cls rest hb
      simp only [List.cons_append] at h7
      simp [tokCls, h7, hx]
  · obtain ⟨s, ⟨b, rfl, -⟩, -⟩ := h; simp [headClass, tokCls]
  · exact h.elim

theorem tokCls_le {c rest : Chars} {t : Tok} (h : Tok1 c t rest) : tokCls c t ≤ 7 := by
  rcases t with _ | _ | _ | n | _ | (s | bs | n) <;> simp only [tokCls] <;> try omega
  · split_ifs <;> omega
  · exact h.elim

theorem tok_not_space {c rest : Chars} {t : Tok} (h : Tok1 c t rest) : ¬ SpaceStart (c ++ rest) :=
  fun hs => by have := tok_cls h; rw [headClass_space hs] at this; have := tokCls_le h; omega

theorem tok_ne_nil {c rest : Chars} {t : Tok} (h : Tok1 c t rest) : c ++ rest ≠ [] :=
  fun he => by
    have h1 := tok_cls h
    rw [he] at h1
    have h2 := tokCls_le h
    simp only [headClass] at h1
    omega

theorem tok_unique {c c' rest rest' : Chars} {t t' : Tok} (h : Tok1 c t rest)
    (h' : Tok1 c' t' rest') (he : c ++ rest = c' ++ rest') : c = c' ∧ t = t' := by
  have hc := tok_cls h
  have hc' := tok_cls h'
  rw [he, hc'] at hc
  rcases t with _ | _ | _ | n | _ | (s | bs | n) <;>
    rcases t' with _ | _ | _ | n' | _ | (s' | bs' | n') <;>
    try first
    | (exfalso; simp only [Tok1] at h; done)
    | (exfalso; simp only [Tok1] at h'; done)
    | (exfalso; simp only [tokCls] at hc; (try split_ifs at hc) <;> omega)
  · simp only [Tok1] at h h'; subst h; subst h'; exact ⟨rfl, rfl⟩
  · simp only [Tok1] at h h'; subst h; subst h'; exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, -⟩ := h; obtain ⟨rfl, -⟩ := h'; exact ⟨rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, hr⟩ | ⟨rfl, rfl⟩ <;>
      rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, hr'⟩ | ⟨rfl, rfl⟩ <;>
      (simp_all; try (subst he; simp at *))
  · simp only [Tok1] at h h'; subst h; subst h'; exact ⟨rfl, rfl⟩
  · simp only [Tok1] at h h'
    have symHead : ∀ {c : Chars} {s : String}, SymLit c s → ∃ c₀, c = '|' :: c₀ := by
      rintro c s ⟨b, rfl, -⟩; exact ⟨_, rfl⟩
    rcases h with hl | ⟨hb, rfl, hr, -⟩ <;> rcases h' with hl' | ⟨hb', rfl, hr', -⟩
    · obtain ⟨rfl, rfl⟩ := symLit_unique hl hl' he; exact ⟨rfl, rfl⟩
    · obtain ⟨c₀, rfl⟩ := symHead hl
      obtain ⟨-, x, c₁, rfl, hx⟩ := bare_cls rest' hb'
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1.symm hx
    · obtain ⟨c₀, rfl⟩ := symHead hl'
      obtain ⟨-, x, c₁, rfl, hx⟩ := bare_cls rest hb
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 hx
    · obtain rfl := bare_unique hb hb' hr hr' he; exact ⟨rfl, rfl⟩
  · obtain ⟨s, hs, rfl⟩ := h
    obtain ⟨s', hs', rfl⟩ := h'
    obtain ⟨rfl, rfl⟩ := strLit_unique hs hs' he
    exact ⟨rfl, rfl⟩

/-! ## Intertoken space and token sequences -/

/-- Where a run of intertoken space may stop: before a non-space character, at
the end, or before an unterminated final line comment. -/
def LStop (x : Chars) : Prop := ¬ SpaceStart x ∨ ∃ body, x = ';' :: body ∧ NoLineEnd body

theorem spaceItem_start {a y : Chars} (h : SpaceItem a) : SpaceStart (a ++ y) := by
  cases h with
  | ws hc => exact Or.inl hc
  | line _ _ => exact Or.inr (Or.inl rfl)
  | nested ha =>
    obtain ⟨u, rfl, -⟩ := nested_shape ha
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem spaceItem_not_lstop {a y : Chars} (h : SpaceItem a) : ¬ LStop (a ++ y) := by
  rintro (hs | ⟨body, hb, hnl⟩)
  · exact hs (spaceItem_start h)
  · cases h with
    | ws hc =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      simp [IsWs] at hc
    | @line body' e _ he =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at hb
      have := hnl e (by rw [← hb]; simp)
      rcases he with rfl | rfl
      · exact this.1 rfl
      · exact this.2 rfl
    | nested ha =>
      obtain ⟨u, rfl, -⟩ := nested_shape ha
      simp at hb

theorem space_unique {s : Chars} (hs : Space s) :
    ∀ {s' x x' : Chars}, Space s' → s ++ x = s' ++ x' → LStop x → LStop x' → s = s' := by
  induction hs with
  | nil =>
    intro s' x x' hs' he hx hx'
    cases hs' with
    | nil => rfl
    | cons ha' _ =>
      simp only [List.nil_append, List.append_assoc] at he
      subst he
      exact absurd hx (spaceItem_not_lstop ha')
  | @cons a b ha _ ih =>
    intro s' x x' hs' he hx hx'
    cases hs' with
    | nil =>
      simp only [List.nil_append, List.append_assoc] at he
      subst he
      exact absurd hx' (spaceItem_not_lstop ha)
    | cons ha' hb' =>
      simp only [List.append_assoc] at he
      obtain rfl := spaceItem_unique ha ha' he
      rw [ih hb' (List.append_cancel_left he) hx hx']

theorem lstop_tok {c rest : Chars} {t : Tok} (h : Tok1 c t rest) : LStop (c ++ rest) :=
  Or.inl (tok_not_space h)

theorem lex_functional {xs : Chars} {ts : List Tok} (h : Lex xs ts) :
    ∀ {xs' : Chars} {ts' : List Tok}, Lex xs' ts' → xs = xs' → ts = ts' := by
  have lnil : LStop [] := Or.inl id
  induction h with
  | @done s hs =>
    intro xs' ts' h' hx
    cases h' with
    | done _ => rfl
    | @doneEof s' body hs' hb' =>
      have he : s ++ [] = s' ++ ';' :: body := by simpa using hx
      obtain rfl := space_unique hs hs' he lnil (Or.inr ⟨body, rfl, hb'⟩)
      simp at he
    | @step s' c rest t ts hs' ht _ =>
      have he : s ++ [] = s' ++ (c ++ rest) := by simpa using hx
      obtain rfl := space_unique hs hs' he lnil (lstop_tok ht)
      exact absurd (List.append_cancel_left he).symm (tok_ne_nil ht)
  | @doneEof s body hs hb =>
    intro xs' ts' h' hx
    cases h' with
    | done hs' =>
      have he : s ++ ';' :: body = xs' ++ [] := by simpa using hx
      obtain rfl := space_unique hs hs' he (Or.inr ⟨body, rfl, hb⟩) lnil
      simp at he
    | doneEof _ _ => rfl
    | @step s' c rest t ts hs' ht _ =>
      have he : s ++ ';' :: body = s' ++ (c ++ rest) := by simpa using hx
      obtain rfl := space_unique hs hs' he (Or.inr ⟨body, rfl, hb⟩) (lstop_tok ht)
      have he' := List.append_cancel_left he
      exact (tok_not_space ht (he' ▸ Or.inr (Or.inl rfl))).elim
  | @step s c rest t ts hs ht _ ih =>
    intro xs' ts' h' hx
    cases h' with
    | done hs' =>
      have he : s ++ (c ++ rest) = xs' ++ [] := by simpa using hx
      obtain rfl := space_unique hs hs' he (lstop_tok ht) lnil
      exact absurd (List.append_cancel_left he) (tok_ne_nil ht)
    | @doneEof s' body hs' hb' =>
      have he : s ++ (c ++ rest) = s' ++ ';' :: body := by simpa using hx
      obtain rfl := space_unique hs hs' he (lstop_tok ht) (Or.inr ⟨body, rfl, hb'⟩)
      have he' := List.append_cancel_left he
      exact (tok_not_space ht (he' ▸ Or.inr (Or.inl rfl))).elim
    | @step s' c' rest' t' ts' hs' ht' hl' =>
      have he : s ++ (c ++ rest) = s' ++ (c' ++ rest') := by simpa using hx
      obtain rfl := space_unique hs hs' he (lstop_tok ht) (lstop_tok ht')
      have he' := List.append_cancel_left he
      obtain ⟨rfl, rfl⟩ := tok_unique ht ht' he'
      rw [ih hl' (List.append_cancel_left he')]

/-! ## Helpers for example spellings -/

theorem delimNext_nil : DelimNext [] := by
  intro d hd
  simp at hd

theorem delimNext_cons {c : Char} {r : Chars} (h : IsDelim c) : DelimNext (c :: r) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  exact hd ▸ h

theorem space_one : Space [' '] := by
  simpa using Space.cons (SpaceItem.ws (c := ' ') (by decide)) Space.nil

end Silmaril.Formats.SExpEncoding.Scheme
