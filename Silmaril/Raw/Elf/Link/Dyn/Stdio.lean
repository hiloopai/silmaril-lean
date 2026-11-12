module

public import Silmaril.Elf.Link.Dyn.Stdio.Defs

/-! # `scanf("%d %d")` reads back what `printf("%d")` writes

PROVED: `scanInt_decStr`: the `%d` conversion of the decimal text of `x` followed by input that
does not start with a digit is `x`, with that input left; `scanDD_text`: on the text
`"a b\n"` of two `int`s, `scanf("%d %d")` converts `a` and `b` and leaves the newline. -/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Stdio

open Silmaril.X86 (Byte)

/-- The digits of `n`, as bytes. -/
def digitsOf (n : Nat) : List Byte := (Nat.toDigits 10 n).map fun c => BitVec.ofNat 8 c.toNat

theorem charDigitBounds (c : Char) (h : c.isDigit = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [ge_iff_le, UInt32.le_iff_toNat_le] at h1 h2
  exact ⟨h1, h2⟩

theorem toNat_byte_of_digit {c : Char} (h : c.isDigit = true) : (BitVec.ofNat 8 c.toNat).toNat = c.toNat := by
  have := charDigitBounds c h
  simp only [BitVec.toNat_ofNat]
  omega

theorem isDigit_digitsOf {n : Nat} : ∀ c ∈ digitsOf n, isDigit c = true := by
  intro c hc
  simp only [digitsOf, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have h := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd
  rw [isDigit, toNat_byte_of_digit h]
  have := charDigitBounds _ h
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem digitsOf_ne_nil {n : Nat} : digitsOf n ≠ [] := by
  simp [digitsOf, Nat.toDigits_ne_nil]

theorem digitsVal_digitsOf {n : Nat} : digitsVal (digitsOf n) = n := by
  have hd : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have : digitsVal (digitsOf n) = Nat.ofDigitChars 10 (Nat.toDigits 10 n) 0 := by
    unfold digitsVal digitsOf
    rw [Nat.ofDigitChars_eq_foldl, List.foldl_map]
    apply List.foldl_ext
    intro v c hc
    rw [toNat_byte_of_digit (hd c hc)]
    rfl
  rw [this, Nat.ofDigitChars_ten_toDigits]

theorem takeWhile_digits {l r : List Byte} (hl : ∀ c ∈ l, isDigit c = true)
    (hr : ∀ c, r.head? = some c → isDigit c = false) : (l ++ r).takeWhile isDigit = l := by
  induction l with
  | nil =>
    cases r with
    | nil => rfl
    | cons c r => simp [hr c rfl]
  | cons c l ih =>
    simp only [List.cons_append, List.takeWhile_cons, hl c (by simp), ↓reduceIte]
    rw [ih (fun c h => hl c (by simp [h]))]

theorem dropWhile_digits {l r : List Byte} (hl : ∀ c ∈ l, isDigit c = true)
    (hr : ∀ c, r.head? = some c → isDigit c = false) : (l ++ r).dropWhile isDigit = r := by
  induction l with
  | nil =>
    cases r with
    | nil => rfl
    | cons c r => simp [hr c rfl]
  | cons c l ih =>
    simp only [List.cons_append, List.dropWhile_cons, hl c (by simp), ↓reduceIte]
    exact ih (fun c h => hl c (by simp [h]))

theorem not_space_of_digit {c : Byte} (h : isDigit c = true) : isSpace c = false := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isSpace, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Nat.not_le]
  omega

theorem decStr_of_nonneg {x : Int} (h : 0 ≤ x) : decStr x = digitsOf x.toNat := by
  simp [decStr, digitsOf, Int.toString_eq_repr, Int.repr_eq_ite, h, Nat.toList_repr]

theorem decStr_of_neg {x : Int} (h : x < 0) : decStr x = 45#8 :: digitsOf (-x).toNat := by
  have : ¬ 0 ≤ x := by omega
  simp [decStr, digitsOf, Int.toString_eq_repr, Int.repr_eq_ite, this, Nat.toList_repr]

/-- **`%d` reads back the decimal text of `x`.** -/
theorem scanInt_decStr (x : Int) {r : List Byte} (hr : ∀ c, r.head? = some c → isDigit c = false) :
    scanInt (decStr x ++ r) = some (x, r) := by
  have hne := @digitsOf_ne_nil
  rcases Int.lt_or_le x 0 with hx | hx
  · rw [decStr_of_neg hx]
    have hds := isDigit_digitsOf (n := (-x).toNat)
    unfold scanInt
    simp only [List.cons_append, List.dropWhile_cons]
    have : isSpace 45#8 = false := by decide
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    simp only [show (45#8 : Byte).toNat = 45 by decide, ↓reduceIte]
    rw [takeWhile_digits hds hr, dropWhile_digits hds hr]
    simp only [hne, ↓reduceIte, digitsVal_digitsOf, Option.some.injEq, Prod.mk.injEq, and_true]
    omega
  · rw [decStr_of_nonneg hx]
    have hds := isDigit_digitsOf (n := x.toNat)
    obtain ⟨c, l, hcl⟩ := List.exists_cons_of_ne_nil (hne (n := x.toNat))
    have hc : isDigit c = true := hds c (by rw [hcl]; simp)
    unfold scanInt
    rw [hcl]
    simp only [List.cons_append, List.dropWhile_cons, not_space_of_digit hc, Bool.false_eq_true,
      ↓reduceIte]
    have h45 : ¬ c.toNat = 45 := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc; omega
    have h43 : ¬ c.toNat = 43 := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc; omega
    simp only [h45, h43, ↓reduceIte]
    rw [← List.cons_append, ← hcl, takeWhile_digits hds hr, dropWhile_digits hds hr]
    simp only [hne, ↓reduceIte, digitsVal_digitsOf, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

/-- A decimal text does not start with white space. -/
theorem head_decStr (x : Int) : ∃ c l, decStr x = c :: l ∧ isSpace c = false := by
  rcases Int.lt_or_le x 0 with hx | hx
  · exact ⟨45#8, _, decStr_of_neg hx, by decide⟩
  · obtain ⟨c, l, hcl⟩ := List.exists_cons_of_ne_nil (digitsOf_ne_nil (n := x.toNat))
    exact ⟨c, l, by rw [decStr_of_nonneg hx, hcl],
      not_space_of_digit (isDigit_digitsOf c (by rw [hcl]; simp))⟩

/-- **`scanf("%d %d")` on the text `"a b\n"`** of two `int`s converts `a` and `b` and leaves
the newline. -/
theorem scanDD_text {a b : Int} (ha : inInt32 a = true) (hb : inInt32 b = true) :
    scanDD (decStr a ++ [32#8] ++ decStr b ++ [10#8]) = .ok a b [10#8] := by
  have hnl : ∀ c, ([10#8] : List Byte).head? = some c → isDigit c = false := by
    intro c h; simp at h; subst h; decide
  have hsp : ∀ c, ([32#8] ++ decStr b ++ [10#8]).head? = some c → isDigit c = false := by
    intro c h; simp at h; subst h; decide
  unfold scanDD
  rw [List.append_assoc, List.append_assoc, scanInt_decStr a (r := [32#8] ++ (decStr b ++ [10#8]))
    (by simpa [List.append_assoc] using hsp)]
  simp only [ha, ↓reduceIte]
  have h2 : scanInt ([32#8] ++ (decStr b ++ [10#8])) = some (b, [10#8]) := by
    obtain ⟨c, l, hcl, hc⟩ := head_decStr b
    unfold scanInt
    simp only [List.singleton_append, List.dropWhile_cons, show isSpace 32#8 = true by decide,
      ↓reduceIte]
    rw [hcl]
    simp only [List.cons_append, List.dropWhile_cons, hc, Bool.false_eq_true, ↓reduceIte]
    rw [← List.cons_append, ← hcl]
    have := scanInt_decStr b hnl
    unfold scanInt at this
    rw [hcl] at this
    simp only [List.cons_append, List.dropWhile_cons, hc, Bool.false_eq_true, ↓reduceIte] at this
    rw [← List.cons_append, ← hcl] at this
    exact this
  rw [h2]
  simp [hb]

end Silmaril.Elf.Link.Dyn.Stdio
