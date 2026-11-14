module

public import Silmaril.Formats.Tar.Defs

/-! Proofs for `Silmaril.Formats.Tar.Thms`: numeric and text fields. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Tar

open Silmaril.Formats.Tar

theorem octalDigits_length (n k : Nat) : (octalDigits n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [octalDigits, ih]

@[simp] theorem encodeOctal_length (v w : Nat) : (encodeOctal v w).length = w := by
  unfold encodeOctal; split <;> simp [octalDigits_length] <;> omega

theorem octalDigit_toNat {d : Nat} (hd : d < 8) : (octalDigit d).toNat = 0x30 + d :=
  UInt8.toNat_ofNat_of_lt (by have : UInt8.size = 256 := rfl; omega)

theorem isOctalDigit_of_mem_octalDigits {n k : Nat} {b : UInt8} (h : b ∈ octalDigits n k) :
    isOctalDigit b = true := by
  induction k generalizing n with
  | zero => simp [octalDigits] at h
  | succ k ih =>
    simp only [octalDigits, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact ih h
    · have := octalDigit_toNat (Nat.mod_lt n (by decide : 8 > 0))
      simp [isOctalDigit, this]; omega

theorem octalValue_octalDigits (n k : Nat) : octalValue (octalDigits n k) = n % 8 ^ k := by
  induction k generalizing n with
  | zero => simp [octalDigits, octalValue, Nat.mod_one]
  | succ k ih =>
    have hd := octalDigit_toNat (Nat.mod_lt n (by decide : 8 > 0))
    have ih' := ih (n / 8)
    simp only [octalValue] at ih' ⊢
    rw [octalDigits, List.foldl_append, ih']
    simp only [List.foldl, hd, Nat.pow_succ', Nat.mod_mul]
    omega

theorem not_isOctalDigit_of_isPadByte {b : UInt8} (h : isPadByte b = true) :
    isOctalDigit b = false := by
  simp [isPadByte, isOctalDigit] at h ⊢; omega

/-- Octal digits followed by NUL/`<space>` filler read back as their value. -/
theorem decodeOctal_octalDigits_append {v k : Nat} (hk : 0 < k) (hv : v < 8 ^ k)
    {pad : List UInt8} (hpad : pad.all isPadByte = true) :
    decodeOctal (octalDigits v k ++ pad) = some v := by
  have hdig : ∀ a ∈ octalDigits v k, isOctalDigit a = true :=
    fun _ h => isOctalDigit_of_mem_octalDigits h
  obtain ⟨d, ds, hcons⟩ : ∃ d ds, octalDigits v k = d :: ds := by
    cases h : octalDigits v k with
    | nil => have := octalDigits_length v k; rw [h] at this; simp at this; omega
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hd : isOctalDigit d = true := hdig d (by simp [hcons])
  simp only [isOctalDigit, decide_eq_true_eq] at hd
  have htw : pad.takeWhile isOctalDigit = [] := by
    cases pad with
    | nil => rfl
    | cons b t =>
      simp only [List.all_cons, Bool.and_eq_true] at hpad
      simp [not_isOctalDigit_of_isPadByte hpad.1]
  have hdw : pad.dropWhile isOctalDigit = pad := by
    cases pad with
    | nil => rfl
    | cons b t =>
      simp only [List.all_cons, Bool.and_eq_true] at hpad
      simp [not_isOctalDigit_of_isPadByte hpad.1]
  have hsp : (octalDigits v k ++ pad).dropWhile (· == 0x20) = octalDigits v k ++ pad := by
    rw [hcons, List.cons_append, List.dropWhile_cons_of_neg]
    intro h; simp at h; subst h; simp at hd
  have h80 : d ≠ 0x80 := by intro h; subst h; simp at hd
  unfold decodeOctal
  rw [hcons, List.cons_append]
  simp only [h80, ite_false, show ¬ 0x80 ≤ d.toNat by omega]
  rw [← List.cons_append, ← hcons, hsp, List.takeWhile_append_of_pos hdig,
    List.dropWhile_append_of_pos hdig, htw, hdw, List.append_nil, hpad, hcons]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, ite_true]
  rw [← hcons, octalValue_octalDigits, Nat.mod_eq_of_lt hv]

theorem decodeOctal_encodeOctal {v w : Nat} (hw : 2 ≤ w) (hv : v < 8 ^ (w - 1)) :
    decodeOctal (encodeOctal v w) = some v := by
  rw [encodeOctal, ite_eq_right (by omega)]
  exact decodeOctal_octalDigits_append (by omega) hv (by decide)

theorem decodeOctal_checksumField {c : Nat} (hc : c < 8 ^ 6) :
    decodeOctal (checksumField c) = some c := by
  rw [checksumField, encodeOctal, ite_eq_right (by decide), List.append_assoc]
  exact decodeOctal_octalDigits_append (by decide) hc (by decide)

@[simp] theorem checksumField_length (c : Nat) : (checksumField c).length = 8 := by
  simp [checksumField]

@[simp] theorem deviceField_length (t : TypeFlag) (v : Nat) : (deviceField t v).length = 8 := by
  unfold deviceField; split <;> simp

theorem decodeOctalOrZero_deviceField {t : TypeFlag} {v : Nat} (hv : v < 8 ^ 7)
    (h0 : t.isDevice = false → v = 0) :
    decodeOctalOrZero (deviceField t v) = some v := by
  unfold deviceField decodeOctalOrZero
  by_cases ht : t.isDevice = true
  · have hd := decodeOctal_encodeOctal (w := 8) (by decide) hv
    have hne : (encodeOctal v 8).all isPadByte = false := by
      rw [encodeOctal, ite_eq_right (by decide)]
      obtain ⟨d, ds, hcons⟩ : ∃ d ds, octalDigits v 7 = d :: ds := by
        cases h : octalDigits v 7 with
        | nil => have := octalDigits_length v 7; rw [h] at this; simp at this
        | cons d ds => exact ⟨d, ds, rfl⟩
      have hd : isOctalDigit d = true := isOctalDigit_of_mem_octalDigits (n := v) (k := 7) (by simp [hcons])
      simp only [isOctalDigit, decide_eq_true_eq] at hd
      simp [hcons, isPadByte]; omega
    simp [ht, hne, hd]
  · simp only [Bool.not_eq_true] at ht
    simp [ht, h0 ht, isPadByte]

/-! ## Text fields -/

@[simp] theorem padTo_length (xs : List UInt8) (n : Nat) : (padTo xs n).length = n := by
  simp [padTo]; omega

theorem fieldBytes_padTo {bytes : List UInt8} {n : Nat} (hlen : bytes.length ≤ n)
    (hnul : bytes.all nonNul = true) : fieldBytes (padTo bytes n) = bytes := by
  unfold fieldBytes padTo
  rw [List.take_of_length_le hlen, List.takeWhile_append_of_pos (by simpa using hnul)]
  cases h : n - bytes.length with
  | zero => simp
  | succ m => simp [List.replicate_succ, nonNul]

theorem toByteArray_data_toList (b : ByteArray) : b.data.toList.toByteArray = b :=
  ByteArray.ext (by simp)

theorem readText_utf8 (s : String) : readText (utf8 s) = some s := by
  simp only [readText, utf8, toByteArray_data_toList, String.toUTF8_eq_toByteArray,
    String.fromUTF8?, dite_eq_left s.isValidUTF8]
  rfl

end Silmaril.Proofs.Formats.Tar
