module

public import Silmaril.Encoding.RadixFacts

/-!
# Base32 alphabets and blocks

The building blocks of the RFC 4648 base32 carrier (`Silmaril.Encoding.Base32`):

* `Alphabet` — radix-32 alphabets (`Radix.Alphabet 5`): `std` (RFC 4648 §6,
  `A–Z 2–7`) and `hex` (§7, "base32hex", `0–9 A–V`);
* full groups are `Radix.Alphabet.encGroup` on 5 bytes (8 digits); the final
  block `encLast` spells 1–4 remaining bytes as 2, 4, 5 or 7 digits and, when
  padded, completes 8 characters with `'='` (RFC 4648 §6 cases (2)–(5));
* the strict `decLast`, exact for `encLast` (`decLast_eq_some_iff`): it
  rejects misplaced or missing padding, digit counts 1, 3 and 6, and non-zero
  pad bits (RFC 4648 §3.5).
-/

@[expose] public section

namespace Silmaril

namespace Base32

open Radix Radix.Alphabet

/-- A base32 alphabet: 32 digit characters with an exact partial inverse, not
containing `'='`. -/
abbrev Alphabet := Radix.Alphabet 5

namespace Alphabet

/-- The base32 alphabet (RFC 4648 §6, Table 3): `A–Z 2–7`. -/
def std : Alphabet :=
  ofTable (fun i => if i.val < 26 then Char.ofNat (65 + i.val) else Char.ofNat (24 + i.val))
    (by decide) (by decide)

/-- The "extended hex" base32 alphabet (RFC 4648 §7, Table 4): `0–9 A–V`;
encoded data keeps the sort order of the bytes. -/
def hex : Alphabet :=
  ofTable (fun i => if i.val < 10 then Char.ofNat (48 + i.val) else Char.ofNat (55 + i.val))
    (by decide) (by decide)

example : std.digit 0 = 'A' ∧ std.digit 25 = 'Z' ∧ std.digit 26 = '2' ∧
    std.digit 31 = '7' ∧ std.value? '0' = none ∧ std.value? '1' = none ∧
    std.value? 'a' = none := by decide

example : hex.digit 0 = '0' ∧ hex.digit 9 = '9' ∧ hex.digit 10 = 'A' ∧
    hex.digit 31 = 'V' ∧ hex.value? 'W' = none ∧ hex.value? 'a' = none := by decide

end Alphabet

variable (A : Alphabet)

/-! ## Final blocks -/

/-- The `'='` padding completing `d` digits to a multiple of 8 characters,
when `padded`. -/
def padding (padded : Bool) (d : Nat) : List Char :=
  if padded then List.replicate ((8 - d % 8) % 8) '=' else []

/-- The final block: the digits of the remaining bytes, then `'='` padding. -/
def encLast (padded : Bool) (bs : List UInt8) : List Char :=
  A.encGroup bs ++ padding padded (A.encGroup bs).length

/-- Strict decoding of a final block: the digits are the characters before
the first `'='`, which must be followed by exactly the expected padding. -/
def decLast (padded : Bool) (cs : List Char) : Option (List UInt8) :=
  if cs = cs.takeWhile (· != '=') ++ padding padded (cs.takeWhile (· != '=')).length then
    A.decGroup (cs.takeWhile (· != '='))
  else none

theorem digitCount_five (m : Nat) : digitCount 5 m = (8 * m + 4) / 5 := rfl

theorem length_encGroup_eq_eight {bs : List UInt8} (h : (A.encGroup bs).length = 8) :
    bs.length = 5 := by
  rw [length_encGroup, digitCount_five] at h
  omega

theorem length_le_of_length_encGroup {bs : List UInt8} (h : (A.encGroup bs).length ≤ 8) :
    bs.length ≤ 5 := by
  rw [length_encGroup, digitCount_five] at h
  omega

/-- A final block of `n` bytes has `⌈8n/5⌉` digits, padded to `8⌈n/5⌉`
characters. -/
theorem length_encLast (padded : Bool) (bs : List UInt8) :
    (encLast A padded bs).length =
      if padded then 8 * ((bs.length + 4) / 5) else (8 * bs.length + 4) / 5 := by
  simp only [encLast, padding, List.length_append, length_encGroup, digitCount_five]
  cases padded <;> simp <;> omega

theorem length_le_of_length_encLast {padded : Bool} {bs : List UInt8}
    (h : (encLast A padded bs).length ≤ 8) : bs.length ≤ 5 := by
  simp only [encLast, List.length_append] at h
  exact length_le_of_length_encGroup A (by omega)

theorem takeWhile_encLast (padded : Bool) (bs : List UInt8) :
    (encLast A padded bs).takeWhile (· != '=') = A.encGroup bs := by
  rw [encLast, List.takeWhile_append_of_pos]
  · cases padded
    · simp [padding]
    · simp only [padding, ↓reduceIte]
      cases (8 - (A.encGroup bs).length % 8) % 8 <;> simp [List.replicate_succ]
  · intro c hc
    have : c ≠ '=' := fun h => A.pad_not_mem_encGroup bs (h ▸ hc)
    simpa using this

theorem decLast_eq_some_iff {padded : Bool} {cs : List Char} {bs : List UInt8} :
    decLast A padded cs = some bs ↔ encLast A padded bs = cs := by
  constructor
  · intro h
    unfold decLast at h
    split at h
    case isFalse => cases h
    case isTrue hcs =>
      rw [← (A.decGroup_eq_some_iff (by decide) (by decide)).mp h] at hcs
      rw [encLast, hcs]
  · rintro rfl
    have hc : encLast A padded bs = A.encGroup bs ++ padding padded (A.encGroup bs).length := rfl
    rw [decLast, takeWhile_encLast]
    simp only [hc, ↓reduceIte]
    exact (A.decGroup_eq_some_iff (by decide) (by decide)).mpr rfl

end Base32

end Silmaril
