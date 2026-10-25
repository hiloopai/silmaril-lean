module

public import Silmaril.Encoding.Carriers

/-!
# Base64 alphabets and group arithmetic

The building blocks of the RFC 4648 base64 carrier (`Silmaril.Encoding.Base64`):

* `Alphabet` — 64 digit characters with an exact partial inverse `value?`,
  excluding the pad character `'='`; `std` (RFC 4648 §4) and `url` (§5);
* the per-group encoders (`enc3`, `enc2`, `enc1`: a 3-byte group to 4 digits,
  a 2- or 1-byte tail to 3 or 2 digits) and the strict per-group decoders
  (`dec4`, `dec3`, `dec2`), which reject non-zero pad bits (RFC 4648 §3.5);
* exactness of each decoder for its encoder (`dec4_eq_some_iff`, …).

Group arithmetic is plain `Nat` arithmetic: a group value is
`v = b₀ * 65536 + b₁ * 256 + b₂`, its digits are `v / 262144 % 64`,
`v / 4096 % 64`, `v / 64 % 64` and `v % 64`, so `omega` discharges the
round trips.
-/

@[expose] public section

namespace Silmaril

namespace Base64

/-! ## Alphabets -/

/-- A base64 alphabet: 64 distinct digit characters with an exact partial
inverse, not containing the pad character `'='`. -/
structure Alphabet where
  /-- The digit for each 6-bit value. -/
  digit : Fin 64 → Char
  /-- The value of a digit character (partial inverse of `digit`). -/
  value? : Char → Option (Fin 64)
  value?_digit : ∀ i, value? (digit i) = some i
  digit_of_value? : ∀ {c : Char} {i : Fin 64}, value? c = some i → digit i = c
  value?_pad : value? '=' = none
  digit_injective : Function.Injective digit

namespace Alphabet

variable (A : Alphabet)

theorem value?_eq_some_iff {c : Char} {i : Fin 64} : A.value? c = some i ↔ A.digit i = c :=
  ⟨A.digit_of_value?, fun h => h ▸ A.value?_digit i⟩

theorem digit_ne_pad (i : Fin 64) : A.digit i ≠ '=' := fun h => by
  have hi := A.value?_digit i
  rw [h, A.value?_pad] at hi
  cases hi

/-- The alphabet of a digit table, with `value?` by search; the side
conditions are decidable facts about the table. -/
def ofDigits (digit : Fin 64 → Char)
    (h : ∀ i, (List.finRange 64).find? (fun j => digit j == digit i) = some i)
    (hpad : (List.finRange 64).find? (fun j => digit j == '=') = none) : Alphabet where
  digit := digit
  value? c := (List.finRange 64).find? (fun j => digit j == c)
  value?_digit := h
  digit_of_value? {c i} hc := by
    have := List.find?_some hc
    simpa using this
  value?_pad := hpad
  digit_injective i j hij := by
    have hi := h i
    rw [hij, h j] at hi
    exact (Option.some.inj hi).symm

/-- The digit table shared by both RFC 4648 alphabets, with the last two
digits as parameters. -/
def table (d62 d63 : Char) (i : Fin 64) : Char :=
  if i.val < 26 then Char.ofNat (65 + i.val)
  else if i.val < 52 then Char.ofNat (71 + i.val)
  else if i.val < 62 then Char.ofNat (i.val - 4)
  else if i.val = 62 then d62 else d63

/-- The standard base64 alphabet (RFC 4648 §4): `A–Z a–z 0–9 + /`. -/
def std : Alphabet :=
  ofDigits (table '+' '/') (by decide) (by decide)

/-- The URL- and filename-safe alphabet (RFC 4648 §5): `A–Z a–z 0–9 - _`. -/
def url : Alphabet :=
  ofDigits (table '-' '_') (by decide) (by decide)

example : std.digit 0 = 'A' ∧ std.digit 25 = 'Z' ∧ std.digit 26 = 'a' ∧
    std.digit 51 = 'z' ∧ std.digit 52 = '0' ∧ std.digit 61 = '9' ∧
    std.digit 62 = '+' ∧ std.digit 63 = '/' := by decide

example : url.digit 62 = '-' ∧ url.digit 63 = '_' ∧ url.value? '+' = none := by decide

/-- The digit of a natural number, modulo 64. -/
def dig (n : Nat) : Char := A.digit ⟨n % 64, Nat.mod_lt _ (by decide)⟩

theorem dig_eq {n : Nat} {i : Fin 64} (h : n % 64 = i.val) : A.dig n = A.digit i :=
  congrArg A.digit (Fin.ext h)

theorem dig_ne_pad (n : Nat) : A.dig n ≠ '=' := A.digit_ne_pad _

@[simp] theorem value?_dig (n : Nat) : A.value? (A.dig n) = some ⟨n % 64, Nat.mod_lt _ (by decide)⟩ :=
  A.value?_digit _

/-! ## Group encoders -/

/-- A 3-byte group as 4 digits. -/
def enc3 (b0 b1 b2 : UInt8) : List Char :=
  [A.dig ((b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) / 262144),
   A.dig ((b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) / 4096),
   A.dig ((b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) / 64),
   A.dig (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat)]

/-- A 2-byte tail as 3 digits (2 zero pad bits). -/
def enc2 (b0 b1 : UInt8) : List Char :=
  [A.dig ((b0.toNat * 65536 + b1.toNat * 256) / 262144),
   A.dig ((b0.toNat * 65536 + b1.toNat * 256) / 4096),
   A.dig ((b0.toNat * 65536 + b1.toNat * 256) / 64)]

/-- A 1-byte tail as 2 digits (4 zero pad bits). -/
def enc1 (b0 : UInt8) : List Char :=
  [A.dig (b0.toNat * 65536 / 262144), A.dig (b0.toNat * 65536 / 4096)]

/-! ## Strict group decoders -/

/-- Four digits as a 3-byte group. -/
def dec4 (c0 c1 c2 c3 : Char) : Option (List UInt8) :=
  (A.value? c0).bind fun v0 => (A.value? c1).bind fun v1 =>
  (A.value? c2).bind fun v2 => (A.value? c3).bind fun v3 =>
    some [UInt8.ofNat ((v0.val * 262144 + v1.val * 4096 + v2.val * 64 + v3.val) / 65536),
          UInt8.ofNat ((v0.val * 262144 + v1.val * 4096 + v2.val * 64 + v3.val) / 256),
          UInt8.ofNat (v0.val * 262144 + v1.val * 4096 + v2.val * 64 + v3.val)]

/-- Three digits as a 2-byte tail; the 2 pad bits must be zero. -/
def dec3 (c0 c1 c2 : Char) : Option (List UInt8) :=
  (A.value? c0).bind fun v0 => (A.value? c1).bind fun v1 =>
  (A.value? c2).bind fun v2 =>
    if v2.val % 4 = 0 then
      some [UInt8.ofNat ((v0.val * 262144 + v1.val * 4096 + v2.val * 64) / 65536),
            UInt8.ofNat ((v0.val * 262144 + v1.val * 4096 + v2.val * 64) / 256)]
    else none

/-- Two digits as a 1-byte tail; the 4 pad bits must be zero. -/
def dec2 (c0 c1 : Char) : Option (List UInt8) :=
  (A.value? c0).bind fun v0 => (A.value? c1).bind fun v1 =>
    if v1.val % 16 = 0 then
      some [UInt8.ofNat ((v0.val * 262144 + v1.val * 4096) / 65536)]
    else none

/-- The last block of a padded spelling: `xx==`, `xxx=` or a full group. -/
def decLast (c0 c1 c2 c3 : Char) : Option (List UInt8) :=
  if c3 = '=' then (if c2 = '=' then A.dec2 c0 c1 else A.dec3 c0 c1 c2)
  else A.dec4 c0 c1 c2 c3

/-! ## Exactness of the group decoders -/

theorem dec4_eq_some_iff {c0 c1 c2 c3 : Char} {bs : List UInt8} :
    A.dec4 c0 c1 c2 c3 = some bs ↔
      ∃ b0 b1 b2, bs = [b0, b1, b2] ∧ A.enc3 b0 b1 b2 = [c0, c1, c2, c3] := by
  constructor
  · intro h
    simp only [dec4, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨v0, h0, v1, h1, v2, h2, v3, h3, rfl⟩ := h
    refine ⟨_, _, _, rfl, ?_⟩
    rw [← A.digit_of_value? h0, ← A.digit_of_value? h1, ← A.digit_of_value? h2,
      ← A.digit_of_value? h3]
    have := v0.isLt; have := v1.isLt; have := v2.isLt; have := v3.isLt
    simp only [enc3, UInt8.toNat_ofNat', Nat.reducePow, List.cons.injEq, and_true]
    refine ⟨A.dig_eq ?_, A.dig_eq ?_, A.dig_eq ?_, A.dig_eq ?_⟩ <;> omega
  · rintro ⟨b0, b1, b2, rfl, h⟩
    simp only [enc3, List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
    simp only [dec4, Alphabet.value?_dig, Option.bind_some, Option.some.injEq,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;>
      (simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow]; omega)

theorem dec3_eq_some_iff {c0 c1 c2 : Char} {bs : List UInt8} :
    A.dec3 c0 c1 c2 = some bs ↔ ∃ b0 b1, bs = [b0, b1] ∧ A.enc2 b0 b1 = [c0, c1, c2] := by
  constructor
  · intro h
    simp only [dec3, Option.bind_eq_some_iff] at h
    obtain ⟨v0, h0, v1, h1, v2, h2, h⟩ := h
    split at h
    · cases h
      refine ⟨_, _, rfl, ?_⟩
      rw [← A.digit_of_value? h0, ← A.digit_of_value? h1, ← A.digit_of_value? h2]
      have := v0.isLt; have := v1.isLt; have := v2.isLt
      simp only [enc2, UInt8.toNat_ofNat', Nat.reducePow, List.cons.injEq, and_true]
      refine ⟨A.dig_eq ?_, A.dig_eq ?_, A.dig_eq ?_⟩ <;> omega
    · cases h
  · rintro ⟨b0, b1, rfl, h⟩
    simp only [enc2, List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have := b0.toNat_lt; have := b1.toNat_lt
    simp only [dec3, Alphabet.value?_dig, Option.bind_some]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;>
      (simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow]; omega)

theorem dec2_eq_some_iff {c0 c1 : Char} {bs : List UInt8} :
    A.dec2 c0 c1 = some bs ↔ ∃ b0, bs = [b0] ∧ A.enc1 b0 = [c0, c1] := by
  constructor
  · intro h
    simp only [dec2, Option.bind_eq_some_iff] at h
    obtain ⟨v0, h0, v1, h1, h⟩ := h
    split at h
    · cases h
      refine ⟨_, rfl, ?_⟩
      rw [← A.digit_of_value? h0, ← A.digit_of_value? h1]
      have := v0.isLt; have := v1.isLt
      simp only [enc1, UInt8.toNat_ofNat', Nat.reducePow, List.cons.injEq, and_true]
      refine ⟨A.dig_eq ?_, A.dig_eq ?_⟩ <;> omega
    · cases h
  · rintro ⟨b0, rfl, h⟩
    simp only [enc1, List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := h
    have := b0.toNat_lt
    simp only [dec2, Alphabet.value?_dig, Option.bind_some]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow]
    omega

theorem enc3_ne_pad {b0 b1 b2 : UInt8} {c0 c1 c2 c3 : Char}
    (h : A.enc3 b0 b1 b2 = [c0, c1, c2, c3]) : c2 ≠ '=' ∧ c3 ≠ '=' := by
  simp only [enc3, List.cons.injEq, and_true] at h
  obtain ⟨-, -, rfl, rfl⟩ := h
  exact ⟨A.dig_ne_pad _, A.dig_ne_pad _⟩

theorem enc2_ne_pad {b0 b1 : UInt8} {c0 c1 c2 : Char}
    (h : A.enc2 b0 b1 = [c0, c1, c2]) : c2 ≠ '=' := by
  simp only [enc2, List.cons.injEq, and_true] at h
  obtain ⟨-, -, rfl⟩ := h
  exact A.dig_ne_pad _

end Alphabet

end Base64

end Silmaril
