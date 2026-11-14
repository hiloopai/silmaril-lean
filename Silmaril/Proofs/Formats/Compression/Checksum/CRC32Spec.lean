module

public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Silmaril.Formats.Compression.Checksum.Defs
public import Silmaril.Proofs.Formats.Compression.Checksum.GF2Poly
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32

/-! Proofs that the reflected shift register `crc32` computes `crc32Spec`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.CRC32

open Silmaril.Formats.Compression Silmaril.Formats.Compression.GF2Poly
open Silmaril.Proofs.Formats.Compression.GF2Poly

/-! ### The generator -/

theorem generator_ne_zero : crc32Generator ≠ 0 := by decide

theorem deg_generator : deg crc32Generator = 32 := by decide

/-- The register polynomial `0xEDB88320` is `G(x) - x³²`, reflected. -/
theorem reflect_poly : reflect 32 crc32Poly = crc32Generator ^^^ 2 ^ 32 := by decide

theorem reflect_ones : reflect 32 (ones 32) = ones 32 := by decide

theorem mod_eq_self_of_lt {a : Nat} (h : a < 2 ^ 32) : mod a crc32Generator = a :=
  mod_eq_self generator_ne_zero (by rw [deg_generator]; exact h)

/-! ### Reflection facts for 32-bit registers -/

/-- Shifting the reflected register towards `x³²` is shifting the register
towards bit `0`; the bit that falls out of the register becomes `x³²`. -/
theorem reflect_shiftLeft_one {c : Nat} (hc : c < 2 ^ 32) :
    reflect 32 c <<< 1 = reflect 32 (c / 2) ^^^ ((c.testBit 0).toNat <<< 32) :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_reflect, Nat.testBit_div_two,
      Nat.testBit_bool_toNat]
    rcases Nat.lt_or_ge i 1 with h | h
    · have : c.testBit 32 = false := Nat.testBit_lt_two_pow hc
      simp [show i = 0 by omega, this]
    rcases Nat.lt_or_ge i 32 with h' | h'
    · simp [h, h', show i - 1 < 32 by omega, show ¬ 32 ≤ i by omega]
      rw [show 31 - (i - 1) = 31 - i + 1 by omega]
    rcases Nat.lt_or_ge i 33 with h'' | h''
    · simp [show i = 32 by omega]
    · simp [show ¬ i - 1 < 32 by omega, show ¬ i < 32 by omega, show i - 32 ≠ 0 by omega]

/-- A byte lands in the low end of the register: the `x³¹ … x²⁴` coefficients. -/
theorem reflect_byte {b : Nat} (hb : b < 2 ^ 8) : reflect 32 b = reflect 8 b <<< 24 :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_shiftLeft, testBit_reflect]
    rcases Nat.lt_or_ge i 24 with h | h
    · have : 2 ^ 8 ≤ 2 ^ (32 - 1 - i) := Nat.pow_le_pow_right (by decide) (by omega)
      have : b.testBit (32 - 1 - i) = false := Nat.testBit_lt_two_pow (by omega)
      simp [this, show ¬ 24 ≤ i by omega]
    rcases Nat.lt_or_ge i 32 with h' | h'
    · simp [h, h', show i - 24 < 8 by omega, show 32 - 1 - i = 8 - 1 - (i - 24) by omega]
    · simp [show ¬ i < 32 by omega, show ¬ i - 24 < 8 by omega]

/-! ### One round: multiplication by `x` and reduction -/

/-- One round of the reflected shift register. -/
def round (c : Nat) : Nat := if c % 2 = 0 then c / 2 else c / 2 ^^^ crc32Poly

theorem go_succ (c k : Nat) : crc32Byte.go c (k + 1) = crc32Byte.go (round c) k := by
  rw [crc32Byte.go, round]; split <;> rfl

theorem round_lt {c : Nat} (hc : c < 2 ^ 32) : round c < 2 ^ 32 := by
  have := crc32Byte_go_lt c 1 hc
  rwa [go_succ] at this

theorem reflect_round {c : Nat} (hc : c < 2 ^ 32) :
    reflect 32 (round c) = mod (reflect 32 c <<< 1) crc32Generator := by
  have hlt := reflect_lt 32 (c / 2)
  rw [reflect_shiftLeft_one hc]
  by_cases h : c % 2 = 0
  · have e : round c = c / 2 := by simp [round, h]
    have tb : c.testBit 0 = false := by simp [Nat.testBit_zero, h]
    rw [e, tb, Bool.toNat_false, Nat.zero_shiftLeft, Nat.xor_zero, mod_eq_self_of_lt hlt]
  · have e : round c = c / 2 ^^^ crc32Poly := by simp [round, h]
    have tb : c.testBit 0 = true := by simp [Nat.testBit_zero]; omega
    rw [e, tb, Bool.toNat_true, Nat.one_shiftLeft, reflect_xor, reflect_poly]
    symm
    refine (mod_eq_iff generator_ne_zero).2 ⟨?_, 1, ?_⟩
    · rw [deg_generator]
      exact Nat.xor_lt_two_pow hlt (by decide)
    · rw [mul_one]
      have e (x y z : Nat) : x ^^^ z ^^^ (x ^^^ (y ^^^ z)) = x ^^^ x ^^^ y ^^^ (z ^^^ z) := by
        ac_rfl
      rw [e, Nat.xor_self, Nat.xor_self, Nat.zero_xor, Nat.xor_zero]

/-- `k` rounds multiply the (reflected) register by `xᵏ` modulo `G`. -/
theorem reflect_go {c : Nat} (hc : c < 2 ^ 32) (k : Nat) :
    reflect 32 (crc32Byte.go c k) = mod (reflect 32 c <<< k) crc32Generator := by
  induction k generalizing c with
  | zero => simp [crc32Byte.go, mod_eq_self_of_lt (reflect_lt 32 c)]
  | succ k ih =>
    rw [go_succ, ih (round_lt hc), reflect_round hc, mod_shiftLeft_mod _ _ generator_ne_zero,
      ← Nat.shiftLeft_add, Nat.add_comm 1 k]

/-! ### One byte: a Horner step -/

theorem reflect_crc32Byte {c b : Nat} (hc : c < 2 ^ 32) (hb : b < 2 ^ 8) :
    reflect 32 (crc32Byte c b) =
      mod ((reflect 32 c <<< 8) ^^^ (reflect 8 b <<< 32)) crc32Generator := by
  have hcb : c ^^^ b < 2 ^ 32 := Nat.xor_lt_two_pow hc (Nat.lt_trans hb (by decide))
  show reflect 32 (crc32Byte.go (c ^^^ b) 8) = _
  rw [reflect_go hcb, reflect_xor, reflect_byte hb, Nat.shiftLeft_xor_distrib,
    ← Nat.shiftLeft_add]

/-! ### The message polynomial -/

theorem messageBits_cons (b : UInt8) (bs : List UInt8) :
    messageBits (b :: bs) = byteBits b ++ messageBits bs := by
  simp [messageBits]

theorem length_byteBits (b : UInt8) : (byteBits b).length = 8 := by simp [byteBits]

theorem length_messageBits (bs : List UInt8) : (messageBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [messageBits_cons, List.length_append, length_byteBits, ih]; simp; omega

theorem messagePoly_nil : messagePoly [] = 0 := rfl

theorem messagePoly_cons (b : UInt8) (bs : List UInt8) :
    messagePoly (b :: bs) =
      (reflect 8 b.toNat <<< (messageBits bs).length) ^^^ messagePoly bs := by
  rw [messagePoly, messageBits_cons, ofBits_append]; rfl

/-! ### The register invariant -/

theorem foldl_lt {c : Nat} (hc : c < 2 ^ 32) (bytes : List UInt8) :
    (bytes.map UInt8.toNat).foldl crc32Byte c < 2 ^ 32 := by
  induction bytes generalizing c with
  | nil => exact hc
  | cons b bs ih => exact ih (crc32Byte_lt _ _ hc (UInt8.toNat_lt b))

/-- Absorbing a message `M` of `k` bits into a register holding (reflected)
`R` leaves (reflected) `(R · xᵏ + M · x³²) mod G`. -/
theorem reflect_foldl {c : Nat} (hc : c < 2 ^ 32) (bytes : List UInt8) :
    reflect 32 ((bytes.map UInt8.toNat).foldl crc32Byte c) =
      mod ((reflect 32 c <<< (messageBits bytes).length) ^^^ (messagePoly bytes <<< 32))
        crc32Generator := by
  induction bytes generalizing c with
  | nil =>
    rw [List.map_nil, List.foldl_nil, messagePoly_nil, show (messageBits []).length = 0 from rfl,
      Nat.shiftLeft_zero, Nat.zero_shiftLeft, Nat.xor_zero, mod_eq_self_of_lt (reflect_lt 32 c)]
  | cons b bs ih =>
    have hG := generator_ne_zero
    rw [List.map_cons, List.foldl_cons, ih (crc32Byte_lt _ _ hc (UInt8.toNat_lt b)),
      reflect_crc32Byte hc (UInt8.toNat_lt b), mod_xor _ _ hG, mod_shiftLeft_mod _ _ hG,
      ← mod_xor _ _ hG, messagePoly_cons, messageBits_cons, List.length_append, length_byteBits]
    refine congrArg (fun x => mod x crc32Generator) ?_
    generalize (messageBits bs).length = L
    generalize reflect 32 c = R
    generalize reflect 8 b.toNat = B
    generalize messagePoly bs = M
    rw [Nat.shiftLeft_xor_distrib, Nat.shiftLeft_xor_distrib,
      ← Nat.shiftLeft_add, ← Nat.shiftLeft_add, ← Nat.shiftLeft_add, Nat.add_comm 32 L,
      Nat.xor_assoc]

/-- The register after a message is the reflected CRC remainder. -/
theorem reflect_crc32State (bytes : List UInt8) :
    reflect 32 (crc32State (bytes.map UInt8.toNat)) = crc32Remainder bytes := by
  rw [crc32State, reflect_foldl (by decide), crc32Remainder]
  show mod ((reflect 32 (ones 32) <<< _) ^^^ _) _ = _
  rw [reflect_ones, mod_xor _ _ generator_ne_zero]

theorem crc32List_eq_reflect (bytes : List UInt8) :
    crc32List (bytes.map UInt8.toNat) = reflect 32 (add (crc32Remainder bytes) (ones 32)) := by
  have hs : crc32State (bytes.map UInt8.toNat) < 2 ^ 32 := foldl_lt (by decide) bytes
  rw [← reflect_crc32State, add, reflect_xor, reflect_reflect hs, reflect_ones]
  rfl

/-! ### Main theorems -/

theorem crc32List_eq_spec (bytes : List UInt8) :
    crc32List (bytes.map UInt8.toNat) = (crc32Spec bytes).toNat := by
  rw [crc32Spec, ← crc32List_eq_reflect, UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  exact crc32List_lt _ (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact UInt8.toNat_lt a)

theorem crc32_eq_spec (data : ByteArray) : crc32 data = crc32Spec data.data.toList := by
  rw [crc32Spec, ← crc32List_eq_reflect]; rfl

theorem digest_eq_spec (bytes : List UInt8) : Checksum.crc32.digest bytes = crc32Spec bytes := by
  rw [crc32Spec, ← crc32List_eq_reflect]
  simp only [Checksum.digest, Checksum.crc32, crc32List, List.foldl_map]

/-! ### Linearity of the register -/

theorem xor_mod_two (c d : Nat) : (c ^^^ d) % 2 = (c % 2 + d % 2) % 2 := by
  have h := Nat.testBit_xor c d 0
  cases hc : c.testBit 0 <;> cases hd : d.testBit 0 <;> simp only [hc, hd] at h <;>
    simp only [Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not, Bool.xor_false,
      Bool.xor_true, Bool.not_false, Bool.not_true] at hc hd h <;> omega

theorem round_xor (c d : Nat) : round (c ^^^ d) = round c ^^^ round d := by
  simp only [round, xor_div_two]
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · rw [show (c ^^^ d) % 2 = 0 by rw [xor_mod_two, hc, hd]]; simp [hc, hd]
  · rw [show (c ^^^ d) % 2 = 1 by rw [xor_mod_two, hc, hd]]; simp [hc, hd]; ac_rfl
  · rw [show (c ^^^ d) % 2 = 1 by rw [xor_mod_two, hc, hd]]; simp [hc, hd]; ac_rfl
  · rw [show (c ^^^ d) % 2 = 0 by rw [xor_mod_two, hc, hd]]; simp only [hc, hd]; simp
    rw [show c / 2 ^^^ crc32Poly ^^^ (d / 2 ^^^ crc32Poly) =
      c / 2 ^^^ d / 2 ^^^ (crc32Poly ^^^ crc32Poly) by ac_rfl, Nat.xor_self, Nat.xor_zero]

theorem go_xor (c d k : Nat) : crc32Byte.go (c ^^^ d) k = crc32Byte.go c k ^^^ crc32Byte.go d k := by
  induction k generalizing c d with
  | zero => rfl
  | succ k ih => rw [go_succ, go_succ, go_succ, round_xor, ih]

theorem crc32Byte_xor (c d b e : Nat) :
    crc32Byte (c ^^^ d) (b ^^^ e) = crc32Byte c b ^^^ crc32Byte d e := by
  show crc32Byte.go _ 8 = crc32Byte.go _ 8 ^^^ crc32Byte.go _ 8
  rw [← go_xor, show c ^^^ d ^^^ (b ^^^ e) = c ^^^ b ^^^ (d ^^^ e) by ac_rfl]

theorem foldl_crc32Byte_xor (c d : Nat) (as bs : List Nat) (h : as.length = bs.length) :
    (List.zipWith (· ^^^ ·) as bs).foldl crc32Byte (c ^^^ d) =
      as.foldl crc32Byte c ^^^ bs.foldl crc32Byte d := by
  induction as generalizing bs c d with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.foldl_cons]
      rw [crc32Byte_xor, ih _ _ _ (by simpa using h)]

/-! ### Single-bit errors -/

/-- Multiplying a nonzero remainder by `x` modulo `G` gives a nonzero remainder,
because `G` has a constant term. -/
theorem mod_shiftLeft_one_ne_zero {r : Nat} (hr : r ≠ 0) (hlt : r < 2 ^ 32) :
    mod (r <<< 1) crc32Generator ≠ 0 := by
  by_cases h : r <<< 1 < 2 ^ 32
  · rw [mod_eq_self_of_lt h, Nat.shiftLeft_eq]; omega
  · have hG1 : 2 ^ 32 ≤ crc32Generator := by decide
    have hG2 : crc32Generator < 2 ^ 33 := by decide
    have h2 : r <<< 1 < 2 ^ 33 := by rw [Nat.shiftLeft_eq]; omega
    have hx := xor_lt_of_bounds (by omega) h2 hG1 hG2
    have e : mod (r <<< 1) crc32Generator = r <<< 1 ^^^ crc32Generator := by
      refine (mod_eq_iff generator_ne_zero).2 ⟨by rw [deg_generator]; exact hx, 1, ?_⟩
      rw [mul_one, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [e]
    intro h0
    have := congrArg (·.testBit 0) h0
    simp at this
    exact absurd this (by decide)

/-- No power of `x` is divisible by `G`. -/
theorem mod_monomial_ne_zero (k : Nat) : mod (1 <<< k) crc32Generator ≠ 0 := by
  induction k with
  | zero => rw [mod_eq_self_of_lt (by decide)]; decide
  | succ k ih =>
    rw [Nat.shiftLeft_add, ← mod_shiftLeft_mod _ _ generator_ne_zero]
    exact mod_shiftLeft_one_ne_zero ih (by rw [← deg_generator]; exact mod_lt _ generator_ne_zero)

theorem reflect_two_pow {i : Nat} (hi : i < 8) : reflect 8 (2 ^ i) = 1 <<< (7 - i) :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_reflect, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases hj : j < 8
    · simp only [hj, decide_true, Bool.true_and]; congr 1; apply propext; omega
    · simp only [hj, decide_false, Bool.false_and]; symm; simp; omega

/-- Flipping one bit of the message adds a monomial to the message polynomial. -/
theorem messagePoly_flip (bytes : List UInt8) {p i : Nat} (hp : p < bytes.length) (hi : i < 8) :
    ∃ j, messagePoly (bytes.modify p (· ^^^ UInt8.ofNat (2 ^ i))) =
      messagePoly bytes ^^^ (1 <<< j) := by
  induction bytes generalizing p with
  | nil => simp at hp
  | cons b bs ih =>
    rcases p with _ | p
    · refine ⟨7 - i + (messageBits bs).length, ?_⟩
      have ht : (UInt8.ofNat (2 ^ i)).toNat = 2 ^ i := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hi)]
      rw [List.modify_zero_cons, messagePoly_cons, messagePoly_cons, UInt8.toNat_xor, ht,
        reflect_xor, reflect_two_pow hi, Nat.shiftLeft_xor_distrib, ← Nat.shiftLeft_add]
      ac_rfl
    · obtain ⟨j, hj⟩ := ih (p := p) (by simp at hp; omega)
      refine ⟨j, ?_⟩
      have hl : (messageBits (bs.modify p (· ^^^ UInt8.ofNat (2 ^ i)))).length =
          (messageBits bs).length := by
        rw [length_messageBits, length_messageBits, List.length_modify]
      rw [List.modify_succ_cons, messagePoly_cons, messagePoly_cons, hl, hj]
      ac_rfl

theorem crc32Remainder_lt (bytes : List UInt8) : crc32Remainder bytes < 2 ^ 32 := by
  rw [← deg_generator]
  exact Nat.xor_lt_two_pow (mod_lt _ generator_ne_zero) (mod_lt _ generator_ne_zero)

theorem crc32Spec_injective {a b : List UInt8} (h : crc32Spec a = crc32Spec b) :
    crc32Remainder a = crc32Remainder b := by
  have h1 := congrArg UInt32.toNat h
  rw [← crc32List_eq_spec, ← crc32List_eq_spec, crc32List_eq_reflect, crc32List_eq_reflect]
    at h1
  have h2 := congrArg (reflect 32) h1
  rw [reflect_reflect (Nat.xor_lt_two_pow (crc32Remainder_lt a) (by decide)),
    reflect_reflect (Nat.xor_lt_two_pow (crc32Remainder_lt b) (by decide))] at h2
  have h3 := congrArg (· ^^^ ones 32) h2
  simpa only [add, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using h3

/-- CRC-32 detects every single-bit error. -/
theorem crc32Spec_flip_ne (bytes : List UInt8) {p i : Nat} (hp : p < bytes.length) (hi : i < 8) :
    crc32Spec (bytes.modify p (· ^^^ UInt8.ofNat (2 ^ i))) ≠ crc32Spec bytes := by
  intro h
  have h1 := crc32Spec_injective h
  obtain ⟨j, hj⟩ := messagePoly_flip bytes hp hi
  have hl : (messageBits (bytes.modify p (· ^^^ UInt8.ofNat (2 ^ i)))).length =
      (messageBits bytes).length := by
    rw [length_messageBits, length_messageBits, List.length_modify]
  simp only [crc32Remainder, add, mulXPow] at h1
  rw [hl, hj, Nat.shiftLeft_xor_distrib, mod_xor _ _ generator_ne_zero] at h1
  generalize mod (ones 32 <<< (messageBits bytes).length) crc32Generator = A at h1
  generalize mod (messagePoly bytes <<< 32) crc32Generator = B at h1
  have h2 : A ^^^ (B ^^^ mod (1 <<< j <<< 32) crc32Generator) ^^^ (A ^^^ B) =
      mod (1 <<< j <<< 32) crc32Generator := by
    generalize mod (1 <<< j <<< 32) crc32Generator = E
    rw [show A ^^^ (B ^^^ E) ^^^ (A ^^^ B) = E ^^^ (A ^^^ A) ^^^ (B ^^^ B) by ac_rfl,
      Nat.xor_self, Nat.xor_self, Nat.xor_zero, Nat.xor_zero]
  rw [h1, Nat.xor_self, ← Nat.shiftLeft_add] at h2
  exact mod_monomial_ne_zero (j + 32) h2.symm

end Silmaril.Proofs.Formats.Compression.CRC32
