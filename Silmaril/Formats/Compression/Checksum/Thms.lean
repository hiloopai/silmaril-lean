module

public import Silmaril.Formats.Compression.Checksum.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Silmaril.Formats.Compression.Thms
import Silmaril.Proofs.Formats.Compression.Checksum
import Silmaril.Proofs.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Proofs.Formats.Compression.Checksum.GF2Poly
import Silmaril.Raw.Formats.Compression.Checksum.Adler32
import Silmaril.Raw.Formats.Compression.Checksum.CRC32

/-!
# Checksums: facts

Proved (standard axioms):

* `adler32_digest`, `adler32_digest_byteArray`, `crc32_digest`: the incremental
  checksums compute the format modules' check values;
* the published check values: Adler-32 of `"Wikipedia"` is `0x11E60398`
  (RFC 1950 §9's example) and of `"123456789"` is `0x091E01DE`; CRC-32 of
  `"123456789"` is `0xCBF43926`;
* `adler32_lt`, `crc32Byte_lt`, `crc32List_lt`, `crc32List_append`: range and
  incremental laws;
* GF(2) polynomials (`GF2Poly`): `mod a g` is the unique remainder of degree
  below `deg g` (`mod_eq_iff`), additive (`mod_xor`) and compatible with
  multiplication by `xᵏ` (`mod_shiftLeft_mod`);
* CRC-32 meets its declarative specification (`crc32Spec`, ISO 3309 / ITU-T V.42
  as cited by RFC 1952 §8): `crc32_eq_spec`, `crc32List_eq_spec` and
  `Checksum.crc32_digest_eq_spec`, via `reflect_crc32Byte_go` (a round of the
  reflected register multiplies by `x` modulo `G`), `reflect_crc32Byte` (a byte
  is a Horner step) and `reflect_crc32State` (the register is the reflected
  remainder); the register is linear (`crc32Byte_xor`, `foldl_crc32Byte_xor`);
* CRC-32 detects every single-bit error (`crc32Spec_flip_ne`), as `G` divides no
  power of `x` (`mod_monomial_ne_zero`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Checksum

theorem adler32_digest (bytes : List UInt8) : adler32.digest bytes = adler32List bytes :=
  Proofs.Formats.Compression.adler32_digest bytes

theorem adler32_digest_byteArray (bytes : ByteArray) :
    adler32.digest bytes.data.toList = Compression.adler32 bytes :=
  Proofs.Formats.Compression.adler32_digest_byteArray bytes

theorem crc32_digest (bytes : ByteArray) : crc32.digest bytes.data.toList = Compression.crc32 bytes :=
  Proofs.Formats.Compression.crc32_digest bytes

/-- RFC 1950 §9's example: the Adler-32 of `"Wikipedia"` is `0x11E60398`. -/
theorem adler32_check_wikipedia :
    adler32.digest [0x57, 0x69, 0x6B, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61] = 0x11E60398 := by
  rw [adler32_digest]; decide

/-- The Adler-32 of `"123456789"` is `0x091E01DE`. -/
theorem adler32_check_123456789 :
    adler32.digest [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0x091E01DE := by
  rw [adler32_digest]; decide

/-- The standard CRC-32 check value: the CRC-32 of `"123456789"` is `0xCBF43926`. -/
theorem crc32_check_123456789 :
    crc32.digest [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xCBF43926 :=
  (crc32_digest ⟨#[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]⟩).trans
    Compression.crc32_check

theorem adler32_lt (data : List Nat) : adler32OfList data < 2 ^ 32 :=
  adler32OfList_lt data

theorem crc32List_append (a b : List Nat) :
    crc32List (a ++ b) = b.foldl crc32Byte (crc32List a ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF :=
  Compression.crc32List_append a b

theorem crc32Byte_lt (c b : Nat) (hc : c < 2 ^ 32) (hb : b < 256) : crc32Byte c b < 2 ^ 32 :=
  Compression.crc32Byte_lt c b hc hb

theorem crc32List_lt (data : List Nat) (h : ∀ b ∈ data, b < 256) : crc32List data < 2 ^ 32 :=
  Compression.crc32List_lt data h

/-- The framework CRC-32 computes the declarative specification. -/
theorem crc32_digest_eq_spec (bytes : List UInt8) : crc32.digest bytes = crc32Spec bytes :=
  Proofs.Formats.Compression.CRC32.digest_eq_spec bytes

end Silmaril.Formats.Compression.Checksum

/-! ### Polynomials over GF(2) -/

namespace Silmaril.Formats.Compression.GF2Poly

/-- Long division leaves a remainder of degree below `deg g`. -/
theorem mod_lt (a : Nat) {g : Nat} (hg : g ≠ 0) : mod a g < 2 ^ deg g :=
  Proofs.Formats.Compression.GF2Poly.mod_lt a hg

/-- `mod a g` is the unique polynomial of degree below `deg g` that differs from
`a` by a multiple of `g`. -/
theorem mod_eq_iff {a g r : Nat} (hg : g ≠ 0) :
    mod a g = r ↔ r < 2 ^ deg g ∧ ∃ q, add a r = mul g q :=
  Proofs.Formats.Compression.GF2Poly.mod_eq_iff hg

/-- Division with remainder: `a = g · q + (a mod g)`. -/
theorem exists_eq_mul_add_mod (a g : Nat) : ∃ q, a = add (mul g q) (mod a g) :=
  Proofs.Formats.Compression.GF2Poly.exists_eq_mul_xor_mod a g

theorem mod_add (a b : Nat) {g : Nat} (hg : g ≠ 0) : mod (add a b) g = add (mod a g) (mod b g) :=
  Proofs.Formats.Compression.GF2Poly.mod_xor a b hg

theorem mod_mulXPow_mod (a k : Nat) {g : Nat} (hg : g ≠ 0) :
    mod (mulXPow k (mod a g)) g = mod (mulXPow k a) g :=
  Proofs.Formats.Compression.GF2Poly.mod_shiftLeft_mod a k hg

theorem mod_mul_self (g q : Nat) (hg : g ≠ 0) : mod (mul g q) g = 0 :=
  Proofs.Formats.Compression.GF2Poly.mod_mul_self g q hg

theorem mul_add (a b c : Nat) : mul a (add b c) = add (mul a b) (mul a c) :=
  Proofs.Formats.Compression.GF2Poly.mul_xor a b c

theorem ofBits_append (as bs : List Bool) :
    ofBits (as ++ bs) = add (mulXPow bs.length (ofBits as)) (ofBits bs) :=
  Proofs.Formats.Compression.GF2Poly.ofBits_append as bs

theorem ofBits_lt (bs : List Bool) : ofBits bs < 2 ^ bs.length :=
  Proofs.Formats.Compression.GF2Poly.ofBits_lt bs

theorem testBit_reflect (n r i : Nat) :
    (reflect n r).testBit i = (decide (i < n) && r.testBit (n - 1 - i)) :=
  Proofs.Formats.Compression.GF2Poly.testBit_reflect n r i

theorem reflect_add (n a b : Nat) : reflect n (add a b) = add (reflect n a) (reflect n b) :=
  Proofs.Formats.Compression.GF2Poly.reflect_xor n a b

theorem reflect_reflect {n r : Nat} (h : r < 2 ^ n) : reflect n (reflect n r) = r :=
  Proofs.Formats.Compression.GF2Poly.reflect_reflect h

end Silmaril.Formats.Compression.GF2Poly

/-! ### CRC-32 against its specification -/

namespace Silmaril.Formats.Compression

open GF2Poly

/-- `k` rounds of the reflected shift register multiply the register, read as
the reflected polynomial, by `xᵏ` modulo `G`. -/
theorem reflect_crc32Byte_go {c : Nat} (hc : c < 2 ^ 32) (k : Nat) :
    reflect 32 (crc32Byte.go c k) = mod (mulXPow k (reflect 32 c)) crc32Generator :=
  Proofs.Formats.Compression.CRC32.reflect_go hc k

/-- Absorbing a byte `b` into the register `R` is the Horner step
`R ↦ (R · x⁸ + B · x³²) mod G`, where `B` is `b` read least significant bit first. -/
theorem reflect_crc32Byte {c b : Nat} (hc : c < 2 ^ 32) (hb : b < 2 ^ 8) :
    reflect 32 (crc32Byte c b) =
      mod (add (mulXPow 8 (reflect 32 c)) (mulXPow 32 (reflect 8 b))) crc32Generator :=
  Proofs.Formats.Compression.CRC32.reflect_crc32Byte hc hb

/-- The register after a message is the reflected CRC remainder. -/
theorem reflect_crc32State (bytes : List UInt8) :
    reflect 32 (crc32State (bytes.map UInt8.toNat)) = crc32Remainder bytes :=
  Proofs.Formats.Compression.CRC32.reflect_crc32State bytes

/-- **CRC-32 is correct**: the shift-register CRC equals the declarative one. -/
theorem crc32List_eq_spec (bytes : List UInt8) :
    crc32List (bytes.map UInt8.toNat) = (crc32Spec bytes).toNat :=
  Proofs.Formats.Compression.CRC32.crc32List_eq_spec bytes

theorem crc32_eq_spec (data : ByteArray) : crc32 data = crc32Spec data.data.toList :=
  Proofs.Formats.Compression.CRC32.crc32_eq_spec data

theorem crc32Remainder_lt (bytes : List UInt8) : crc32Remainder bytes < 2 ^ 32 :=
  Proofs.Formats.Compression.CRC32.crc32Remainder_lt bytes

theorem messagePoly_cons (b : UInt8) (bs : List UInt8) :
    messagePoly (b :: bs) = add (mulXPow (messageBits bs).length (reflect 8 b.toNat))
      (messagePoly bs) :=
  Proofs.Formats.Compression.CRC32.messagePoly_cons b bs

/-- The register update is GF(2)-linear in the register and the byte jointly. -/
theorem crc32Byte_xor (c d b e : Nat) :
    crc32Byte (c ^^^ d) (b ^^^ e) = crc32Byte c b ^^^ crc32Byte d e :=
  Proofs.Formats.Compression.CRC32.crc32Byte_xor c d b e

theorem foldl_crc32Byte_xor (c d : Nat) (as bs : List Nat) (h : as.length = bs.length) :
    (List.zipWith (· ^^^ ·) as bs).foldl crc32Byte (c ^^^ d) =
      as.foldl crc32Byte c ^^^ bs.foldl crc32Byte d :=
  Proofs.Formats.Compression.CRC32.foldl_crc32Byte_xor c d as bs h

/-- `G` divides no power of `x`. -/
theorem mod_monomial_ne_zero (k : Nat) : mod (mulXPow k 1) crc32Generator ≠ 0 :=
  Proofs.Formats.Compression.CRC32.mod_monomial_ne_zero k

/-- CRC-32 detects every single-bit error: flipping bit `i` of byte `p` changes
the check value. -/
theorem crc32Spec_flip_ne (bytes : List UInt8) {p i : Nat} (hp : p < bytes.length) (hi : i < 8) :
    crc32Spec (bytes.modify p (· ^^^ UInt8.ofNat (2 ^ i))) ≠ crc32Spec bytes :=
  Proofs.Formats.Compression.CRC32.crc32Spec_flip_ne bytes hp hi

end Silmaril.Formats.Compression
