module

public import Mathlib.Data.UInt
public import Mathlib.Data.BitVec
public import Mathlib.Tactic

/-!
# Shared word utilities for cryptographic and non-cryptographic hash functions

Word rotations, endianness conversions, packing/unpacking, and XOR operations
for 32-bit and 64-bit words. Used by MD5, SHA-1, SHA-256, BLAKE3, and others.

## Operations
- `rotl32` / `rotr32`, `rotl64` / `rotr64`: rotations (mod width)
- `toBytesBE32` / `ofBytesBE32` / `toBytesLE32` / `ofBytesLE32`: 32-bit endianness
- `toBytesBE64` / `ofBytesBE64` / `toBytesLE64` / `ofBytesLE64`: 64-bit endianness
- `rotateRight` / `pack32LE` / `unpack32LE` / `xor32` / `xor4`: BLAKE3 helpers

## Theorems
- `rotl32_zero`, `rotr32_zero`, `rotl64_zero`, `rotr64_zero`: rotating by 0 is
  the identity, for every word (not just a sampled one).
- `rotr32_rotl32`, `rotl32_rotr32`, `rotr64_rotl64`, `rotl64_rotr64`: the two
  rotations are mutually inverse, for every word and every shift amount.
- `rotl32_mod`, `rotl64_mod`: rotations only depend on the shift mod the width.
- `ofBytesBE32_toBytesBE32`, `toBytesBE32_ofBytesBE32`: 32-bit BE round-trips
- `ofBytesLE32_toBytesLE32`, `toBytesLE32_ofBytesLE32`: 32-bit LE round-trips
- `ofBytesBE64_toBytesBE64`, `toBytesBE64_ofBytesBE64`: 64-bit BE round-trips
  (these are the conversions SHA-512 depends on)
- `ofBytesLE64_toBytesLE64`, `toBytesLE64_ofBytesLE64`: 64-bit LE round-trips
- `Word.rotateRight_eq_rotr32`, `Word.pack32LE_eq_ofBytesLE32`,
  `Word.unpack32LE_eq_toBytesLE32`: the BLAKE3-facing names agree with the
  canonical ones (they are now definitions in terms of them).
-/

@[expose] public section

namespace Silmaril.Crypto

def rotl32 (x : UInt32) (n : Nat) : UInt32 :=
  let n' := n % 32
  let bv := BitVec.ofNat 32 x.toNat
  UInt32.ofNat (bv.rotateLeft n').toNat

def rotr32 (x : UInt32) (n : Nat) : UInt32 :=
  let n' := n % 32
  let bv := BitVec.ofNat 32 x.toNat
  UInt32.ofNat (bv.rotateRight n').toNat

def rotl64 (x : UInt64) (n : Nat) : UInt64 :=
  let n' := n % 64
  let bv := BitVec.ofNat 64 x.toNat
  UInt64.ofNat (bv.rotateLeft n').toNat

def rotr64 (x : UInt64) (n : Nat) : UInt64 :=
  let n' := n % 64
  let bv := BitVec.ofNat 64 x.toNat
  UInt64.ofNat (bv.rotateRight n').toNat

def toBytesBE32 (x : UInt32) : UInt8 × UInt8 × UInt8 × UInt8 :=
  let n := x.toNat
  (UInt8.ofNat (n / 256 ^ 3),
   UInt8.ofNat ((n / 256 ^ 2) % 256),
   UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat (n % 256))

def toBytesLE32 (x : UInt32) : UInt8 × UInt8 × UInt8 × UInt8 :=
  let n := x.toNat
  (UInt8.ofNat (n % 256),
   UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat ((n / 256 ^ 2) % 256),
   UInt8.ofNat (n / 256 ^ 3))

def ofBytesBE32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat ((b0.toNat % 256) * 256 ^ 3 + (b1.toNat % 256) * 256 ^ 2
              + (b2.toNat % 256) * 256 + (b3.toNat % 256))

def ofBytesLE32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat ((b0.toNat % 256) + (b1.toNat % 256) * 256
              + (b2.toNat % 256) * 256 ^ 2 + (b3.toNat % 256) * 256 ^ 3)

def toBytesBE64 (x : UInt64) : UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 :=
  let n := x.toNat
  (UInt8.ofNat (n / 256 ^ 7),
   UInt8.ofNat ((n / 256 ^ 6) % 256),
   UInt8.ofNat ((n / 256 ^ 5) % 256),
   UInt8.ofNat ((n / 256 ^ 4) % 256),
   UInt8.ofNat ((n / 256 ^ 3) % 256),
   UInt8.ofNat ((n / 256 ^ 2) % 256),
   UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat (n % 256))

def toBytesLE64 (x : UInt64) : UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 × UInt8 :=
  let n := x.toNat
  (UInt8.ofNat (n % 256),
   UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat ((n / 256 ^ 2) % 256),
   UInt8.ofNat ((n / 256 ^ 3) % 256),
   UInt8.ofNat ((n / 256 ^ 4) % 256),
   UInt8.ofNat ((n / 256 ^ 5) % 256),
   UInt8.ofNat ((n / 256 ^ 6) % 256),
   UInt8.ofNat (n / 256 ^ 7))

def ofBytesBE64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  UInt64.ofNat ((b0.toNat % 256) * 256 ^ 7 + (b1.toNat % 256) * 256 ^ 6
              + (b2.toNat % 256) * 256 ^ 5 + (b3.toNat % 256) * 256 ^ 4
              + (b4.toNat % 256) * 256 ^ 3 + (b5.toNat % 256) * 256 ^ 2
              + (b6.toNat % 256) * 256 + (b7.toNat % 256))

def ofBytesLE64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  UInt64.ofNat ((b0.toNat % 256) + (b1.toNat % 256) * 256
              + (b2.toNat % 256) * 256 ^ 2 + (b3.toNat % 256) * 256 ^ 3
              + (b4.toNat % 256) * 256 ^ 4 + (b5.toNat % 256) * 256 ^ 5
              + (b6.toNat % 256) * 256 ^ 6 + (b7.toNat % 256) * 256 ^ 7)

/-! ### Helper lemmas -/

private lemma uint8_lt_256 (b : UInt8) : b.toNat < 256 := by
  have h := b.toBitVec.isLt
  simpa using h

private lemma uint64_lt_256p8 (x : UInt64) : x.toNat < 256 ^ 8 := by
  have : 256 ^ 8 = 2 ^ 64 := by norm_num
  have h := x.toBitVec.isLt
  simpa [this] using h

private lemma uint64_eq_of_toNat_eq {x y : UInt64} (h : x.toNat = y.toNat) : x = y := by
  calc
    x = UInt64.ofNat x.toNat := by symm; exact UInt64.ofNat_toNat
    _ = UInt64.ofNat y.toNat := by rw [h]
    _ = y := UInt64.ofNat_toNat

private lemma uint32_lt_256p4 (x : UInt32) : x.toNat < 256 ^ 4 := by
  have : 256 ^ 4 = 2 ^ 32 := by norm_num
  have h := x.toBitVec.isLt
  simpa [this] using h

private lemma uint32_eq_of_toNat_eq {x y : UInt32} (h : x.toNat = y.toNat) : x = y := by
  calc
    x = UInt32.ofNat x.toNat := by symm; exact UInt32.ofNat_toNat
    _ = UInt32.ofNat y.toNat := by rw [h]
    _ = y := UInt32.ofNat_toNat

private lemma uint8_eq_of_toNat_eq {x y : UInt8} (h : x.toNat = y.toNat) : x = y := by
  calc
    x = UInt8.ofNat x.toNat := by symm; exact UInt8.ofNat_toNat
    _ = UInt8.ofNat y.toNat := by rw [h]
    _ = y := UInt8.ofNat_toNat

/-! ### 32-bit big-endian round-trip -/

set_option maxHeartbeats 600000 in
theorem ofBytesBE32_toBytesBE32 (x : UInt32) : ofBytesBE32
    ((toBytesBE32 x).1) ((toBytesBE32 x).2.1) ((toBytesBE32 x).2.2.1) ((toBytesBE32 x).2.2.2) = x := by
  apply uint32_eq_of_toNat_eq
  dsimp [toBytesBE32, ofBytesBE32]
  simp [UInt32.toNat_ofNat]
  have hx := uint32_lt_256p4 x
  omega

set_option maxHeartbeats 600000 in
theorem toBytesBE32_ofBytesBE32 (b0 b1 b2 b3 : UInt8) : toBytesBE32 (ofBytesBE32 b0 b1 b2 b3) = (b0, b1, b2, b3) := by
  have h0 := uint8_lt_256 b0
  have h1 := uint8_lt_256 b1
  have h2 := uint8_lt_256 b2
  have h3 := uint8_lt_256 b3
  dsimp [toBytesBE32, ofBytesBE32]
  simp [UInt32.toNat_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uint8_eq_of_toNat_eq; simp; omega
  · apply uint8_eq_of_toNat_eq; simp; omega
  · apply uint8_eq_of_toNat_eq; simp; omega
  · apply uint8_eq_of_toNat_eq; simp; omega

/-! ### 32-bit little-endian round-trip -/

set_option maxHeartbeats 600000 in
theorem ofBytesLE32_toBytesLE32 (x : UInt32) : ofBytesLE32
    ((toBytesLE32 x).1) ((toBytesLE32 x).2.1) ((toBytesLE32 x).2.2.1) ((toBytesLE32 x).2.2.2) = x := by
  apply uint32_eq_of_toNat_eq
  dsimp [toBytesLE32, ofBytesLE32]
  simp [UInt32.toNat_ofNat]
  have hx := uint32_lt_256p4 x
  omega

set_option maxHeartbeats 600000 in
theorem toBytesLE32_ofBytesLE32 (b0 b1 b2 b3 : UInt8) : toBytesLE32 (ofBytesLE32 b0 b1 b2 b3) = (b0, b1, b2, b3) := by
  have h0 := uint8_lt_256 b0
  have h1 := uint8_lt_256 b1
  have h2 := uint8_lt_256 b2
  have h3 := uint8_lt_256 b3
  dsimp [toBytesLE32, ofBytesLE32]
  simp [UInt32.toNat_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uint8_eq_of_toNat_eq; simp; omega
  · apply uint8_eq_of_toNat_eq; simp; omega
  · apply uint8_eq_of_toNat_eq; simp; omega
  · apply uint8_eq_of_toNat_eq; simp; omega

/-! ### Rotation theorems

These are the universally quantified facts (FIPS 180-4 §3.2): the point-value
`decide` examples that used to live in `WordUtils.lean` were satisfied by a
rotation special-cased to the sampled inputs.
-/


private theorem bitvec_rotateRight_rotateLeft {w : Nat} (x : BitVec w) (r : Nat) : (x.rotateLeft r).rotateRight r = x := by
  ext i hi
  have hw : 0 < w := by omega
  have hr : r % w < w := Nat.mod_lt _ hw
  rw [BitVec.getElem_rotateRight]
  split <;> rename_i h1 <;>
    rw [BitVec.getElem_rotateLeft (by omega)] <;> split <;> rename_i h2
  · exact absurd h2 (by omega)
  · congr 1; omega
  · congr 1; omega
  · exact absurd h2 (by omega)

private theorem bitvec_rotateLeft_rotateRight {w : Nat} (x : BitVec w) (r : Nat) : (x.rotateRight r).rotateLeft r = x := by
  ext i hi
  have hw : 0 < w := by omega
  have hr : r % w < w := Nat.mod_lt _ hw
  rw [BitVec.getElem_rotateLeft]
  split <;> rename_i h1 <;>
    rw [BitVec.getElem_rotateRight (by omega)] <;> split <;> rename_i h2
  · exact absurd h2 (by omega)
  · congr 1; omega
  · congr 1; omega
  · exact absurd h2 (by omega)

private theorem bitvec_rotateLeft_zero {w : Nat} (x : BitVec w) : x.rotateLeft 0 = x := by
  ext i hi
  have hw : 0 < w := by omega
  rw [BitVec.getElem_rotateLeft (by omega)]
  split <;> rename_i h
  · simp at h
  · congr 1

private theorem bitvec_rotateRight_zero {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  ext i hi
  have hw : 0 < w := by omega
  rw [BitVec.getElem_rotateRight (by omega)]
  split <;> rename_i h
  · congr 1
    simp
  · simp at h; omega

private theorem ofNat_toBitVec32 (x : UInt32) : BitVec.ofNat 32 x.toNat = x.toBitVec := by simp
private theorem ofBitVec_eq32 (b : BitVec 32) : UInt32.ofNat b.toNat = UInt32.ofBitVec b := by simp
private theorem ofNat_toBitVec64 (x : UInt64) : BitVec.ofNat 64 x.toNat = x.toBitVec := by simp
private theorem ofBitVec_eq64 (b : BitVec 64) : UInt64.ofNat b.toNat = UInt64.ofBitVec b := by simp

theorem rotl32_eq (x : UInt32) (n : Nat) :
    rotl32 x n = UInt32.ofBitVec (x.toBitVec.rotateLeft (n % 32)) := by
  simp only [rotl32, ofNat_toBitVec32, ofBitVec_eq32]
theorem rotr32_eq (x : UInt32) (n : Nat) :
    rotr32 x n = UInt32.ofBitVec (x.toBitVec.rotateRight (n % 32)) := by
  simp only [rotr32, ofNat_toBitVec32, ofBitVec_eq32]
theorem rotl64_eq (x : UInt64) (n : Nat) :
    rotl64 x n = UInt64.ofBitVec (x.toBitVec.rotateLeft (n % 64)) := by
  simp only [rotl64, ofNat_toBitVec64, ofBitVec_eq64]
theorem rotr64_eq (x : UInt64) (n : Nat) :
    rotr64 x n = UInt64.ofBitVec (x.toBitVec.rotateRight (n % 64)) := by
  simp only [rotr64, ofNat_toBitVec64, ofBitVec_eq64]

theorem rotr32_rotl32 (x : UInt32) (n : Nat) : rotr32 (rotl32 x n) n = x := by
  rw [rotl32_eq, rotr32_eq]
  have h : (UInt32.ofBitVec (x.toBitVec.rotateLeft (n % 32))).toBitVec
      = x.toBitVec.rotateLeft (n % 32) := by simp
  rw [h, bitvec_rotateRight_rotateLeft]

theorem rotl32_rotr32 (x : UInt32) (n : Nat) : rotl32 (rotr32 x n) n = x := by
  rw [rotl32_eq, rotr32_eq]
  have h : (UInt32.ofBitVec (x.toBitVec.rotateRight (n % 32))).toBitVec
      = x.toBitVec.rotateRight (n % 32) := by simp
  rw [h, bitvec_rotateLeft_rotateRight]

theorem rotr64_rotl64 (x : UInt64) (n : Nat) : rotr64 (rotl64 x n) n = x := by
  rw [rotl64_eq, rotr64_eq]
  have h : (UInt64.ofBitVec (x.toBitVec.rotateLeft (n % 64))).toBitVec
      = x.toBitVec.rotateLeft (n % 64) := by simp
  rw [h, bitvec_rotateRight_rotateLeft]

theorem rotl64_rotr64 (x : UInt64) (n : Nat) : rotl64 (rotr64 x n) n = x := by
  rw [rotl64_eq, rotr64_eq]
  have h : (UInt64.ofBitVec (x.toBitVec.rotateRight (n % 64))).toBitVec
      = x.toBitVec.rotateRight (n % 64) := by simp
  rw [h, bitvec_rotateLeft_rotateRight]

theorem rotl32_zero (x : UInt32) : rotl32 x 0 = x := by
  rw [rotl32_eq]; simp only [Nat.zero_mod, bitvec_rotateLeft_zero]
theorem rotr32_zero (x : UInt32) : rotr32 x 0 = x := by
  rw [rotr32_eq]; simp only [Nat.zero_mod, bitvec_rotateRight_zero]
theorem rotl64_zero (x : UInt64) : rotl64 x 0 = x := by
  rw [rotl64_eq]; simp only [Nat.zero_mod, bitvec_rotateLeft_zero]
theorem rotr64_zero (x : UInt64) : rotr64 x 0 = x := by
  rw [rotr64_eq]; simp only [Nat.zero_mod, bitvec_rotateRight_zero]

theorem rotl32_mod (x : UInt32) (n : Nat) : rotl32 x (n % 32) = rotl32 x n := by
  simp only [rotl32_eq, Nat.mod_mod]
theorem rotl64_mod (x : UInt64) (n : Nat) : rotl64 x (n % 64) = rotl64 x n := by
  simp only [rotl64_eq, Nat.mod_mod]

/-! ### 64-bit round-trips

`toBytesBE64` / `ofBytesBE64` are the conversions `Silmaril.Crypto.SHA512`
parses and emits with.
-/

set_option maxHeartbeats 1200000 in
theorem ofBytesBE64_toBytesBE64 (x : UInt64) :
    ofBytesBE64 (toBytesBE64 x).1 (toBytesBE64 x).2.1 (toBytesBE64 x).2.2.1
      (toBytesBE64 x).2.2.2.1 (toBytesBE64 x).2.2.2.2.1 (toBytesBE64 x).2.2.2.2.2.1
      (toBytesBE64 x).2.2.2.2.2.2.1 (toBytesBE64 x).2.2.2.2.2.2.2 = x := by
  apply uint64_eq_of_toNat_eq
  dsimp [toBytesBE64, ofBytesBE64]
  simp [UInt64.toNat_ofNat]
  have hx := uint64_lt_256p8 x
  omega

set_option maxHeartbeats 1200000 in
theorem toBytesBE64_ofBytesBE64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    toBytesBE64 (ofBytesBE64 b0 b1 b2 b3 b4 b5 b6 b7) = (b0, b1, b2, b3, b4, b5, b6, b7) := by
  have h0 := uint8_lt_256 b0
  have h1 := uint8_lt_256 b1
  have h2 := uint8_lt_256 b2
  have h3 := uint8_lt_256 b3
  have h4 := uint8_lt_256 b4
  have h5 := uint8_lt_256 b5
  have h6 := uint8_lt_256 b6
  have h7 := uint8_lt_256 b7
  dsimp [toBytesBE64, ofBytesBE64]
  simp [UInt64.toNat_ofNat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply uint8_eq_of_toNat_eq; simp; omega)

set_option maxHeartbeats 1200000 in
theorem ofBytesLE64_toBytesLE64 (x : UInt64) :
    ofBytesLE64 (toBytesLE64 x).1 (toBytesLE64 x).2.1 (toBytesLE64 x).2.2.1
      (toBytesLE64 x).2.2.2.1 (toBytesLE64 x).2.2.2.2.1 (toBytesLE64 x).2.2.2.2.2.1
      (toBytesLE64 x).2.2.2.2.2.2.1 (toBytesLE64 x).2.2.2.2.2.2.2 = x := by
  apply uint64_eq_of_toNat_eq
  dsimp [toBytesLE64, ofBytesLE64]
  simp [UInt64.toNat_ofNat]
  have hx := uint64_lt_256p8 x
  omega

set_option maxHeartbeats 1200000 in
theorem toBytesLE64_ofBytesLE64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    toBytesLE64 (ofBytesLE64 b0 b1 b2 b3 b4 b5 b6 b7) = (b0, b1, b2, b3, b4, b5, b6, b7) := by
  have h0 := uint8_lt_256 b0
  have h1 := uint8_lt_256 b1
  have h2 := uint8_lt_256 b2
  have h3 := uint8_lt_256 b3
  have h4 := uint8_lt_256 b4
  have h5 := uint8_lt_256 b5
  have h6 := uint8_lt_256 b6
  have h7 := uint8_lt_256 b7
  dsimp [toBytesLE64, ofBytesLE64]
  simp [UInt64.toNat_ofNat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply uint8_eq_of_toNat_eq; simp; omega)

end Silmaril.Crypto

namespace Silmaril.Crypto.Word

open Silmaril.Crypto

/-! These three used to be independent re-implementations of `rotr32`,
`ofBytesLE32` and `toBytesLE32` with no theorem relating them, so a fix applied
to one was silently not applied to the other.  They are now definitions in terms
of the canonical ones; the `*_eq_*` theorems below record that. -/

/-- Right-rotate a 32-bit word by `r` bits (BLAKE3 spelling of `rotr32`). -/
def rotateRight (x : UInt32) (r : Fin 32) : UInt32 := rotr32 x r.val

/-- Pack four little-endian bytes into a 32-bit word. -/
def pack32LE (b0 b1 b2 b3 : UInt8) : UInt32 := ofBytesLE32 b0 b1 b2 b3

/-- Unpack a 32-bit word into four little-endian bytes. -/
def unpack32LE (w : UInt32) : UInt8 × UInt8 × UInt8 × UInt8 := toBytesLE32 w

theorem rotateRight_eq_rotr32 (x : UInt32) (r : Fin 32) : rotateRight x r = rotr32 x r.val := rfl

theorem pack32LE_eq_ofBytesLE32 (b0 b1 b2 b3 : UInt8) :
    pack32LE b0 b1 b2 b3 = ofBytesLE32 b0 b1 b2 b3 := rfl

theorem unpack32LE_eq_toBytesLE32 (w : UInt32) : unpack32LE w = toBytesLE32 w := rfl

/-- Packing and unpacking are mutually inverse. -/
theorem pack32LE_unpack32LE (w : UInt32) :
    pack32LE (unpack32LE w).1 (unpack32LE w).2.1 (unpack32LE w).2.2.1 (unpack32LE w).2.2.2 = w :=
  ofBytesLE32_toBytesLE32 w

/-- Unpacking and packing are mutually inverse. -/
theorem unpack32LE_pack32LE (b0 b1 b2 b3 : UInt8) :
    unpack32LE (pack32LE b0 b1 b2 b3) = (b0, b1, b2, b3) :=
  toBytesLE32_ofBytesLE32 b0 b1 b2 b3

/-- XOR two 32-bit words. -/
def xor32 (a b : UInt32) : UInt32 := a ^^^ b

/-- XOR four 32-bit words. -/
def xor4 (a b c d : UInt32) : UInt32 := a ^^^ b ^^^ c ^^^ d

/-- XOR is commutative. -/
theorem xor32_comm (a b : UInt32) : xor32 a b = xor32 b a := by
  simp [xor32, UInt32.xor_comm]

/-- XOR is associative. -/
theorem xor32_assoc (a b c : UInt32) : xor32 a (xor32 b c) = xor32 (xor32 a b) c := by
  simp [xor32, UInt32.xor_assoc]

/-- XOR with zero is identity. -/
theorem xor32_zero (a : UInt32) : xor32 a 0 = a := by
  simp [xor32, UInt32.xor_zero]

/-- XOR is self-inverse. -/
theorem xor32_self (a : UInt32) : xor32 a a = 0 := by
  simp [xor32, UInt32.xor_self]

end Silmaril.Crypto.Word
