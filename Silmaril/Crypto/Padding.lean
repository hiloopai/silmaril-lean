module

public import Mathlib.Tactic

/-!
# Merkle–Damgård length-strengthening padding

Implements the classic MD-strengthening padding for various block sizes: append
a single `1` bit (the byte `0x80`, since this API is byte-granular), then the
minimal run of zero bytes, then the message length in bits.

- `paddingMD`: 64-byte blocks with 64-bit big-endian length (SHA-1, SHA-256)
- `paddingMD_LE`: 64-byte blocks with 64-bit little-endian length (MD5, RFC 1321 §3.1)
- `paddingSHA512`: 128-byte blocks with 128-bit big-endian length (SHA-512, SHA-384)

This padding is **injective** (equivalently: suffix-free on the final block),
which is what the trailing length field buys.  It is *not* prefix-free —
`paddingMD_not_prefix_free` exhibits the counterexample — so do not rely on
prefix-freeness for a security argument.

References:
- RFC 1321 §3.1 (MD5)
- FIPS 180-4 §5.1.1 (SHA-1, SHA-256: 512-bit blocks)
- FIPS 180-4 §5.1.2 (SHA-384, SHA-512: 1024-bit blocks)

## Theorems

- `natToBytesBE64_injective`, `natToBytesLE64_injective`, `natToBytesBE128_injective`:
  the length encodings are injective below their respective wrap-around points.
- `paddingMD_block_multiple`, `paddingMD_LE_block_multiple`,
  `paddingSHA512_block_multiple`: padded length is a multiple of the block size.
- `paddingMD_prefix`, `paddingMD_LE_prefix`, `paddingSHA512_prefix`: the original
  message is a prefix of its padding.
- `paddingMD_injective`, `paddingMD_LE_injective`, `paddingSHA512_injective`:
  injectivity, with no hypothesis beyond representability of the bit length.
- `paddingMD_not_prefix_free`: MD-strengthening is not prefix-free.
-/

@[expose] public section

namespace Silmaril.Crypto

def padFirstByte : UInt8 := 0x80
def padZero : UInt8 := 0x00

/-- 64-bit big-endian length encoding. -/
def natToBytesBE64 (lenBits : Nat) : List UInt8 :=
  let v := lenBits % (2 ^ 64)
  [UInt8.ofNat (v / 256 ^ 7),
   UInt8.ofNat ((v / 256 ^ 6) % 256),
   UInt8.ofNat ((v / 256 ^ 5) % 256),
   UInt8.ofNat ((v / 256 ^ 4) % 256),
   UInt8.ofNat ((v / 256 ^ 3) % 256),
   UInt8.ofNat ((v / 256 ^ 2) % 256),
   UInt8.ofNat ((v / 256) % 256),
   UInt8.ofNat (v % 256)]

/-- 64-bit little-endian length encoding (MD5). -/
def natToBytesLE64 (lenBits : Nat) : List UInt8 :=
  let v := lenBits % (2 ^ 64)
  [UInt8.ofNat (v % 256),
   UInt8.ofNat ((v / 256) % 256),
   UInt8.ofNat ((v / 256 ^ 2) % 256),
   UInt8.ofNat ((v / 256 ^ 3) % 256),
   UInt8.ofNat ((v / 256 ^ 4) % 256),
   UInt8.ofNat ((v / 256 ^ 5) % 256),
   UInt8.ofNat ((v / 256 ^ 6) % 256),
   UInt8.ofNat (v / 256 ^ 7)]

/-- 128-bit big-endian length encoding (SHA-512). -/
def natToBytesBE128 (lenBits : Nat) : List UInt8 :=
  let v := lenBits % (2 ^ 128)
  [UInt8.ofNat (v / 256 ^ 15),
   UInt8.ofNat ((v / 256 ^ 14) % 256),
   UInt8.ofNat ((v / 256 ^ 13) % 256),
   UInt8.ofNat ((v / 256 ^ 12) % 256),
   UInt8.ofNat ((v / 256 ^ 11) % 256),
   UInt8.ofNat ((v / 256 ^ 10) % 256),
   UInt8.ofNat ((v / 256 ^ 9) % 256),
   UInt8.ofNat ((v / 256 ^ 8) % 256),
   UInt8.ofNat ((v / 256 ^ 7) % 256),
   UInt8.ofNat ((v / 256 ^ 6) % 256),
   UInt8.ofNat ((v / 256 ^ 5) % 256),
   UInt8.ofNat ((v / 256 ^ 4) % 256),
   UInt8.ofNat ((v / 256 ^ 3) % 256),
   UInt8.ofNat ((v / 256 ^ 2) % 256),
   UInt8.ofNat ((v / 256) % 256),
   UInt8.ofNat (v % 256)]

@[simp] theorem natToBytesBE64_length (n : Nat) : (natToBytesBE64 n).length = 8 := rfl
@[simp] theorem natToBytesLE64_length (n : Nat) : (natToBytesLE64 n).length = 8 := rfl
@[simp] theorem natToBytesBE128_length (n : Nat) : (natToBytesBE128 n).length = 16 := rfl

/-! ### Injectivity of the length encodings

The point of Merkle–Damgård strengthening is the trailing length field.  These
lemmas are what makes the padding injective *without* assuming the two messages
have the same length; everything below depends on them.
-/

private theorem uint8_ofNat_inj_mod {x y : Nat} (h : UInt8.ofNat x = UInt8.ofNat y) :
    x % 256 = y % 256 := by
  have := congrArg UInt8.toNat h
  simpa [UInt8.toNat_ofNat] using this

private theorem uint8_mod_inj {x y : Nat}
    (h : UInt8.ofNat (x % 256) = UInt8.ofNat (y % 256)) : x % 256 = y % 256 := by
  have := uint8_ofNat_inj_mod h
  simpa using this

/-- One digit of the big-endian expansion: knowing the quotient by `m * 256`
and the digit at weight `m` determines the quotient by `m`. -/
private theorem byte_chain {a b m m' : Nat} (hm : m * 256 = m')
    (hhi : a / m' = b / m') (hlo : a / m % 256 = b / m % 256) : a / m = b / m := by
  subst hm
  have e1 : a / m / 256 = a / (m * 256) := Nat.div_div_eq_div_mul ..
  have e2 : b / m / 256 = b / (m * 256) := Nat.div_div_eq_div_mul ..
  omega

private theorem byte_last {a b : Nat} (hhi : a / 256 = b / 256) (hlo : a % 256 = b % 256) :
    a = b := by omega

private theorem byte_top64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a / 256 ^ 7 % 256 = b / 256 ^ 7 % 256) : a / 256 ^ 7 = b / 256 ^ 7 := by omega

private theorem byte_top128 {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : a / 256 ^ 15 % 256 = b / 256 ^ 15 % 256) : a / 256 ^ 15 = b / 256 ^ 15 := by omega

/-- The 64-bit big-endian length encoding is injective below `2 ^ 64`. -/
theorem natToBytesBE64_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : natToBytesBE64 a = natToBytesBE64 b) : a = b := by
  simp only [natToBytesBE64, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  replace h1 := uint8_mod_inj h1
  replace h2 := uint8_mod_inj h2
  replace h3 := uint8_mod_inj h3
  replace h4 := uint8_mod_inj h4
  replace h5 := uint8_mod_inj h5
  replace h6 := uint8_mod_inj h6
  replace h7 := uint8_mod_inj h7
  have t7 := byte_top64 ha hb (uint8_ofNat_inj_mod h0)
  have t6 := byte_chain (m := 256 ^ 6) (m' := 256 ^ 7) (by norm_num) t7 h1
  have t5 := byte_chain (m := 256 ^ 5) (m' := 256 ^ 6) (by norm_num) t6 h2
  have t4 := byte_chain (m := 256 ^ 4) (m' := 256 ^ 5) (by norm_num) t5 h3
  have t3 := byte_chain (m := 256 ^ 3) (m' := 256 ^ 4) (by norm_num) t4 h4
  have t2 := byte_chain (m := 256 ^ 2) (m' := 256 ^ 3) (by norm_num) t3 h5
  have t1 := byte_chain (m := 256) (m' := 256 ^ 2) (by norm_num) t2 h6
  exact byte_last t1 h7

/-- The 64-bit little-endian length encoding is injective below `2 ^ 64`. -/
theorem natToBytesLE64_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : natToBytesLE64 a = natToBytesLE64 b) : a = b := by
  simp only [natToBytesLE64, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  replace h0 := uint8_mod_inj h0
  replace h1 := uint8_mod_inj h1
  replace h2 := uint8_mod_inj h2
  replace h3 := uint8_mod_inj h3
  replace h4 := uint8_mod_inj h4
  replace h5 := uint8_mod_inj h5
  replace h6 := uint8_mod_inj h6
  have t7 := byte_top64 ha hb (uint8_ofNat_inj_mod h7)
  have t6 := byte_chain (m := 256 ^ 6) (m' := 256 ^ 7) (by norm_num) t7 h6
  have t5 := byte_chain (m := 256 ^ 5) (m' := 256 ^ 6) (by norm_num) t6 h5
  have t4 := byte_chain (m := 256 ^ 4) (m' := 256 ^ 5) (by norm_num) t5 h4
  have t3 := byte_chain (m := 256 ^ 3) (m' := 256 ^ 4) (by norm_num) t4 h3
  have t2 := byte_chain (m := 256 ^ 2) (m' := 256 ^ 3) (by norm_num) t3 h2
  have t1 := byte_chain (m := 256) (m' := 256 ^ 2) (by norm_num) t2 h1
  exact byte_last t1 h0

/-- The 128-bit big-endian length encoding is injective below `2 ^ 128`. -/
theorem natToBytesBE128_injective {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : natToBytesBE128 a = natToBytesBE128 b) : a = b := by
  simp only [natToBytesBE128, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  replace h1 := uint8_mod_inj h1
  replace h2 := uint8_mod_inj h2
  replace h3 := uint8_mod_inj h3
  replace h4 := uint8_mod_inj h4
  replace h5 := uint8_mod_inj h5
  replace h6 := uint8_mod_inj h6
  replace h7 := uint8_mod_inj h7
  replace h8 := uint8_mod_inj h8
  replace h9 := uint8_mod_inj h9
  replace h10 := uint8_mod_inj h10
  replace h11 := uint8_mod_inj h11
  replace h12 := uint8_mod_inj h12
  replace h13 := uint8_mod_inj h13
  replace h14 := uint8_mod_inj h14
  replace h15 := uint8_mod_inj h15
  have t15 := byte_top128 ha hb (uint8_ofNat_inj_mod h0)
  have t14 := byte_chain (m := 256 ^ 14) (m' := 256 ^ 15) (by norm_num) t15 h1
  have t13 := byte_chain (m := 256 ^ 13) (m' := 256 ^ 14) (by norm_num) t14 h2
  have t12 := byte_chain (m := 256 ^ 12) (m' := 256 ^ 13) (by norm_num) t13 h3
  have t11 := byte_chain (m := 256 ^ 11) (m' := 256 ^ 12) (by norm_num) t12 h4
  have t10 := byte_chain (m := 256 ^ 10) (m' := 256 ^ 11) (by norm_num) t11 h5
  have t9 := byte_chain (m := 256 ^ 9) (m' := 256 ^ 10) (by norm_num) t10 h6
  have t8 := byte_chain (m := 256 ^ 8) (m' := 256 ^ 9) (by norm_num) t9 h7
  have t7 := byte_chain (m := 256 ^ 7) (m' := 256 ^ 8) (by norm_num) t8 h8
  have t6 := byte_chain (m := 256 ^ 6) (m' := 256 ^ 7) (by norm_num) t7 h9
  have t5 := byte_chain (m := 256 ^ 5) (m' := 256 ^ 6) (by norm_num) t6 h10
  have t4 := byte_chain (m := 256 ^ 4) (m' := 256 ^ 5) (by norm_num) t5 h11
  have t3 := byte_chain (m := 256 ^ 3) (m' := 256 ^ 4) (by norm_num) t4 h12
  have t2 := byte_chain (m := 256 ^ 2) (m' := 256 ^ 3) (by norm_num) t3 h13
  have t1 := byte_chain (m := 256) (m' := 256 ^ 2) (by norm_num) t2 h14
  exact byte_last t1 h15

/-! ### The padding functions -/

/-- Number of zero bytes between the `0x80` byte and the 8-byte length field,
for 64-byte blocks.  Used by both the big-endian (SHA-1, SHA-256) and the
little-endian (MD5) variants. -/
def paddingZeroCount (msgLenBytes : Nat) : Nat :=
  let r := msgLenBytes % 64
  if r < 56 then 55 - r else 119 - r

/-- Number of zero bytes between the `0x80` byte and the 16-byte length field,
for 128-byte blocks (SHA-384, SHA-512). -/
def paddingZeroCountSHA512 (msgLenBytes : Nat) : Nat :=
  let r := msgLenBytes % 128
  if r < 112 then 111 - r else 239 - r

/-- Padding for 64-byte block algorithms with big-endian length (SHA-1, SHA-256). -/
def paddingMD (msg : List UInt8) : List UInt8 :=
  let lenBits := msg.length * 8
  let zeros := List.replicate (paddingZeroCount msg.length) padZero
  let lengthBytes := natToBytesBE64 lenBits
  msg ++ [padFirstByte] ++ zeros ++ lengthBytes

/-- Padding for 64-byte block algorithms with little-endian length (MD5). -/
def paddingMD_LE (msg : List UInt8) : List UInt8 :=
  let lenBits := msg.length * 8
  let zeros := List.replicate (paddingZeroCount msg.length) padZero
  let lengthBytes := natToBytesLE64 lenBits
  msg ++ [padFirstByte] ++ zeros ++ lengthBytes

/-- Padding for 128-byte block algorithms (SHA-512, SHA-384). -/
def paddingSHA512 (msg : List UInt8) : List UInt8 :=
  let lenBits := msg.length * 8
  let zeros := List.replicate (paddingZeroCountSHA512 msg.length) padZero
  let lengthBytes := natToBytesBE128 lenBits
  msg ++ [padFirstByte] ++ zeros ++ lengthBytes

/-! ### Block-multiple lemmas -/

/-- The padded length is always a multiple of 64. -/
theorem paddingMD_block_multiple (msg : List UInt8) : 64 ∣ (paddingMD msg).length := by
  dsimp [paddingMD, paddingZeroCount]
  by_cases h : msg.length % 64 < 56
  · simp [h]
    omega
  · simp [h]
    omega

/-- The MD5 padded length is always a multiple of 64. -/
theorem paddingMD_LE_block_multiple (msg : List UInt8) : 64 ∣ (paddingMD_LE msg).length := by
  dsimp [paddingMD_LE, paddingZeroCount]
  by_cases h : msg.length % 64 < 56
  · simp [h]
    omega
  · simp [h]
    omega

/-- The SHA-512 padded length is always a multiple of 128. -/
theorem paddingSHA512_block_multiple (msg : List UInt8) : 128 ∣ (paddingSHA512 msg).length := by
  dsimp [paddingSHA512, paddingZeroCountSHA512]
  by_cases h : msg.length % 128 < 112
  · simp [h]; omega
  · simp [h]; omega

/-! ### Prefix lemmas -/

/-- Padding always extends the original message (msg is a prefix). -/
theorem paddingMD_prefix (msg : List UInt8) : msg <+: paddingMD msg := by
  dsimp [paddingMD]; simp

/-- Padding always extends the original message (msg is a prefix). -/
theorem paddingMD_LE_prefix (msg : List UInt8) : msg <+: paddingMD_LE msg := by
  dsimp [paddingMD_LE]; simp

/-- Padding always extends the original message (msg is a prefix). -/
theorem paddingSHA512_prefix (msg : List UInt8) : msg <+: paddingSHA512 msg := by
  dsimp [paddingSHA512]; simp

/-! ### Injectivity

These are the real Merkle–Damgård strengthening statements: no `msg1.length =
msg2.length` hypothesis, only the representability bound that FIPS 180-4 §5.1
itself imposes (`ℓ < 2 ^ 64` resp. `ℓ < 2 ^ 128`).
-/

/-- The last 8 bytes of `paddingMD msg` are the big-endian bit length. -/
private theorem paddingMD_tail (msg : List UInt8) :
    (paddingMD msg).reverse.take 8 = (natToBytesBE64 (msg.length * 8)).reverse := by
  dsimp only [paddingMD]
  rw [List.reverse_append]
  exact List.take_left' (by simp)

/-- The last 8 bytes of `paddingMD_LE msg` are the little-endian bit length. -/
private theorem paddingMD_LE_tail (msg : List UInt8) :
    (paddingMD_LE msg).reverse.take 8 = (natToBytesLE64 (msg.length * 8)).reverse := by
  dsimp only [paddingMD_LE]
  rw [List.reverse_append]
  exact List.take_left' (by simp)

/-- The last 16 bytes of `paddingSHA512 msg` are the big-endian bit length. -/
private theorem paddingSHA512_tail (msg : List UInt8) :
    (paddingSHA512 msg).reverse.take 16 = (natToBytesBE128 (msg.length * 8)).reverse := by
  dsimp only [paddingSHA512]
  rw [List.reverse_append]
  exact List.take_left' (by simp)

/-- MD-strengthening with a 64-bit big-endian length is injective on messages
whose bit length is representable (FIPS 180-4 §5.1.1: `ℓ < 2 ^ 64`). -/
theorem paddingMD_injective {msg1 msg2 : List UInt8}
    (hb1 : msg1.length * 8 < 2 ^ 64) (hb2 : msg2.length * 8 < 2 ^ 64)
    (hp : paddingMD msg1 = paddingMD msg2) : msg1 = msg2 := by
  have henc : natToBytesBE64 (msg1.length * 8) = natToBytesBE64 (msg2.length * 8) := by
    have h := congrArg (fun l : List UInt8 => l.reverse.take 8) hp
    rw [paddingMD_tail, paddingMD_tail] at h
    simpa using congrArg List.reverse h
  have h_len : msg1.length = msg2.length := by
    have := natToBytesBE64_injective hb1 hb2 henc
    omega
  have h_take : (paddingMD msg1).take msg1.length = (paddingMD msg2).take msg1.length := by
    rw [hp]
  dsimp only [paddingMD] at h_take
  simpa [h_len] using h_take

/-- MD-strengthening with a 64-bit little-endian length (MD5, RFC 1321 §3.1) is
injective on messages whose bit length is representable. -/
theorem paddingMD_LE_injective {msg1 msg2 : List UInt8}
    (hb1 : msg1.length * 8 < 2 ^ 64) (hb2 : msg2.length * 8 < 2 ^ 64)
    (hp : paddingMD_LE msg1 = paddingMD_LE msg2) : msg1 = msg2 := by
  have henc : natToBytesLE64 (msg1.length * 8) = natToBytesLE64 (msg2.length * 8) := by
    have h := congrArg (fun l : List UInt8 => l.reverse.take 8) hp
    rw [paddingMD_LE_tail, paddingMD_LE_tail] at h
    simpa using congrArg List.reverse h
  have h_len : msg1.length = msg2.length := by
    have := natToBytesLE64_injective hb1 hb2 henc
    omega
  have h_take : (paddingMD_LE msg1).take msg1.length = (paddingMD_LE msg2).take msg1.length := by
    rw [hp]
  dsimp only [paddingMD_LE] at h_take
  simpa [h_len] using h_take

/-- MD-strengthening with a 128-bit big-endian length (FIPS 180-4 §5.1.2) is
injective on messages whose bit length is representable (`ℓ < 2 ^ 128`). -/
theorem paddingSHA512_injective {msg1 msg2 : List UInt8}
    (hb1 : msg1.length * 8 < 2 ^ 128) (hb2 : msg2.length * 8 < 2 ^ 128)
    (hp : paddingSHA512 msg1 = paddingSHA512 msg2) : msg1 = msg2 := by
  have henc : natToBytesBE128 (msg1.length * 8) = natToBytesBE128 (msg2.length * 8) := by
    have h := congrArg (fun l : List UInt8 => l.reverse.take 16) hp
    rw [paddingSHA512_tail, paddingSHA512_tail] at h
    simpa using congrArg List.reverse h
  have h_len : msg1.length = msg2.length := by
    have := natToBytesBE128_injective hb1 hb2 henc
    omega
  have h_take : (paddingSHA512 msg1).take msg1.length = (paddingSHA512 msg2).take msg1.length := by
    rw [hp]
  dsimp only [paddingSHA512] at h_take
  simpa [h_len] using h_take

/-! ### What this padding is *not*

The module used to be titled "prefix-free padding".  Length-suffix
MD-strengthening is not prefix-free: padding the padded empty message
reproduces `paddingMD []` as its own first block. -/

/-- MD-strengthening is **not** prefix-free. -/
theorem paddingMD_not_prefix_free :
    paddingMD [] <+: paddingMD (paddingMD []) ∧ paddingMD [] ≠ paddingMD (paddingMD []) := by
  constructor
  · decide
  · decide

/-- SHA-512's MD-strengthening is **not** prefix-free either. -/
theorem paddingSHA512_not_prefix_free :
    paddingSHA512 [] <+: paddingSHA512 (paddingSHA512 [])
      ∧ paddingSHA512 [] ≠ paddingSHA512 (paddingSHA512 []) := by
  constructor
  · decide
  · decide

end Silmaril.Crypto
