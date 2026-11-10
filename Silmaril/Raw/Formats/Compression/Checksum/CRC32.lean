module

public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Bits.Bit

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Checksum.CRC32`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

set_option maxRecDepth 20000000

/-! ### Published check values

`String.toUTF8` does not reduce inside a `module`, so the vectors are spelled as
the ASCII bytes of the string, with the string given in the docstring. -/

/-- CRC32 of empty input is 0. -/
theorem crc32_empty : crc32 ByteArray.empty = 0 := by decide

/-- RFC 1952 §8 check value: the CRC-32 of the nine ASCII bytes of `"123456789"`
is `0xCBF43926`. -/
theorem crc32_check :
    crc32 (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) = 0xCBF43926 := by
  decide

/-- Published check value: the CRC-32 of `"a"` is `0xE8B7BE43`. -/
theorem crc32_check_a : crc32 (ByteArray.mk #[0x61]) = 0xE8B7BE43 := by decide

/-- Published check value: the CRC-32 of `"abc"` is `0x352441C2`. -/
theorem crc32_check_abc : crc32 (ByteArray.mk #[0x61, 0x62, 0x63]) = 0x352441C2 := by decide

/-- Published check value: the CRC-32 of
`"The quick brown fox jumps over the lazy dog"` is `0x414FA339`. -/
theorem crc32_check_fox :
    crc32 (ByteArray.mk #[0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x20, 0x62, 0x72,
      0x6F, 0x77, 0x6E, 0x20, 0x66, 0x6F, 0x78, 0x20, 0x6A, 0x75, 0x6D, 0x70, 0x73, 0x20, 0x6F,
      0x76, 0x65, 0x72, 0x20, 0x74, 0x68, 0x65, 0x20, 0x6C, 0x61, 0x7A, 0x79, 0x20, 0x64, 0x6F,
      0x67]) = 0x414FA339 := by
  decide

/-! ### Incremental update -/

theorem crc32_xor_cancel (x : Nat) : x ^^^ 0xFFFFFFFF ^^^ 0xFFFFFFFF = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- `crc32List` is the complement of the running register. -/
theorem crc32List_eq_state (data : List Nat) : crc32List data = crc32State data ^^^ 0xFFFFFFFF :=
  rfl

/-- The running register of a concatenation resumes the register of the prefix. -/
theorem crc32State_append (a b : List Nat) :
    crc32State (a ++ b) = b.foldl crc32Byte (crc32State a) := by
  simp [crc32State, List.foldl_append]

/-- Incremental-update law: the CRC-32 of `a ++ b` is obtained from the CRC-32 of
`a` by complementing it back into a register, absorbing `b`, and complementing
again. In particular `crc32List (a ++ b)` is a function of `crc32List a` and `b`. -/
theorem crc32List_append (a b : List Nat) :
    crc32List (a ++ b) = b.foldl crc32Byte (crc32List a ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF := by
  rw [crc32List_eq_state, crc32List_eq_state, crc32State_append, crc32_xor_cancel]

/-- Appending nothing changes nothing (sanity check on `crc32List_append`). -/
theorem crc32List_append_nil (a : List Nat) :
    crc32List (a ++ []) = crc32List a := by
  rw [crc32List_append]; simp [crc32_xor_cancel]

/-! ### Range -/

theorem crc32Byte_go_lt (c k : Nat) (hc : c < 2 ^ 32) : crc32Byte.go c k < 2 ^ 32 := by
  induction k generalizing c with
  | zero => simpa [crc32Byte.go] using hc
  | succ k ih =>
    rw [crc32Byte.go]
    split
    · exact ih _ (by omega)
    · exact ih _ (Nat.xor_lt_two_pow (by omega) (by decide))

/-- The CRC-32 round function keeps the register below `2 ^ 32`, provided the
byte really is a byte. -/
theorem crc32Byte_lt (c b : Nat) (hc : c < 2 ^ 32) (hb : b < 256) : crc32Byte c b < 2 ^ 32 :=
  crc32Byte_go_lt _ _ (Nat.xor_lt_two_pow hc (by omega))

/-- `crc32List` of a list of genuine bytes is a 32-bit value, so the `UInt32.ofNat`
in `crc32` does not truncate. -/
theorem crc32List_lt (data : List Nat) (h : ∀ b ∈ data, b < 256) : crc32List data < 2 ^ 32 := by
  have hfold : ∀ (l : List Nat) (c : Nat), c < 2 ^ 32 → (∀ b ∈ l, b < 256) →
      l.foldl crc32Byte c < 2 ^ 32 := by
    intro l
    induction l with
    | nil => intro c hc _; simpa using hc
    | cons x xs ih =>
      intro c hc hb
      exact ih _ (crc32Byte_lt c x hc (hb x (by simp))) (fun b hbm => hb b (by simp [hbm]))
  exact Nat.xor_lt_two_pow (hfold data _ (by decide) h) (by decide)

end Silmaril.Formats.Compression
