module

public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Bits.Bit

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Bits.ByteFields`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

theorem toNat_ofNat_mod (n : Nat) : (UInt8.ofNat (n % 256)).toNat = n % 256 :=
  UInt8.toNat_ofNat_of_lt' (by rw [show UInt8.size = 256 from rfl]; omega)

theorem le32Val_le32Bytes (n : Nat) :
    le32Val (UInt8.ofNat (n % 256)) (UInt8.ofNat (n / 256 % 256))
      (UInt8.ofNat (n / 65536 % 256)) (UInt8.ofNat (n / 16777216 % 256)) = n % 4294967296 := by
  simp only [le32Val, toNat_ofNat_mod]
  omega

theorem be32Val_be32Bytes (n : Nat) :
    be32Val (UInt8.ofNat (n / 16777216 % 256)) (UInt8.ofNat (n / 65536 % 256))
      (UInt8.ofNat (n / 256 % 256)) (UInt8.ofNat (n % 256)) = n % 4294967296 := by
  simp only [be32Val, toNat_ofNat_mod]
  omega

theorem le32Bytes_le32Val (b0 b1 b2 b3 : UInt8) :
    le32Bytes (le32Val b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  have h1 : b1.toNat < 256 := b1.toNat_lt
  have h2 : b2.toNat < 256 := b2.toNat_lt
  have h3 : b3.toNat < 256 := b3.toNat_lt
  have e0 : le32Val b0 b1 b2 b3 % 256 = b0.toNat := by simp only [le32Val]; omega
  have e1 : le32Val b0 b1 b2 b3 / 256 % 256 = b1.toNat := by simp only [le32Val]; omega
  have e2 : le32Val b0 b1 b2 b3 / 65536 % 256 = b2.toNat := by simp only [le32Val]; omega
  have e3 : le32Val b0 b1 b2 b3 / 16777216 % 256 = b3.toNat := by simp only [le32Val]; omega
  simp only [le32Bytes, e0, e1, e2, e3, UInt8.ofNat_toNat]

theorem be32Bytes_be32Val (b0 b1 b2 b3 : UInt8) :
    be32Bytes (be32Val b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  have h1 : b1.toNat < 256 := b1.toNat_lt
  have h2 : b2.toNat < 256 := b2.toNat_lt
  have h3 : b3.toNat < 256 := b3.toNat_lt
  have e0 : be32Val b0 b1 b2 b3 / 16777216 % 256 = b0.toNat := by simp only [be32Val]; omega
  have e1 : be32Val b0 b1 b2 b3 / 65536 % 256 = b1.toNat := by simp only [be32Val]; omega
  have e2 : be32Val b0 b1 b2 b3 / 256 % 256 = b2.toNat := by simp only [be32Val]; omega
  have e3 : be32Val b0 b1 b2 b3 % 256 = b3.toNat := by simp only [be32Val]; omega
  simp only [be32Bytes, e0, e1, e2, e3, UInt8.ofNat_toNat]

/-- Only the low 32 bits of the value are stored. -/
theorem le32Bytes_mod (n : Nat) : le32Bytes (n % 4294967296) = le32Bytes n := by
  simp only [le32Bytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

/-- Rebuilding a `ByteArray` from its byte list is the identity. -/
theorem byteArray_eta (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  simp

theorem byteArray_size_toList (b : ByteArray) : b.size = b.data.toList.length := by
  rw [ByteArray.size]
  exact (Array.length_toList ..).symm

end Silmaril.Formats.Compression
