module

public import Silmaril.Elf.Pin.Defs
public import Silmaril.Elf.Parse.Defs

/-! # Proofs of `Silmaril.Elf.Pin` -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Pin

open Silmaril.IncludeBytes Silmaril.X86.Link Silmaril.Elf.Pin

/-- The byte map `blobOf` applies (`Project.Formats.elfBytes`). -/
def g : UInt8 → BitVec 8 := fun byte => BitVec.ofNat 8 byte.toNat

theorem valueLE_append : ∀ a b : List (BitVec 8),
    Blob.valueLE (a ++ b) = Blob.valueLE a + 2 ^ (8 * a.length) * Blob.valueLE b
  | [], b => by simp [Blob.valueLE]
  | x :: a, b => by
    simp only [List.cons_append, Blob.valueLE, valueLE_append a b, List.length_cons]
    rw [show 8 * (a.length + 1) = 8 + 8 * a.length by omega, Nat.pow_add]
    rw [show (2 : Nat) ^ 8 = 256 from rfl]; simp only [Nat.mul_add, ← Nat.mul_assoc]; omega

theorem valueLE_bytesLE : ∀ k n, Blob.valueLE ((bytesLE k n).map g) = n % 2 ^ (8 * k)
  | 0, n => by simp [bytesLE, Blob.valueLE, Nat.mod_one]
  | k + 1, n => by
    simp only [bytesLE, List.map_cons, Blob.valueLE, valueLE_bytesLE k (n / 256), g]
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add, Nat.mod_mul]
    simp [BitVec.toNat_ofNat]

theorem length_bytesLE : ∀ k n, (bytesLE k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [bytesLE, length_bytesLE k]

theorem valueLE_bytesChunks (chunk : Nat) : ∀ len cs,
    Blob.valueLE ((bytesChunks chunk len cs).map g) = chunksVal chunk len cs ∧
      (bytesChunks chunk len cs).length = chunksLen chunk len cs
  | _, [] => by simp [bytesChunks, chunksVal, chunksLen, Blob.valueLE]
  | len, c :: cs => by
    obtain ⟨h1, h2⟩ := valueLE_bytesChunks chunk (len - chunk) cs
    simp only [bytesChunks, List.map_append, chunksVal, chunksLen, List.length_append]
    rw [valueLE_append, valueLE_bytesLE, List.length_map, length_bytesLE, h1, h2]
    exact ⟨rfl, rfl⟩

theorem blobOf_decode (chunk len : Nat) (cs : List Nat) :
    Silmaril.Elf.blobOf ⟨decode chunk len cs⟩ = ⟨chunksVal chunk len cs, chunksLen chunk len cs⟩ := by
  obtain ⟨h1, h2⟩ := valueLE_bytesChunks chunk len cs
  simp only [Silmaril.Elf.blobOf, Blob.ofBytes, Silmaril.Project.Formats.elfBytes, decode,
    Silmaril.Formats.Bytes.toList, Array.toList_map, List.toList_toArray, Array.size_map,
    List.size_toArray]
  congr 1

end Silmaril.Proofs.Elf.Pin

end
