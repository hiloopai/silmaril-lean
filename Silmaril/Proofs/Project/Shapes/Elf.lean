module

public import Silmaril.Project.Shapes.Elf.Defs
public import Silmaril.X86.Ladder.Pinned.Thms
public import Silmaril.X86.Link.Blob.Thms
public import Silmaril.Data.IncludeBytes.Types
import Silmaril.Data.IncludeBytes

/-! # Proofs: the ELF shapes (`Silmaril.Project.Shapes.Elf.Thms`)

`loads_x86_iff` (`Loads Loader.x86` is `Pinned.LoadedAt` on the file as a `Blob`),
`entry_x86_of_blob`, and `ofBytes_decode`: an included file as a `Blob`, computed from its
chunk literals (`chunksVal`, `chunksLen`) without decoding its bytes.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.Elf

open Silmaril.Process.LPS
open Silmaril.X86.Link
open Silmaril.Project
open Silmaril.Project.Shapes
open Silmaril.X86.Ladder (Pinned.LoadedAt)

theorem loads_x86_iff {V : Type} (X : Value V) (perms : String) (addr : Nat)
    (code : List (BitVec 8)) :
    Loads Loader.x86 X perms addr code ↔
      Pinned.LoadedAt (Blob.ofBytes (Silmaril.Project.Formats.elfBytes X.bytes)) perms addr
        code := by
  simp only [Loads, Loader.x86, Loader.lps, Pinned.LoadedAt, Blob.bytes_ofBytes,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    exact ⟨r, hr, h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨_, ⟨r, hr, rfl⟩, h⟩

theorem entry_x86_of_blob {V : Type} {X : Value V} {B : Blob} {addr : Nat}
    (hB : Blob.ofBytes (Silmaril.Project.Formats.elfBytes X.bytes) = B)
    (h : (Blob.parseN ELFImage.x86Policy B.n B.len).map (·.header.entry) = some addr) :
    Entry Loader.x86 X addr := by
  have hb : Silmaril.Project.Formats.elfBytes X.bytes = B.bytes := by
    rw [← hB, Blob.bytes_ofBytes]
  rw [Option.map_eq_some_iff] at h
  obtain ⟨r, hr, he⟩ := h
  refine ⟨r.image B.bytes, ?_, he⟩
  simp only [Loader.x86, Loader.lps, hb]
  rw [Blob.bytes, Blob.parse_bytesOf, hr]
  rfl

theorem entry_x86_of_satisfies {X : Value ELFImage.Records} {addr : Nat}
    (hF : X.format = Silmaril.Project.Formats.elfExecX86)
    (h : X.Satisfies fun r => r.header.entry = addr) : Entry Loader.x86 X addr := by
  obtain ⟨r, hr, he⟩ := h
  have hp : ELFImage.parse ELFImage.x86Policy (Silmaril.Project.Formats.elfBytes X.bytes) =
      some r := by
    rw [← hr, Value.parse, hF]; rfl
  exact ⟨r.image (Silmaril.Project.Formats.elfBytes X.bytes),
    by simp only [Loader.x86, Loader.lps, hp, Option.map_some], he⟩

section Decode

open Silmaril.IncludeBytes (bytesLE bytesChunks decode)

/-- The byte map of `elfBytes`. -/
abbrev toBv (x : UInt8) : BitVec 8 := BitVec.ofNat 8 x.toNat

theorem valueLE_append (l₁ l₂ : List (BitVec 8)) :
    Blob.valueLE (l₁ ++ l₂) = Blob.valueLE l₁ + 256 ^ l₁.length * Blob.valueLE l₂ := by
  induction l₁ with
  | nil => simp [Blob.valueLE]
  | cons x t ih =>
    show x.toNat + 256 * Blob.valueLE (t ++ l₂) =
      x.toNat + 256 * Blob.valueLE t + 256 ^ (t.length + 1) * Blob.valueLE l₂
    rw [ih, Nat.mul_add, ← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm (256 ^ t.length) 256,
      Nat.mul_assoc]

theorem valueLE_bytesLE (k n : Nat) :
    Blob.valueLE ((bytesLE k n).map toBv) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [bytesLE, Blob.valueLE, Nat.mod_one]
  | succ k ih =>
    have hb : (toBv (UInt8.ofNat n)).toNat = n % 256 := by simp [toBv]
    show (toBv (UInt8.ofNat n)).toNat + 256 * Blob.valueLE ((bytesLE k (n / 256)).map toBv) =
      n % 256 ^ (k + 1)
    rw [hb, ih, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

theorem valueLE_bytesChunks (chunk len : Nat) (cs : List Nat) :
    Blob.valueLE ((bytesChunks chunk len cs).map toBv) = chunksVal chunk len cs := by
  induction cs generalizing len with
  | nil => rfl
  | cons c cs ih =>
    show Blob.valueLE ((bytesLE (min chunk len) c ++ bytesChunks chunk (len - chunk) cs).map
        toBv) = c % 256 ^ min chunk len + 256 ^ min chunk len * chunksVal chunk (len - chunk) cs
    rw [List.map_append, valueLE_append, valueLE_bytesLE, ih, List.length_map,
      Silmaril.IncludeBytes.length_bytesLE]

theorem length_bytesChunks (chunk len : Nat) (cs : List Nat) :
    (bytesChunks chunk len cs).length = chunksLen chunk len cs := by
  induction cs generalizing len with
  | nil => rfl
  | cons c cs ih =>
    show (bytesLE (min chunk len) c ++ bytesChunks chunk (len - chunk) cs).length =
      min chunk len + chunksLen chunk (len - chunk) cs
    rw [List.length_append, Silmaril.IncludeBytes.length_bytesLE, ih]

theorem ofBytes_decode (chunk len : Nat) (cs : List Nat) :
    Blob.ofBytes (Silmaril.Project.Formats.elfBytes ⟨decode chunk len cs⟩) =
      ⟨chunksVal chunk len cs, chunksLen chunk len cs⟩ := by
  have hl : (Silmaril.Project.Formats.elfBytes ⟨decode chunk len cs⟩).toList =
      (bytesChunks chunk len cs).map toBv := by
    simp [Silmaril.Project.Formats.elfBytes, Silmaril.Formats.Bytes.toList, decode]
  have hs : (Silmaril.Project.Formats.elfBytes ⟨decode chunk len cs⟩).size =
      chunksLen chunk len cs := by
    rw [Array.size_eq_length_toList, hl, List.length_map, length_bytesChunks]
  show (⟨Blob.valueLE (Silmaril.Project.Formats.elfBytes ⟨decode chunk len cs⟩).toList,
    (Silmaril.Project.Formats.elfBytes ⟨decode chunk len cs⟩).size⟩ : Blob) = _
  rw [hs, hl, valueLE_bytesChunks]

end Decode

end Silmaril.Proofs.Project.Shapes.Elf

end
