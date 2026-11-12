module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.X86.Link.Blob.Thms

/-! # The fast source answers as the file

`sub_fast`: `fastRead` on the bytes of a value reads the file `blobOf b` (standard axioms). -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Staged

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.Elf.Check (Sub)
open Silmaril.X86.Link (Blob)

theorem elfBytes_getElem? (b : Silmaril.Formats.Bytes) (o : Nat) :
    (Silmaril.Project.Formats.elfBytes b).toList[o]? =
      if h : o < b.data.size then some (BitVec.ofNat 8 b.data[o].toNat) else none := by
  simp only [Silmaril.Project.Formats.elfBytes, Silmaril.Formats.Bytes.toList]
  rw [Array.toList_map, List.toList_toArray, List.getElem?_map, Array.getElem?_toList]
  split
  · rename_i h
    rw [Array.getElem?_eq_getElem (by exact h)]
    rfl
  · rename_i h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]
    rfl

theorem fastRead_eq (b : Silmaril.Formats.Bytes) : ∀ (w o : Nat),
    fastRead b.data o w = Silmaril.Formats.ELF.readLE (Silmaril.Project.Formats.elfBytes b) o w
  | 0, _ => rfl
  | w + 1, o => by
    simp only [fastRead, Silmaril.Formats.ELF.readLE, elfBytes_getElem?, fastRead_eq b w (o + 1)]
    split
    · cases Silmaril.Formats.ELF.readLE (Silmaril.Project.Formats.elfBytes b) (o + 1) w with
      | none => rfl
      | some v =>
        show _ = (Option.some _ >>= _)
        simp
    · rfl

/-- **`fastRead` on the bytes of `b` answers as the file `blobOf b`.** -/
theorem sub_fast (b : Silmaril.Formats.Bytes) : Sub (fastRead b.data) (blobOf b) := by
  intro o w v h
  rw [fastRead_eq] at h
  have e := Blob.readLE_bytesOf (blobOf b).n (blobOf b).len o w
  have hb : Blob.bytesOf (blobOf b).n (blobOf b).len = Silmaril.Project.Formats.elfBytes b :=
    Blob.bytes_ofBytes _
  rw [hb] at e
  show Blob.readLEN _ _ o w = some v
  rw [← e]; exact h

end Silmaril.Proofs.Elf.Staged
