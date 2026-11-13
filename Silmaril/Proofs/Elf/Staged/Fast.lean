module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.X86.Link.Blob.Thms
public import Silmaril.Prelude.Bytes.Thms

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

namespace Silmaril.Proofs.Elf.Staged

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Elf.Check (Sub)

theorem fastRead_list (l : List UInt8) : ∀ (w o : Nat), o + w ≤ l.length →
    fastRead ⟨⟨l⟩⟩ o w = some (Silmaril.KBytes.leVal ((l.drop o).take w))
  | 0, _, _ => by simp [fastRead, Silmaril.KBytes.leVal]
  | w + 1, o, h => by
    have ho : o < l.length := by omega
    have hs : o < (ByteArray.mk ⟨l⟩).size := by simpa [ByteArray.size] using ho
    simp only [fastRead, hs, ↓reduceDIte]
    rw [fastRead_list l w (o + 1) (by omega)]
    rw [List.drop_eq_getElem_cons ho, List.take_succ_cons]
    simp [Silmaril.KBytes.leVal, ByteArray.getElem_eq_getElem_data]

/-- **Kernel bytes answer as the file of their bytes.** -/
theorem sub_kbytes (x : Silmaril.KBytes) (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) : Sub x.readLE (blobOf ⟨raw⟩) := by
  intro o w v hr
  rw [Silmaril.KBytes.readLE_eq x hx] at hr
  split at hr
  · rename_i hle
    cases hr
    apply sub_fast ⟨raw⟩ o w
    show fastRead raw o w = _
    rw [← h]
    exact fastRead_list x.toList w o hle
  · cases hr

end Silmaril.Proofs.Elf.Staged
