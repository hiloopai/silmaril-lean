module

public import Silmaril.Process.CLI.Cover.Defs
public import Silmaril.Process.CLI.Loaded.Thms

/-!
# Proofs: covered ranges, and code and data in a loaded image

The header is `Silmaril/Process/CLI/Cover/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.CLI.Cover

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.X86.Link.Blob (valueLE)

theorem valueLE_inj : ∀ {xs ys : List Byte}, xs.length = ys.length → valueLE xs = valueLE ys →
    xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [valueLE] at h
    have hx := x.isLt
    have hy := y.isLt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : valueLE xs = valueLE ys := by omega
    rw [BitVec.eq_of_toNat_eq h1, valueLE_inj (by simpa using hl) h2]

/-- A range found in one segment: the segment holds its bytes at its address. -/
theorem slice_of_inSeg {s : Segment} {a : Nat} {bs : List Byte} {x : Bool}
    (h : Range.inSeg ⟨a, bs.length, x, valueLE bs⟩ s = true) :
    s.permissions.write = false ∧
      (if x then s.permissions.execute else s.permissions.read) = true ∧
      s.vaddr ≤ a ∧ a + bs.length ≤ s.vaddr + s.memSize ∧
      (s.contents.drop (a - s.vaddr)).take bs.length = bs := by
  simp only [Range.inSeg, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hw, hx⟩, hlo⟩, hhi⟩, hv⟩ := h
  refine ⟨hw, hx, hlo, hhi, valueLE_inj ?_ hv⟩
  have := s.memSize_le_contents
  simp only [List.length_take, List.length_drop]
  omega

theorem Covers.codeIn {img : Image} {seg : Seg} {a : Nat} {code : List Byte}
    (h : Covers img seg) (hr : ⟨a, code.length, true, valueLE code⟩ ∈ seg.ranges) :
    CodeIn img a code := by
  obtain ⟨s, hs, hin⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ hr)
  obtain ⟨hw, hx, hlo, hhi, hv⟩ := slice_of_inSeg hin
  exact ⟨s, hs, hw, hx, hlo, hhi, hv⟩

theorem Covers.dataIn {img : Image} {seg : Seg} {a : Nat} {bytes : List Byte}
    (h : Covers img seg) (hr : ⟨a, bytes.length, false, valueLE bytes⟩ ∈ seg.ranges) :
    DataIn img a bytes := by
  obtain ⟨s, hs, hin⟩ := List.any_eq_true.1 (List.all_eq_true.1 h _ hr)
  obtain ⟨hw, hx, hlo, hhi, hv⟩ := slice_of_inSeg hin
  exact ⟨s, hs, hw, hx, hlo, hhi, hv⟩

/-- A slice of a loaded segment reads back under the access the segment allows. -/
theorem readWith_slice {mem : Memory} {s : Segment} {access : Silmaril.Process.Access}
    (hf : mem.readWith access s.vaddr s.contents.length = some s.contents) {a : Nat}
    {bs : List Byte} (pos : 0 < bs.length) (hlo : s.vaddr ≤ a)
    (hhi : a + bs.length ≤ s.vaddr + s.memSize)
    (hv : (s.contents.drop (a - s.vaddr)).take bs.length = bs) :
    mem.readWith access a bs.length = some bs := by
  have hlen := s.memSize_le_contents
  have := Memory.readWith_sub_range hf (offset := a - s.vaddr) (len := bs.length)
    (by omega) (by omega)
  rwa [hv, show s.vaddr + (a - s.vaddr) = a by omega] at this

theorem CodeIn.fetch {img : Image} {a : Nat} {code : List Byte} {mem : Memory}
    (h : CodeIn img a code) (hl : img.Loaded mem) (pos : 0 < code.length) :
    mem.fetchBytes a code.length = some code := by
  obtain ⟨s, hs, hw, hx, hlo, hhi, hv⟩ := h
  exact readWith_slice ((hl s hs hw).2 hx) pos hlo hhi hv

theorem DataIn.read {img : Image} {a : Nat} {bytes : List Byte} {mem : Memory}
    (h : DataIn img a bytes) (hl : img.Loaded mem) (pos : 0 < bytes.length) :
    mem.readBytes a bytes.length = some bytes := by
  obtain ⟨s, hs, hw, hr, hlo, hhi, hv⟩ := h
  exact readWith_slice ((hl s hs hw).1 hr) pos hlo hhi hv

end Silmaril.Proofs.Process.CLI.Cover
