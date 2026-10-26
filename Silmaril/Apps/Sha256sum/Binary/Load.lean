module

public import Silmaril.Apps.Sha256sum.Binary.Image
public import Silmaril.Apps.Sha256sum.Binary.Compress

/-! # Loading `sha256sum-min` puts the pilot `sha256_compress` where the contract wants it

`readWith_segment`: in any memory where an image is mapped (`Image.Mapped`, the loader
clause of `Process.CLI.X86Linux.Loaded`), reading inside a segment with an access the
segment permits returns the segment's contents.

For `sha256sum-min` this discharges two preconditions of the pilot contract
(`Sha256O2.SysVEntry.code` and `.kTable`) from the loader alone:

* `loaded_code`: the 459 executable bytes at `sha256_compress` are
  `Sha256O2.image textBase rodataBase`;
* `loaded_kTable`: the 256 readable bytes at `sha256_compress_K` are `Sha256O2.kBytes`.

Both go through the lifted transcription `Binary.Compress`, whose bytes the kernel decoded
with `X86.Ext.decode` (`Compress.transcript_verify`) and compared with the pilot image
(`Compress.bytes_eq_Binary_linkedImage`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary

open Silmaril.Process (Byte Memory Access)
open Silmaril.Process.CLI

theorem readWith_segment {image : Image} {memory : Memory} (h : image.Mapped memory)
    {seg : Segment} (hs : seg ∈ image.segments) (wf : image.WF) {acc : Access}
    (hp : seg.permissions.allows acc = true) (off len : Nat)
    (hlen : off + len ≤ seg.memSize) (hpos : 0 < len) :
    memory.readWith acc (seg.vaddr + off) len = some ((seg.contents.drop off).take len) := by
  obtain ⟨hfit, hwrap⟩ := wf seg hs
  obtain ⟨hreg, hbytes⟩ := h seg hs
  have hclen : seg.contents.length = seg.memSize := by
    simp [Segment.contents]; omega
  have hblen : ((seg.contents.drop off).take len).length = len := by
    simp; omega
  conv => lhs; rw [← hblen]
  apply Memory.readWith_eq
  · rw [hblen]
    simp only [Memory.Permitted, Memory.checkSpan_iff]
    refine ⟨by unfold Silmaril.Process.addressLimit at hwrap ⊢; omega,
      by unfold Silmaril.Process.addressLimit at hwrap ⊢; omega, fun o ho => ?_⟩
    simp only [Memory.permits, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨seg.region, hreg, ⟨by simp [Segment.region]; omega, by simp [Segment.region]; omega⟩,
      by simpa [Segment.region] using hp⟩
  · intro i hi
    have hi' : off + i < seg.contents.length := by rw [hblen] at hi; omega
    have := hbytes (off + i) hi'
    rw [← Nat.add_assoc] at this
    rw [this]
    simp

theorem seg1_mem : Image.seg1 ∈ Image.image.segments := by simp [Image.image]
theorem seg2_mem : Image.seg2 ∈ Image.image.segments := by simp [Image.image]

/-- The executable segment holds the transcribed `sha256_compress` at `0x405200`. -/
theorem seg1_compress :
    (Image.seg1.contents.drop (0x405200 - 0x401000)).take 459 = Compress.bytes := by
  decide +kernel

/-- The read-only segment holds the transcribed K table at `0x407f10`. -/
theorem seg2_K :
    (Image.seg2.contents.drop (0x407f10 - 0x406000)).take 256 = Compress.const_sha256_compress_K := by
  decide +kernel

/-- **Loading puts the pilot image at `sha256_compress`.** -/
theorem loaded_code {memory : Memory} (h : Image.image.Mapped memory) :
    memory.fetchBytes textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
      some (Silmaril.Crypto.X86.Sha256O2.image textBase rodataBase) := by
  have := readWith_segment h seg1_mem Image.image_wf (acc := .execute) (by decide)
    (0x405200 - 0x401000) 459 (by decide) (by decide)
  rw [seg1_compress, Compress.bytes_eq_Binary_linkedImage] at this
  exact this

/-- **Loading puts the K table at `sha256_compress_K`.** -/
theorem loaded_kTable {memory : Memory} (h : Image.image.Mapped memory) :
    memory.readBytes rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
      some Silmaril.Crypto.X86.Sha256O2.kBytes := by
  have := readWith_segment h seg2_mem Image.image_wf (acc := .read) (by decide)
    (0x407f10 - 0x406000) 256 (by decide) (by decide)
  rw [seg2_K, Compress.const_sha256_compress_K_eq_Sha256O2_kBytes] at this
  exact this

end Silmaril.Apps.Sha256sum.Binary
