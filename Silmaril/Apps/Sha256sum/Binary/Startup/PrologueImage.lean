module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Cuts
public import Silmaril.Apps.Sha256sum.Binary.Digest.Spec
public import Silmaril.Apps.Sha256sum.Binary.Digest.Code
public import Silmaril.Apps.Sha256sum.Binary.Sc3
public import Silmaril.Apps.Sha256sum.Binary.Load

/-! # Image facts for the prologue of `digest_file`

What the prologue (`Startup.Prologue`) needs from the loaded image, from `Image.image.Mapped`
alone:

* `operand_dash`, `operand_nul`: the literal `"-"` at `0x406052` (read-only segment 2);
* `seg3_permitted`: any span inside segment 3 (`[0x409010, 0x413150)`, read/write) is
  permitted for reading and writing, with the instances `have_read_stdin` (`0x40a0a0`, 4
  bytes) and `iobuf` (`0x40a0c0`, 32768 bytes);
* `sc3_loaded`, `loop_loaded`: the wrapper `sc3` and the read loop are loaded.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.PrologueImage

open Silmaril.Process (Byte Memory Access)
open Silmaril.Process.CLI
open Silmaril.X86.Ext (Loaded loadN)

/-- A span inside a mapped segment is permitted for any access the segment allows. -/
theorem permitted_segment {image : Image} {memory : Memory} (h : image.Mapped memory)
    {seg : Segment} (hs : seg ∈ image.segments) (wf : image.WF) {acc : Access}
    (hp : seg.permissions.allows acc = true) (off len : Nat)
    (hoff : off < seg.memSize) (hlen : off + len ≤ seg.memSize) :
    memory.Permitted acc (seg.vaddr + off) len := by
  obtain ⟨hfit, hwrap⟩ := wf seg hs
  obtain ⟨hreg, _⟩ := h seg hs
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by unfold Silmaril.Process.addressLimit at hwrap ⊢; omega,
    by unfold Silmaril.Process.addressLimit at hwrap ⊢; omega, fun o ho => ?_⟩
  simp only [Memory.permits, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨seg.region, hreg, ⟨by simp [Segment.region]; omega, by simp [Segment.region]; omega⟩,
    by simpa [Segment.region] using hp⟩

theorem seg3_mem : Image.seg3 ∈ Image.image.segments := by simp [Image.image]

/-- **Segment 3 is readable**: any span inside `[0x409010, 0x413150)`. -/
theorem seg3_read {m : Memory} (h : Image.image.Mapped m) {a len : Nat}
    (h1 : 0x409010 ≤ a) (h2 : a + len ≤ 0x413150) : m.Permitted .read a len := by
  rcases Nat.eq_zero_or_pos len with rfl | hpos
  · simp only [Memory.Permitted, Memory.checkSpan_iff, Silmaril.Process.addressLimit]
    refine ⟨by omega, by omega, fun o ho => absurd ho (Nat.not_lt_zero _)⟩
  have := permitted_segment h seg3_mem Image.image_wf (acc := .read) (by decide)
    (a - 0x409010) len (by simp [Image.seg3]; omega) (by simp [Image.seg3]; omega)
  have e : Image.seg3.vaddr + (a - 0x409010) = a := by simp [Image.seg3]; omega
  rwa [e] at this

/-- **Segment 3 is writable**: any span inside `[0x409010, 0x413150)`. -/
theorem seg3_write {m : Memory} (h : Image.image.Mapped m) {a len : Nat}
    (h1 : 0x409010 ≤ a) (h2 : a + len ≤ 0x413150) : m.Permitted .write a len := by
  rcases Nat.eq_zero_or_pos len with rfl | hpos
  · simp only [Memory.Permitted, Memory.checkSpan_iff, Silmaril.Process.addressLimit]
    refine ⟨by omega, by omega, fun o ho => absurd ho (Nat.not_lt_zero _)⟩
  have := permitted_segment h seg3_mem Image.image_wf (acc := .write) (by decide)
    (a - 0x409010) len (by simp [Image.seg3]; omega) (by simp [Image.seg3]; omega)
  have e : Image.seg3.vaddr + (a - 0x409010) = a := by simp [Image.seg3]; omega
  rwa [e] at this

/-- `have_read_stdin` (`0x40a0a0`) is readable. -/
theorem haveReadStdin_read {m : Memory} (h : Image.image.Mapped m) :
    m.Permitted .read 0x40a0a0 4 := seg3_read h (by decide) (by decide)

/-- `have_read_stdin` (`0x40a0a0`) is writable. -/
theorem haveReadStdin_write {m : Memory} (h : Image.image.Mapped m) :
    m.Permitted .write 0x40a0a0 4 := seg3_write h (by decide) (by decide)

/-- `iobuf` (`0x40a0c0`, 32768 bytes) is readable. -/
theorem iobuf_read {m : Memory} (h : Image.image.Mapped m) :
    m.Permitted .read 0x40a0c0 32768 := seg3_read h (by decide) (by decide)

/-- `iobuf` (`0x40a0c0`, 32768 bytes) is writable. -/
theorem iobuf_write {m : Memory} (h : Image.image.Mapped m) :
    m.Permitted .write 0x40a0c0 32768 := seg3_write h (by decide) (by decide)

theorem seg2_dash : (Image.seg2.contents.drop (0x406052 - 0x406000)).take 1 = [0x2d] := by
  decide +kernel

theorem seg2_nul : (Image.seg2.contents.drop (0x406053 - 0x406000)).take 1 = [0x00] := by
  decide +kernel

/-- **The operand literal's first byte is `'-'`** (`0x406052`). -/
theorem operand_dash {m : Memory} (h : Image.image.Mapped m) :
    loadN m 0x406052#64 1 = some 0x2d#64 := by
  have := readWith_segment h seg2_mem Image.image_wf (acc := .read) (by decide)
    (0x406052 - 0x406000) 1 (by decide) (by decide)
  rw [seg2_dash] at this
  have e : Image.seg2.vaddr + (0x406052 - 0x406000) = (0x406052#64 : Silmaril.X86.Word).toNat := rfl
  rw [e] at this
  rw [Silmaril.X86.Ext.loadN_of_readBytes this]
  rfl

/-- **The operand literal's second byte is `NUL`** (`0x406053`). -/
theorem operand_nul {m : Memory} (h : Image.image.Mapped m) :
    loadN m 0x406053#64 1 = some 0#64 := by
  have := readWith_segment h seg2_mem Image.image_wf (acc := .read) (by decide)
    (0x406053 - 0x406000) 1 (by decide) (by decide)
  rw [seg2_nul] at this
  have e : Image.seg2.vaddr + (0x406053 - 0x406000) = (0x406053#64 : Silmaril.X86.Word).toNat := rfl
  rw [e] at this
  rw [Silmaril.X86.Ext.loadN_of_readBytes this]
  rfl

/-- The wrapper `sc3` is loaded (`Sc3.loaded`). -/
theorem sc3_loaded {m : Memory} (h : Image.image.Mapped m) : Loaded m Sc3.base Sc3.code :=
  Sc3.loaded h

/-- The read loop is loaded (`Digest.loaded`). -/
theorem loop_loaded {m : Memory} (h : Image.image.Mapped m) : Loaded m Digest.base Digest.code :=
  Digest.loaded h

end Silmaril.Apps.Sha256sum.Binary.Startup.PrologueImage
