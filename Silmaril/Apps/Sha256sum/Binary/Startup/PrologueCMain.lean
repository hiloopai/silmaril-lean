module

public import Silmaril.Apps.Sha256sum.Binary.Startup.CmainCut
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Wire

/-! # `Wire.CMain` at the end of `digest_file`'s prologue

`digest_file`'s prologue (`Startup.Prologue`, from `AtDigestEntryW` at `0x402de0` to the read
loop's head) writes only `PW sp0`: its own frame `[sp0 - 448, sp0 - 248)`, `*missing`
(`cmain`'s `0x90(%rsp)`, i.e. `[sp0 - 96, sp0 - 92)`) and `have_read_stdin` (`0x40a0a0`).
`cmain_of_entry` (VERIFIED) packages, for any memory `m'` written within `PW` from the entry
memory with `have_read_stdin = 1`, `cmain`'s state `Wire.CMain (sp0 - 240) m'` the tail needs:

* from `AtDigestEntryW`: `ok = 1`, the operand index `0` of count `1`, `binary = 0`;
* from `LaunchFacts`: the text (`Lift.code_of_mapped`, `Ro`), the `hexd` table (`.rodata`),
  `prefix_tag = 0`, `digest_delim = '\n'`, `err_error = 0`, the empty output layer (the
  `.data`/`.bss` image), the stack bounds and permissions; each kept through `W2` (startup)
  and `PW` (prologue), which miss it;
* `have_read_stdin = 1`: the hypothesis.

This file must not import `Startup.Prologue` (which imports it); `PW` is defined here, in
`Prologue`'s namespace.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Prologue

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (leBytes)
open Silmaril.Apps.Sha256sum.X86Sys (XState ofU8)
open Silmaril.Process.LPS.Problems.GnuSha256sum

/-- What the prologue writes: its frame (the six saved registers and `digest_file`'s locals),
`*missing` (`cmain`'s `0x90(%rsp)`), `have_read_stdin`. -/
def PW (sp0 : Word) (a : Nat) : Prop :=
  (sp0.toNat - 448 ≤ a ∧ a < sp0.toNat - 248) ∨ (sp0.toNat - 96 ≤ a ∧ a < sp0.toNat - 92) ∨
    (0x40a0a0 ≤ a ∧ a < 0x40a0a4)

theorem seg2_rd {m : Memory} (h : Image.image.Mapped m) (off len : Nat)
    (hlen : off + len ≤ 0x2010) (hpos : 0 < len) {v : List Byte}
    (hv : (Image.seg2.contents.drop off).take len = v) :
    m.readWith .read (0x406000 + off) len = some v :=
  hv ▸ readWith_segment h seg2_mem Image.image_wf (acc := .read) (by decide) off len hlen hpos

theorem seg3_mem' : Image.seg3 ∈ Image.image.segments := by simp [Image.image]

theorem seg3_rd {m : Memory} (h : Image.image.Mapped m) (off len : Nat)
    (hlen : off + len ≤ 0xa140) (hpos : 0 < len) {v : List Byte}
    (hv : (Image.seg3.contents.drop off).take len = v) :
    m.readWith .read (0x409010 + off) len = some v :=
  hv ▸ readWith_segment h seg3_mem' Image.image_wf (acc := .read) (by decide) off len hlen hpos

/-- The text survives writes that miss it. -/
theorem code_of_ww {m m' : Memory} {F : Nat → Prop} (hc : Apps.Sha256sum.Lift.Code m)
    (hw : Memory.WritesWithin m m' F)
    (hF : ∀ a, F a → ¬ (0x401000 ≤ a ∧ a < 0x401000 + 0x43cb)) :
    Apps.Sha256sum.Lift.Code m' := by
  refine ⟨?_, fun a h1 h2 => by rw [hw.permits]; exact hc.ro a h1 h2⟩
  rw [hw.fetchBytes]; · exact hc.textAt
  intro o ho hin
  have := hF _ hin
  simp only [Apps.Sha256sum.Lift.textBase, Apps.Sha256sum.Lift.textSize] at ho this
  omega

/-- **VERIFIED. `cmain`'s state after `digest_file`'s prologue**: from `digest_file`'s entry
`AtDigestEntryW c s` (with the launch facts), any memory `m'` written within `PW` from `s`'s
memory with `have_read_stdin = 1` holds `Wire.CMain` at `cmain`'s `rsp = sp0 - 240`. -/
theorem cmain_of_entry {c : Ctx} {s : XState} {m' : Memory} (hl : LaunchFacts c)
    (h : AtDigestEntryW c s) (hw : Memory.WritesWithin s.memory m' (PW c.sp0))
    (hstdin : m'.readWith .read 0x40a0a0 4 = some (leBytes 1#64 4)) :
    Wire.CMain (c.sp0 - 240#64) m' := by
  have lo := hl.spLo
  have hi := hl.spHi
  -- the combined footprint from launch
  have hw2 : Memory.WritesWithin c.m0 m' (fun a => W2 c.sp0 a ∨ PW c.sp0 a) :=
    (h.entry.mem.mono fun _ h => Or.inl h).trans (hw.mono fun _ h => Or.inr h)
  have esp : (c.sp0 - 240#64).toNat = c.sp0.toNat - 240 := by
    rw [BitVec.toNat_sub_of_le] <;> simp only [BitVec.le_def, BitVec.toNat_ofNat]
    omega
  have ex : ∀ k : Nat, k < 0x100 → (c.sp0 - 240#64 + BitVec.ofNat 64 k).toNat =
      c.sp0.toNat - 240 + k := by
    intro k hk
    rw [BitVec.toNat_add, esp, BitVec.toNat_ofNat]; omega
  -- a byte of the image (below the stack room, not in `W2 ∨ PW`)
  have img : ∀ a, 0x400000 ≤ a → a < 0x413150 → ¬ (0x412118 ≤ a ∧ a < 0x412128) →
      ¬ (0x409010 ≤ a ∧ a < 0x409014) → ¬ (0x40a0a0 ≤ a ∧ a < 0x40a0a4) →
      ¬ (W2 c.sp0 a ∨ PW c.sp0 a) := by
    intro a h1 h2 h3 h4 h5 hin
    simp only [W2, W1, PW] at hin
    omega
  -- a byte of `cmain`'s frame outside the prologue's writes
  have frm : ∀ k len : Nat, 0x28 ≤ k → k + len ≤ 0x90 → ∀ o < len,
      ¬ PW c.sp0 ((c.sp0 - 240#64 + BitVec.ofNat 64 k).toNat + o) := by
    intro k len h1 h2 o ho hin
    rw [ex k (by omega)] at hin
    simp only [PW] at hin; omega
  have frm8 : ∀ o < 8, ¬ PW c.sp0 ((c.sp0 - 240#64 + 8#64).toNat + o) := by
    intro o ho hin
    rw [ex 8 (by omega)] at hin
    simp only [PW] at hin; omega
  have hmap := hl.mapped
  have hcode0 : Apps.Sha256sum.Lift.Code c.m0 :=
    Apps.Sha256sum.Lift.code_of_mapped hmap fun a h1 h2 => hl.ro a
      (by simp only [Apps.Sha256sum.Lift.textBase] at h1; omega)
      (by simp only [Apps.Sha256sum.Lift.textBase, Apps.Sha256sum.Lift.textSize] at h2; omega)
  have perm : ∀ acc : Silmaril.Process.Access, acc ≠ .execute →
      m'.Permitted acc ((c.sp0 - 240#64).toNat - 128) (128 + 0x98) := by
    intro acc hacc
    rw [hw2.permitted_iff, esp]
    exact Silmaril.X86.Ext.Memory.Permitted.sub (hl.rw acc hacc) (by decide) (by omega)
      (by omega)
  have dperm : ∀ acc : Silmaril.Process.Access, acc ≠ .execute →
      m'.Permitted acc 0x409010 0xa140 := by
    intro acc hacc
    rw [hw2.permitted_iff]
    exact data_perm hmap acc hacc
  have imgR : ∀ (a len : Nat) (v : List Byte), 0x400000 ≤ a → a + len ≤ 0x413150 →
      (0x412128 ≤ a ∨ a + len ≤ 0x409010 ∨ (0x409014 ≤ a ∧ a + len ≤ 0x40a0a0)) →
      c.m0.readWith .read a len = some v → m'.readWith .read a len = some v := by
    intro a len v h1 h2 h3 hr
    exact Wire.keep_read hw2 (fun o ho => img _ (by omega) (by omega) (by omega) (by omega)
      (by omega)) hr
  refine ⟨code_of_ww hcode0 hw2 fun a ha hin => img a (by omega) (by omega)
      (by omega) (by omega) (by omega) ha, ?_, ⟨by omega, by omega⟩, perm .read (by decide),
    perm .write (by decide), Wire.keep_read hw (frm 0x2c 4 (by decide) (by decide)) h.okFlag,
    ⟨Wire.keep_read hw frm8 h.argIdx, Wire.keep_read hw (frm 0x50 4 (by decide) (by decide))
      h.argLast⟩, hstdin, ?_, ?_,
    Wire.keep_read hw (fun o ho hin => by simp only [PW] at hin; omega) h.binary, ?_,
    ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact imgR _ _ _ (by decide) (by decide) (by decide)
      (seg2_rd hmap 0x12c0 16 (by decide) (by decide) (by decide +kernel))
  · exact imgR _ _ _ (by decide) (by decide) (by decide)
      (seg3_rd hmap 0x10 4 (by decide) (by decide) (by decide +kernel))
  · exact imgR _ _ _ (by decide) (by decide) (by decide)
      (seg3_rd hmap 4 1 (by decide) (by decide) (by decide +kernel))
  · exact imgR _ _ _ (by decide) (by decide) (by decide)
      (seg3_rd hmap 0x9118 4 (by decide) (by decide) (by decide +kernel))
  · exact imgR _ _ _ (by decide) (by decide) (by decide)
      (seg3_rd hmap 0x9120 8 (by decide) (by decide) (by decide +kernel))
  · have := Silmaril.Process.Memory.readWith_sub_range
      (seg3_rd hmap 0x9130 1 (by decide) (by decide) rfl) (offset := 0) (len := 0)
      (by decide) (by decide)
    exact imgR _ _ _ (by decide) (by decide) (by decide) (by simpa using this)
  · exact imgR _ _ _ (by decide) (by decide) (by decide)
      (seg3_rd hmap 0x911c 4 (by decide) (by decide) (by decide +kernel))
  · exact Silmaril.X86.Ext.Memory.Permitted.sub (dperm .write (by decide)) (by decide)
      (by decide) (by decide)
  · exact Silmaril.X86.Ext.Memory.Permitted.sub (dperm .write (by decide)) (by decide)
      (by decide) (by decide)
  · exact Silmaril.X86.Ext.Memory.Permitted.sub (dperm .read (by decide)) (by decide)
      (by decide) (by decide)

end Silmaril.Apps.Sha256sum.Binary.Startup.Prologue
