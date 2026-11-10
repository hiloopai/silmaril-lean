module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Next

/-!
# `adler32_z`: the VC of the prologue (entry to `0x20`)

Six pushes (`push_go`; the pushed registers become `Saved`), `s1 = rdi & 0xffff` into
`r15` (`start1`), `s2 = (rdi >> 16) & 0xffff` spilled (`start2`), arriving at the cut point
`0x20` with `InvP`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

theorem sp48 (c : Ctx) : c.m0.core.read .rsp - 48#64 = c.sp := rfl

set_option maxHeartbeats 40000000 in
theorem vcE (c : Ctx) (hP : c.Pre) (_hl : Loaded c.m0.memory c.base adler32zCode) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base none 20 0 c.m0 := by
  have hrip : c.m0.core.rip = c.base + BitVec.ofNat 64 0 := by simpa using hP.rip
  adler_vc [hrip, Mem.ofReg, sub8, sp48, start1 c hP, start2 c hP]
  have hlo := sp_toNat hP
  have a8 := push_toNat hP (k := 8) (by decide)
  have a16 := push_toNat hP (k := 16) (by decide)
  have a24 := push_toNat hP (k := 24) (by decide)
  have a32 := push_toNat hP (k := 32) (by decide)
  have a40 := push_toNat hP (k := 40) (by decide)
  refine push_go hP FM.refl a8 (by decide) (fun m1 hF1 hL1 hr1 hk1 => ?_)
  simp only [hL1, true_and]
  refine push_go hP hF1 a16 (by decide) (fun m2 hF2 hL2 hr2 hk2 => ?_)
  simp only [hL2, true_and]
  refine push_go hP hF2 a24 (by decide) (fun m3 hF3 hL3 hr3 hk3 => ?_)
  simp only [hL3, true_and]
  refine push_go hP hF3 a32 (by decide) (fun m4 hF4 hL4 hr4 hk4 => ?_)
  simp only [hL4, true_and]
  refine push_go hP hF4 a40 (by decide) (fun m5 hF5 hL5 hr5 hk5 => ?_)
  simp only [hL5, true_and]
  refine push_go hP hF5 (o := 48) hlo (by decide) (fun m6 hF6 hL6 hr6 hk6 => ?_)
  simp only [hL6, true_and]
  have hS6 : Saved c m6 := by
    have e1 := sp_add_toNat hP (k := 8) (by decide)
    have e2 := sp_add_toNat hP (k := 16) (by decide)
    have e3 := sp_add_toNat hP (k := 24) (by decide)
    have e4 := sp_add_toNat hP (k := 32) (by decide)
    have e5 := sp_add_toNat hP (k := 40) (by decide)
    refine ⟨hr6, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1, hk6 _ (by rw [hlo]; omega), show c.lo + 48 + 8 = (c.m0.core.read .rsp - 40#64).toNat by
        rw [a40]]; exact hr5
    · rw [e2, hk6 _ (by rw [hlo]; omega), hk5 _ (by rw [a40]; omega),
        show c.lo + 48 + 16 = (c.m0.core.read .rsp - 32#64).toNat by rw [a32]]; exact hr4
    · rw [e3, hk6 _ (by rw [hlo]; omega), hk5 _ (by rw [a40]; omega), hk4 _ (by rw [a32]; omega),
        show c.lo + 48 + 24 = (c.m0.core.read .rsp - 24#64).toNat by rw [a24]]; exact hr3
    · rw [e4, hk6 _ (by rw [hlo]; omega), hk5 _ (by rw [a40]; omega), hk4 _ (by rw [a32]; omega),
        hk3 _ (by rw [a24]; omega),
        show c.lo + 48 + 32 = (c.m0.core.read .rsp - 16#64).toNat by rw [a16]]; exact hr2
    · rw [e5, hk6 _ (by rw [hlo]; omega), hk5 _ (by rw [a40]; omega), hk4 _ (by rw [a32]; omega),
        hk3 _ (by rw [a24]; omega), hk2 _ (by rw [a16]; omega),
        show c.lo + 48 + 40 = (c.m0.core.read .rsp - 8#64).toNat by rw [a8]]; exact hr1
  refine store_go hP hF6 hS6 (slot16 hP) (by decide) (fun m7 hF7 hS7 hL7 hA7 _ => ?_)
  simp only [hL7, true_and]
  refine ⟨hP, ?_, hF7, hS7, ?_, ?_, ?_, ?_, hA7⟩
  all_goals seg_read [sp48]
  all_goals rfl

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
