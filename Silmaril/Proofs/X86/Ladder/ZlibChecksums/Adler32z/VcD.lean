module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Next

/-!
# `adler32_z`: the VC of the byte tail `0x3e0`

From the tail loop head: the byte step and back to `0x3e0`, or at the end of the buffer
the store of `s2`, the two reductions (`modWN`), the store of the reduced `s2`, the jump to
the epilogue `0x1e0`, the six pops, and the stop at the `ret` `0x1f6` with `Q`.
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

set_option maxHeartbeats 40000000 in
theorem vcD (c : Ctx) (s : MState) (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 992) (hI : InvD c s) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (meas c .r8 s)) 60 992 s := by
  obtain ⟨hF, k, pos, hkp, hpn, hrem, hr8, hrdx, hr15, hrax⟩ := hI
  have hP := hF.pre
  have h0 : loadN s.memory (s.core.read .r8) 1 = some (c.b pos) := by
    simpa using load_buf_off hP hF.mem hF.nz hr8 0 (by omega)
  have hn := n_lt c
  have hstep := R_succW c (k := k) (j := pos - k) (by omega)
  rw [show k + (pos - k) = pos by omega, show pos - k + 1 = pos + 1 - k by omega] at hstep
  have e1 := hstep.1.symm
  have e2 : BitVec.ofNat 64 (c.R k (pos - k)).2 + BitVec.ofNat 64 (c.R k (pos + 1 - k)).1 =
      BitVec.ofNat 64 (c.R k (pos + 1 - k)).2 := by rw [hstep.2, hstep.1]
  have hb := R_lt c.bs c.a k (pos + 1 - k) (by unfold NMAX; omega)
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, h0, zx_b, hr15, hrax, e1, e2]
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hne' : s.core.read .r8 + 1#64 ≠ s.core.read .rdx := by simpa using hne
    have hlt : pos + 1 < c.n := by
      rcases Nat.lt_or_ge (pos + 1) c.n with h | h
      · exact h
      · exfalso; apply hne'; rw [hr8, hrdx, BitVec.add_assoc, ← BitVec.ofNat_add,
          show pos + 1 = c.n by omega]
    refine ⟨⟨hF.with rfl (by seg_read [hF.sp]), k, pos + 1, by omega, hlt, hrem, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read [hr8]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    · seg_read [hrdx]
    · seg_read []
    · seg_read []
    · simp only [meas]; seg_read [hr8]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, p_sub c (by omega), p_sub c (by omega)]; omega
  · have heq' : s.core.read .r8 + 1#64 = s.core.read .rdx := by simpa using heq
    have hend : pos + 1 = c.n := by
      rw [hr8, hrdx, BitVec.add_assoc, ← BitVec.ofNat_add] at heq'
      exact p_add_inj (by omega) hn heq'
    rw [hend] at hb
    have hR := R_final c (k := k) (by omega)
    have hb1 : (c.R k (c.n - k)).1 < 2 ^ 64 := by have := hb.1; unfold Ctx.R; omega
    have hb2 : (c.R k (c.n - k)).2 < 2 ^ 64 := by have := hb.2; unfold Ctx.R; omega
    simp only [hend]
    refine store_go hP hF.mem hF.saved (slot16 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 _ => ?_)
    simp only [hL1, true_and, hA1]
    adler_vc [hrip, hl, hF.sp, Mem.ofReg, hA1, hL1, modWN _ hb1, modWN _ hb2, hR.1, hR.2]
    refine store_go hP hF1 hS1 (slot16 hP) (by decide) (fun m2 hF2 hS2 hL2 hA2 _ => ?_)
    simp only [hL2, true_and, hA2]
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hS2
    adler_vc [hrip, hl, hF.sp, Mem.ofReg, hA2, hL2, BlockCert9.popWord_eq,
      Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords, s0, s1, s2, s3, s4, s5]
    refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF2, ?_⟩ <;> seg_read [sp_48, pack_res c hF.nz]

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
