module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Next

/-!
# `adler32_z`: the VC of the short byte loop `0x205` (`2 ≤ len ≤ 15`)

The byte step and back to `0x205`; at the end the spill of `s2`, the conditional subtraction
of `BASE` from `s1` (both branches), the multiply-high reduction of `s2`, the pops, and the
stop at the `ret` `0x274` with `Q`.
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
theorem vcB (c : Ctx) (s : MState) (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 517) (hI : InvB c s) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (meas c .rcx s)) 60 517 s := by
  obtain ⟨hF, hn2, hn15, i, hin, hrcx, hrdx, hr15, hrax⟩ := hI
  have hP := hF.pre
  have h0 : loadN s.memory (s.core.read .rcx) 1 = some (c.b i) := by
    simpa using load_buf_off hP hF.mem hF.nz hrcx 0 (by omega)
  have hn := n_lt c
  have hstep := R_succW c (k := 0) (j := i) (by omega)
  simp only [Nat.zero_add] at hstep
  have e1 := hstep.1.symm
  have e2 : BitVec.ofNat 64 (c.R 0 i).2 + BitVec.ofNat 64 (c.R 0 (i + 1)).1 =
      BitVec.ofNat 64 (c.R 0 (i + 1)).2 := by rw [hstep.2, hstep.1]
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, h0, zx_b, hr15, hrax, e1, e2]
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hne' : s.core.read .rcx + 1#64 ≠ s.core.read .rdx := by simpa using hne
    have hlt : i + 1 < c.n := by
      rcases Nat.lt_or_ge (i + 1) c.n with h | h
      · exact h
      · exfalso; apply hne'; rw [hrcx, hrdx, BitVec.add_assoc, ← BitVec.ofNat_add,
          show i + 1 = c.n by omega]
    refine ⟨⟨hF.with rfl (by seg_read [hF.sp]), hn2, hn15, i + 1, hlt, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read [hrcx]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    · seg_read [hrdx]
    · seg_read []
    · seg_read []
    · simp only [meas]; seg_read [hrcx]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, p_sub c (by omega), p_sub c (by omega)]; omega
  · have heq' : s.core.read .rcx + 1#64 = s.core.read .rdx := by simpa using heq
    have hend : i + 1 = c.n := by
      rw [hrcx, hrdx, BitVec.add_assoc, ← BitVec.ofNat_add] at heq'
      exact p_add_inj (by omega) hn heq'
    have hRf := R_final c (k := 0) (by omega)
    simp only [Nat.sub_zero] at hRf
    have hb1 : (c.R 0 c.n).1 ≤ (c.S 0).1 + 255 * c.n := R1_le c.bs c.a 0 c.n
    have hS0 : (c.S 0).1 < 65521 := (S_lt c.bs c.a 0).1
    have hb : (c.R 0 c.n).1 < 2 ^ 32 ∧ (c.R 0 c.n).2 < 2 ^ 32 :=
      R_lt c.bs c.a 0 c.n (by unfold NMAX; omega)
    have hb2 : (c.R 0 c.n).2 < 2 ^ 64 := by omega
    have hv : (c.R 0 c.n).1 < 2 * 65521 := by omega
    simp only [hend]
    refine store_go hP hF.mem hF.saved (slot16 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 _ => ?_)
    simp only [hL1, true_and]
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hS1
    refine ⟨fun hle => ?_, fun hgt => ?_⟩
    · have hle' : (c.R 0 c.n).1 ≤ 65520 := by
        have h' : (BitVec.ofNat 64 (c.R 0 c.n).1).toNat ≤ (65520#64).toNat := by
          simpa [BitVec.ule] using hle
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'; simpa using h'
      have e3 : BitVec.ofNat 64 (c.R 0 c.n).1 = BitVec.ofNat 64 (c.S c.n).1 := by
        rw [← hRf.1, Nat.mod_eq_of_lt (by omega)]
      adler_vc [hrip, hl, hF.sp, Mem.ofReg, hA1, hL1, modWN _ hb2, hRf.2, e3,
        BlockCert9.popWord_eq, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords,
        s0, s1, s2, s3, s4, s5]
      refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF1, ?_⟩ <;> seg_read [sp_48, pack_res c hF.nz]
    · have hgt' : 65520 < (c.R 0 c.n).1 := by
        have h' : ¬ (BitVec.ofNat 64 (c.R 0 c.n).1).toNat ≤ (65520#64).toNat := by
          simpa [BitVec.ule] using hgt
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'; simp at h'; omega
      have e4 : BitVec.ofNat 64 (c.R 0 c.n).1 - 65521#64 = BitVec.ofNat 64 (c.S c.n).1 := by
        rw [← hRf.1]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      adler_vc [hrip, hl, hF.sp, Mem.ofReg, hA1, hL1, modWN _ hb2, hRf.2, e4,
        BlockCert9.popWord_eq, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords,
        s0, s1, s2, s3, s4, s5]
      refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF1, ?_⟩ <;> seg_read [sp_48, pack_res c hF.nz]

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
