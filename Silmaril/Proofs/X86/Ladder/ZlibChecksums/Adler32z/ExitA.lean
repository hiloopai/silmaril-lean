module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Do16
import Mathlib.Tactic.Ring

/-!
# `adler32_z`: the `NMAX` chunk loop `0x80` from the `s2` update on

`exitA1` (from `0x14b`, after the read-modify-write of `s2`): back to `0x80` with one more block,
or at the chunk end both reductions (`modWN'`) and the spills of the new sums and end pointer,
stopping at `0x1c5` with a variable path budget. `exitA2` (from `0x1c5`): the four ways out of
a finished chunk. Offsets are variables (see `Do16`).
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
theorem exitA1 (c : Ctx) (s : MState) (K k j o0 o1 : Nat) (h0 : o0 = 331) (h1 : o1 = 453)
    (hF : Fr c s)
    (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o0)
    (hkn : k + NMAX ≤ c.n) (hj : j < NMAX) (hj16 : j % 16 = 0)
    (hr8 : s.core.read .r8 = c.p + BitVec.ofNat 64 (k + j + 16))
    (hr15 : s.core.read .r15 = BitVec.ofNat 64 (c.R k (j + 16)).1)
    (h20 : loadN s.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.R k (j + 16)).2))
    (h18 : loadN s.memory (c.sp + 18446744073709551592#64) 8 = some (c.p + BitVec.ofNat 64 (k + NMAX)))
    (h10 : loadN s.memory (c.sp + 18446744073709551600#64) 8 = some (BitVec.ofNat 64 (c.n - k - NMAX)))
    (h08 : loadN s.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - k)))
    (hk : ∀ t : MState, Fr c t → Loaded t.memory c.base adler32zCode →
      t.core.rip = c.base + BitVec.ofNat 64 o1 →
      t.core.read .r8 = c.p + BitVec.ofNat 64 (k + NMAX) →
      t.core.read .rcx = c.p + BitVec.ofNat 64 (k + NMAX) →
      t.core.read .rsi = BitVec.ofNat 64 (c.n - k - NMAX) →
      t.core.read .r15 = BitVec.ofNat 64 (c.S (k + NMAX)).1 →
      loadN t.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.S (k + NMAX)).2) →
      loadN t.memory (c.sp + 18446744073709551592#64) 8 = some (c.p + BitVec.ofNat 64 (k + NMAX + NMAX)) →
      loadN t.memory (c.sp + 18446744073709551600#64) 8 = some (BitVec.ofNat 64 (c.n - k - NMAX)) →
      loadN t.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - k)) →
      wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
        (some (c.n - (k + j))) K o1 t) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (c.n - (k + j))) (K + 27) o0 s := by
  subst h0 h1
  have hP := hF.pre
  have hn := n_lt c
  have hpfit : c.p.toNat + (c.n - 1) < 2 ^ 64 := p_fit hP hF.nz (by unfold NMAX at hkn; omega)
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, h20, h18, h10, h08, hr15, hr8]
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hne' : ¬ (c.p + BitVec.ofNat 64 (k + j + 16) = c.p + BitVec.ofNat 64 (k + NMAX)) := by
      simpa using hne
    have hj1 : j + 16 < NMAX := by
      rcases Nat.lt_or_ge (j + 16) NMAX with h | h
      · exact h
      · exfalso; apply hne'; unfold NMAX at *
        rw [show k + j + 16 = k + 5552 by omega]
    refine ⟨⟨hF.with rfl (by seg_read [hF.sp]), k, j + 16, hkn, hj1, by omega, ?_, ?_, ?_, h18, h10, h08⟩, ?_⟩
    · seg_read [hr8]; rw [Nat.add_assoc]
    · seg_read [hr15]
    · exact h20
    · simp only [meas]; seg_read [hr8]
      unfold NMAX at *
      rw [p_sub c (by omega)]; omega
  · have heq' : c.p + BitVec.ofNat 64 (k + j + 16) = c.p + BitVec.ofNat 64 (k + NMAX) := by
      simpa using heq
    have hjN : j + 16 = NMAX := by
      have := p_add_inj (c := c) (by unfold NMAX at *; omega) (by unfold NMAX at *; omega) heq'
      omega
    have hb := R_lt c.bs c.a k NMAX (le_refl _)
    have hb1 : (c.R k NMAX).1 < 2 ^ 64 := by have := hb.1; unfold Ctx.R; omega
    have hb2 : (c.R k NMAX).2 < 2 ^ 64 := by have := hb.2; unfold Ctx.R; omega
    rw [hjN] at hr15 h20 ⊢
    simp only [hjN, modWN' _ hb1, modWN' _ hb2, red_R1, red_R2]
    refine store_go hP hF.mem hF.saved (slot16 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 hD1 => ?_)
    simp only [hL1, true_and]
    refine store_go hP hF1 hS1 (slot24 hP) (by decide) (fun m2 hF2 hS2 hL2 hA2 hD2 => ?_)
    simp only [hL2, true_and]
    have e24 : c.p + (BitVec.ofNat 64 (k + j + 16) + 5552#64) = c.p + BitVec.ofNat 64 (k + NMAX + NMAX) := by
      rw [show (5552#64 : Word) = BitVec.ofNat 64 5552 from rfl, p_addL]; unfold NMAX at *
      rw [show k + j + 16 + 5552 = k + 5552 + 5552 by omega]
    rw [e24] at hA2
    apply hk _ (hF.withMem hF2 hS2 (by seg_read [hF.sp])) hL2
    · seg_read [Silmaril.X86.State.write_rip]
    · seg_read [hr8]; unfold NMAX at *; rw [show k + j + 16 = k + 5552 by omega]
    · seg_read [h18]
    · seg_read []
    · seg_read []
    · exact keep hD2 (slot24 hP) (slot16 hP) (by decide) hA1
    · exact hA2
    · exact keep hD2 (slot24 hP) (slot32 hP) (by decide) (keep hD1 (slot16 hP) (slot32 hP) (by decide) h10)
    · exact keep hD2 (slot24 hP) (slot40 hP) (by decide) (keep hD1 (slot16 hP) (slot40 hP) (by decide) h08)

set_option maxHeartbeats 40000000 in
/-- `0x1c5`: the next chunk (`0x59`, back to `0x80`), the end (`rem = 0`, stop at `0x1f6`), the
byte tail (`rem ≤ 15`, via `0x463` to `0x3e0`) or the last-chunk loop (via `0x2b3` to
`0x2e3`). -/
theorem exitA2 (c : Ctx) (s : MState) (kk m o : Nat) (ho : o = 453) (hF : Fr c s)
    (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o)
    (hkk : kk ≤ c.n) (hkN : NMAX ≤ kk) (hm : c.n - kk < m)
    (hr8 : s.core.read .r8 = c.p + BitVec.ofNat 64 kk)
    (hrcx : s.core.read .rcx = c.p + BitVec.ofNat 64 kk)
    (hrsi : s.core.read .rsi = BitVec.ofNat 64 (c.n - kk))
    (hr15 : s.core.read .r15 = BitVec.ofNat 64 (c.S kk).1)
    (h20 : loadN s.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.S kk).2))
    (h18 : loadN s.memory (c.sp + 18446744073709551592#64) 8 = some (c.p + BitVec.ofNat 64 (kk + NMAX)))
    (h10 : loadN s.memory (c.sp + 18446744073709551600#64) 8 = some (BitVec.ofNat 64 (c.n - kk)))
    (h08 : loadN s.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - kk + NMAX))) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base (some m) 30 o s := by
  subst ho
  have hP := hF.pre
  have hn := n_lt c
  have hS := hF.saved
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hF.saved
  unfold NMAX at *
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, h20, h18, h10, h08, hr15, hr8, hrcx, hrsi, BlockCert9.popWord_eq,
    Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords, s0, s1, s2, s3, s4, s5]
  have hR0 : c.R kk 0 = c.S kk := R_zero _ _ _
  refine ⟨fun hgt => ?_, fun hle => ⟨fun hnz => ⟨fun h15 => ?_, fun h16 => ?_⟩, fun hz => ?_⟩⟩
  · -- another full chunk: back to `0x80`
    have hbig : 5552 ≤ c.n - kk := by
      have h' : ¬ (BitVec.ofNat 64 (c.n - kk)).toNat ≤ (5551#64).toNat := by simpa [BitVec.ule] using hgt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'; simp at h'; omega
    refine store_go hP hF.mem hS (slot40 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 hD1 => ?_)
    simp only [hL1, true_and]
    have k24 := keep hD1 (slot40 hP) (slot24 hP) (by decide) h18
    adler_vc [hrip, hl, hF.sp, Mem.ofReg, hL1, k24]
    refine store_go hP hF1 hS1 (slot32 hP) (by decide) (fun m2 hF2 hS2 hL2 hA2 hD2 => ?_)
    simp only [hL2, true_and]
    have k16 := keep hD2 (slot32 hP) (slot16 hP) (by decide) (keep hD1 (slot40 hP) (slot16 hP) (by decide) h20)
    have k24' := keep hD2 (slot32 hP) (slot24 hP) (by decide) k24
    have k40 := keep hD2 (slot32 hP) (slot40 hP) (by decide) hA1
    have e32 : BitVec.ofNat 64 (c.n - kk) - 5552#64 = BitVec.ofNat 64 (c.n - kk - 5552) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [e32] at hA2
    refine ⟨⟨⟨hP, by seg_read [hF.sp], hF2, hS2, hF.nz⟩, kk, 0, by unfold NMAX; omega, by unfold NMAX; omega,
      by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read []; rw [subNMAX]; simp
    · seg_read [hr15, hR0]
    · rw [hR0]; exact k16
    · simpa [NMAX] using k24'
    · simpa [NMAX, Nat.sub_sub] using hA2
    · simpa [NMAX] using k40
    · simp only [meas]; seg_read []; rw [subNMAX, p_sub c (by omega)]; omega
  · -- `1 ≤ rem ≤ 15`: to the byte tail
    have hnz' : c.n - kk ≠ 0 := by
      intro h0; rw [h0] at hnz; simp at hnz
    have hle15 : c.n - kk ≤ 15 := by
      have h' : (BitVec.ofNat 64 (c.n - kk)).toNat ≤ (15#64).toNat := by simpa [BitVec.ule] using h15
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'; simpa using h'
    refine ⟨⟨hF.with rfl (by seg_read [hF.sp]), kk, kk, le_refl _, by omega, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read [hr8]
    · seg_read []; exact rdxA c c.n kk hkk
    · seg_read [hr15]; simp [hR0]
    · seg_read []; simp [hR0]
    · simp only [meas]; seg_read [hr8]; rw [p_sub c (by omega)]; omega
  · -- `16 ≤ rem ≤ 5551`: to the last-chunk loop
    have hnn : c.n - kk < 2 ^ 64 := by omega
    have h16' : 16 ≤ c.n - kk := by
      have h' : ¬ (BitVec.ofNat 64 (c.n - kk)).toNat ≤ (15#64).toNat := by simpa [BitVec.ule] using h16
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn] at h'; simp at h'; omega
    have hle' : c.n - kk ≤ 5551 := by
      have h' : (BitVec.ofNat 64 (c.n - kk)).toNat ≤ (5551#64).toNat := by
        simpa [BitVec.ule] using hle
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn] at h'; simpa using h'
    simp only [qm_eq _ h16' hnn, q1_eq _ h16' hnn]
    refine store_go hP hF.mem hS (slot40 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 hD1 => ?_)
    simp only [hL1, true_and]
    refine store_go hP hF1 hS1 (slot32 hP) (by decide) (fun m2 hF2 hS2 hL2 hA2 hD2 => ?_)
    simp only [hL2, true_and]
    refine store_go hP hF2 hS2 (slot24 hP) (by decide) (fun m3 hF3 hS3 hL3 hA3 hD3 => ?_)
    simp only [hL3, true_and]
    have k16 := keep hD3 (slot24 hP) (slot16 hP) (by decide) (keep hD2 (slot32 hP) (slot16 hP)
      (by decide) (keep hD1 (slot40 hP) (slot16 hP) (by decide) h20))
    have k32 := keep hD3 (slot24 hP) (slot32 hP) (by decide) hA2
    have k40 := keep hD3 (slot24 hP) (slot40 hP) (by decide) (keep hD2 (slot32 hP) (slot40 hP)
      (by decide) hA1)
    refine ⟨⟨⟨hP, by seg_read [hF.sp], hF3, hS3, hF.nz⟩, kk, 0, h16', hle', hkk, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read [hrcx]; simp
    · seg_read [hr15]; simp [hR0]
    · simp only [Nat.mul_zero, hR0]; exact k16
    · rw [← BitVec.ofNat_add] at hA3; simpa using hA3
    · simpa using k32
    · simpa using k40
    · simp only [meas]; seg_read [hrcx]; rw [p_sub c (by omega)]; omega
  · -- `rem = 0`: the end
    have hz' : c.n = kk := by
      have := hz; simp only [BitVec.and_self, beq_iff_eq, Bool.not_eq_false'] at this
      have := congrArg BitVec.toNat this; simp at this; omega
    subst hz'
    refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF.mem, ?_⟩ <;> seg_read [sp_48]
    exact pack_res c hF.nz

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
