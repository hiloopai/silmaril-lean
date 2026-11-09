module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Do16
import Mathlib.Tactic.Ring

/-!
# `adler32_z`: the last-chunk loop `0x2e3` from the `s2` update on

`exitC` (from `0x3a3`, after the read-modify-write of `s2`): back to `0x2e3` with one more
block, or after the last block either both reductions, the epilogue and the stop at `0x1f6`
(`rem % 16 = 0`) or the end pointer and the byte tail `0x3e0`. `tailC` prepends the
read-modify-write at `0x39e` (`rmw`). Both are stated for a variable offset `o` (with
`o = 931` resp. `926`) so that no elaboration or kernel check unfolds `wpN` at a literal
offset (see `Do16`).
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
theorem exitC (c : Ctx) (s : MState) (o k t : Nat) (ho : o = 931) (hF : Fr c s)
    (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o)
    (hr16 : 16 ≤ c.n - k) (hrem : c.n - k ≤ 5551) (hkn : k ≤ c.n) (ht : t ≤ (c.n - k - 16) / 16)
    (hrcx : s.core.read .rcx = c.p + BitVec.ofNat 64 (k + 16 * t))
    (hr15 : s.core.read .r15 = BitVec.ofNat 64 (c.R k (16 * t + 16)).1)
    (hA3' : loadN s.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.R k (16 * t + 16)).2))
    (h18' : loadN s.memory (c.sp + 18446744073709551592#64) 8 =
      some (c.p + BitVec.ofNat 64 (k + 16 * ((c.n - k - 16) / 16 + 1))))
    (h10' : loadN s.memory (c.sp + 18446744073709551600#64) 8 =
      some (BitVec.ofNat 64 ((c.n - k - 16) / 16)))
    (h08' : loadN s.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - k))) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (c.n - (k + 16 * t))) 60 o s := by
  subst ho
  have hP := hF.pre
  have hn := n_lt c
  have hq := Nat.div_mul_le_self (c.n - k - 16) 16
  have hpos : k + 16 * t + 16 ≤ c.n := by omega
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, hA3', h18', h10', h08', hr15, hrcx]
  have hq16 : 16 * ((c.n - k - 16) / 16) + 16 ≤ c.n - k := by omega
  have hpfit : c.p.toNat + (c.n - 1) < 2 ^ 64 := p_fit hP hF.nz (by omega)
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hne' : ¬ (c.p + (BitVec.ofNat 64 (k + 16 * t) + 16#64) =
        c.p + BitVec.ofNat 64 (k + 16 * ((c.n - k - 16) / 16 + 1))) := by simpa using hne
    have ht1 : t + 1 ≤ (c.n - k - 16) / 16 := by
      rcases Nat.lt_or_ge t ((c.n - k - 16) / 16) with h | h
      · exact h
      · exfalso; apply hne'; rw [p_add16 c, show k + 16 * t + 16 = k + 16 * ((c.n - k - 16) / 16 + 1) by omega]
    refine ⟨⟨hF.with rfl (by seg_read [hF.sp]), k, t + 1, hr16, hrem, hkn, ht1, ?_, ?_, ?_, h18', h10', h08'⟩, ?_⟩
    · seg_read [hrcx, p_add16 c]; rw [show k + 16 * t + 16 = k + 16 * (t + 1) by omega]
    · seg_read [hr15]; rw [show 16 * (t + 1) = 16 * t + 16 by omega]
    · rw [show 16 * (t + 1) = 16 * t + 16 by omega]; exact hA3'
    · simp only [meas]; seg_read [hrcx]
      rw [p_add16 c, p_sub c (by omega)]; omega
  · have heq' : c.p + (BitVec.ofNat 64 (k + 16 * t) + 16#64) =
        c.p + BitVec.ofNat 64 (k + 16 * ((c.n - k - 16) / 16 + 1)) := by simpa using heq
    rw [p_add16 c] at heq'
    have htq : t = (c.n - k - 16) / 16 := by
      have := p_add_inj (c := c) (by omega) (by omega) heq'; omega
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · have hz' : (c.n - k) % 16 = 0 := (and15 _ (by omega)).1 (by simpa using hz)
      have hfull : 16 * t + 16 = c.n - k := by omega
      have hb := R_lt c.bs c.a k (c.n - k) (by unfold NMAX; omega)
      have hb1 : (c.R k (c.n - k)).1 < 2 ^ 64 := by have := hb.1; unfold Ctx.R; omega
      have hb2 : (c.R k (c.n - k)).2 < 2 ^ 64 := by have := hb.2; unfold Ctx.R; omega
      have hR := R_final c (k := k) (by omega)
      simp only [hfull] at hA3' ⊢
      simp only [modWN _ hb1, modWN _ hb2, hR.1, hR.2]
      refine store_go hP hF.mem hF.saved (slot16 hP) (by decide) (fun m4 hF4 hS4 hL4 hA4 _ => ?_)
      simp only [hL4, true_and, hA4]
      obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hS4
      adler_vc [hrip, hl, hF.sp, Mem.ofReg, hA4, hL4, BlockCert9.popWord_eq,
        Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords, s0, s1, s2, s3, s4, s5]
      refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF4, ?_⟩ <;> seg_read [sp_48, pack_res c hF.nz]
    · have hnz' : (c.n - k) % 16 ≠ 0 := fun h0' => by
        simp at hnz
        exact hnz (by have := (and15 _ (by omega)).2 h0'; simpa using this)
      have hlt : k + 16 * t + 16 < c.n := by omega
      refine ⟨⟨hF.with rfl (by seg_read [hF.sp]), k, k + 16 * t + 16, by omega, hlt, hrem,
        ?_, ?_, ?_, ?_⟩, ?_⟩
      · seg_read []; rw [show k + 16 * ((c.n - k - 16) / 16 + 1) = k + 16 * t + 16 by omega]
      · seg_read []; exact rdx_eq c.p c.n k _ (by omega)
      · seg_read [hr15]; rw [show k + 16 * t + 16 - k = 16 * t + 16 by omega]
      · seg_read []; rw [show k + 16 * t + 16 - k = 16 * t + 16 by omega]
      · simp only [meas]; seg_read [hrcx]
        rw [show k + 16 * ((c.n - k - 16) / 16 + 1) = k + 16 * t + 16 by omega,
          p_sub c (by omega)]; omega

/-- `tailC`: the read-modify-write at `0x39e`, then `exitC`. -/
theorem tailC (c : Ctx) (s : MState) (o k t : Nat) (ho : o = 926) (hF : Fr c s)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o)
    (hr16 : 16 ≤ c.n - k) (hrem : c.n - k ≤ 5551) (hkn : k ≤ c.n) (ht : t ≤ (c.n - k - 16) / 16)
    (hrcx : s.core.read .rcx = c.p + BitVec.ofNat 64 (k + 16 * t))
    (hr15 : s.core.read .r15 = BitVec.ofNat 64 (c.R k (16 * t + 16)).1)
    (A q : Word) (hA : s.core.read .rax = A)
    (hq : loadN s.memory (c.sp + 18446744073709551584#64) 8 = some q)
    (hqA : q + A = BitVec.ofNat 64 (c.R k (16 * t + 16)).2)
    (h18 : loadN s.memory (c.sp + 18446744073709551592#64) 8 =
      some (c.p + BitVec.ofNat 64 (k + 16 * ((c.n - k - 16) / 16 + 1))))
    (h10 : loadN s.memory (c.sp + 18446744073709551600#64) 8 =
      some (BitVec.ofNat 64 ((c.n - k - 16) / 16)))
    (h08 : loadN s.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - k))) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (c.n - (k + 16 * t))) 61 o s := by
  have hP := hF.pre
  refine rmw c _ 60 o s A q (ho ▸ lk926) (by omega) (by subst ho; rfl) (by subst ho; rfl) hrip hF.sp
    hA hq (spill_perm hP hF.mem (slot16 hP) (by decide)) (fun after hst => ?_)
  obtain ⟨hF1, hS1, hL1, hA1, hD1⟩ := spill hP hF.mem hF.saved (slot16 hP) (by decide) hst
  rw [hqA] at hA1
  refine ⟨hL1, exitC c _ (o + 5) k t (by omega) (hF.withMem hF1 hS1 (by seg_read [hF.sp])) hL1
    (by seg_read []) hr16 hrem hkn ht (by seg_read [hrcx]) (by seg_read [hr15]) hA1
    (keep hD1 (slot16 hP) (slot24 hP) (by decide) h18) (keep hD1 (slot16 hP) (slot32 hP) (by decide) h10)
    (keep hD1 (slot16 hP) (slot40 hP) (by decide) h08)⟩

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
