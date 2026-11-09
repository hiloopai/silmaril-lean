module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Next

/-!
# `adler32_z`: the VC after the prologue (`0x20`)

The five ways out of the dispatch: `len = 1` (one byte, two conditional subtractions of
`BASE`, stop at `0x2b2`), a null buffer (stop at `0x462` with `1`), `len = 0` (stop at `0x274`),
`2 ≤ len ≤ 15` (the cut point `0x205`), `16 ≤ len ≤ 5551` (spills, the cut point `0x2e3`) and
`len ≥ 5552` (spills, the cut point `0x80`).
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
theorem vcP (c : Ctx) (s : MState) (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 32) (hI : InvP c s) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base (some (c.n + 1)) 60 32 s := by
  have hP := hI.pre
  have hrdx : s.core.read .rdx = BitVec.ofNat 64 c.n := by rw [hI.rdx]; simp [Ctx.n]
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hI.saved
  adler_vc [hrip, hl, hI.sp, Mem.ofReg, hrdx, hI.rsi, hI.rcx, hI.r15, hI.s2, BlockCert9.popWord_eq,
    Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords, s0, s1, s2, s3, s4, s5]
  refine ⟨fun h1 => ?_, fun h1 => ⟨fun hp0 => ?_, fun hp0 => ⟨fun hle15 => ⟨fun hz => ⟨fun hs1 => ?_, fun hs1 => ?_⟩, fun hz => ?_⟩, fun hgt15 => ⟨fun hle => ?_, fun hgt => ?_⟩⟩⟩⟩
  · have hn1 : c.n = 1 := by
      have := h1; simp only [beq_iff_eq] at this
      have := congrArg BitVec.toNat this; simp at this; have := n_lt c; omega
    have hpz : c.p.toNat ≠ 0 := fun h => hP.ok.2.2 h hn1
    have hb0 : loadN s.memory c.p 1 = some (c.b 0) := by
      simpa using load_buf hP hI.mem hpz (i := 0) (by omega)
    have hS0 := S_lt c.bs c.a 0
    have hbyte := (c.bs.getD 0 0).isLt
    have hS1 := S1_eq c (by omega)
    have hv1 : c.b 0 + BitVec.ofNat 64 (c.S 0).1 =
        BitVec.ofNat 64 ((c.S 0).1 + (c.bs.getD 0 0).toNat) := by
      rw [b_eq, BitVec.ofNat_add, BitVec.add_comm]
    have hV1 : (c.S 0).1 + (c.bs.getD 0 0).toNat < 2 * 65521 := by
      simp only [Ctx.S, BASE] at hS0 ⊢; omega
    have hv2 : BitVec.ofNat 64 (c.S 0).2 + BitVec.ofNat 64 (c.S 1).1 =
        BitVec.ofNat 64 ((c.S 0).2 + (c.S 1).1) := by rw [BitVec.ofNat_add]
    have hV2 : (c.S 0).2 + (c.S 1).1 < 2 * 65521 := by
      have := S_lt c.bs c.a 1; simp only [Ctx.S, BASE] at hS0 this ⊢; omega
    adler_vc [hrip, hl, hI.sp, Mem.ofReg, hrdx, hI.rsi, hI.rcx, hI.r15, hI.s2, BlockCert9.popWord_eq,
      Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords, s0, s1, s2, s3, s4, s5, hb0, zx_b, hv1]
    have fin : ∀ t : MState, t.core.read .rsp = c.sp + 48#64 → t.memory = s.memory →
        t.core.read .rbx = c.m0.core.read .rbx → t.core.read .rbp = c.m0.core.read .rbp →
        t.core.read .r12 = c.m0.core.read .r12 → t.core.read .r13 = c.m0.core.read .r13 →
        t.core.read .r14 = c.m0.core.read .r14 → t.core.read .r15 = c.m0.core.read .r15 →
        t.core.read .rax = (BitVec.ofNat 64 (c.S 1).2 <<< 16) ||| BitVec.ofNat 64 (c.S 1).1 →
        Q c t := fun t a1 a2 a3 a4 a5 a6 a7 a8 a9 => by
      have := pack_res c hpz; rw [hn1] at this
      exact ⟨hP, a1.trans (sp_48 c), a3, a4, a5, a6, a7, a8, a2 ▸ hI.mem, a9.trans this⟩
    refine ⟨fun c1 => ?_, fun c1 => ?_⟩
    · have e1 := cs_le (by omega) c1
      rw [← hS1.1] at e1
      simp only [e1, hv2]
      refine ⟨fun c2 => ?_, fun c2 => ?_⟩
      · have e2 := cs_le (by omega) c2
        rw [← hS1.2] at e2
        simp only [e2]
        apply fin <;> seg_read []
      · have e2 := cs_gt hV2 c2
        rw [← hS1.2] at e2
        simp only [e2]
        apply fin <;> seg_read []
    · have e1 := cs_gt hV1 c1
      rw [← hS1.1] at e1
      simp only [e1, hv2]
      refine ⟨fun c2 => ?_, fun c2 => ?_⟩
      · have e2 := cs_le (by omega) c2
        rw [← hS1.2] at e2
        simp only [e2]
        apply fin <;> seg_read []
      · have e2 := cs_gt hV2 c2
        rw [← hS1.2] at e2
        simp only [e2]
        apply fin <;> seg_read []
  · -- buf = 0
    have hpz : c.p.toNat = 0 := by
      have := hp0; simp only [BitVec.and_self, beq_iff_eq] at this; simp [this]
    refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.mem, ?_⟩ <;> seg_read [sp_48]
    simp [Ctx.res, hpz]
  · -- len = 0, s1 reduced
    have hn0 : c.n = 0 := by
      have := hz; simp only [BitVec.and_self, beq_iff_eq] at this
      have := congrArg BitVec.toNat this; simp at this; have := n_lt c; omega
    have hpz : c.p.toNat ≠ 0 := by
      intro h; apply absurd hp0; simp [show c.p = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h)]
    have hS0 := S_lt c.bs c.a 0
    have hm2 : (c.S 0).2 < 2 ^ 64 := by simp only [Ctx.S, BASE] at hS0 ⊢; omega
    have e2 := modWN _ hm2
    rw [Nat.mod_eq_of_lt (show (c.S 0).2 < 65521 by simpa [Ctx.S, BASE] using hS0.2)] at e2
    simp only [e2]
    refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.mem, ?_⟩ <;> seg_read [sp_48]
    have := pack_res c hpz; rw [hn0] at this; exact this
  · exfalso
    have hS0 := S_lt c.bs c.a 0
    have := cs_le (v := (c.S 0).1) (by simp only [Ctx.S, BASE] at hS0 ⊢; omega)
    have h' : ¬ (BitVec.ofNat 64 (c.S 0).1).toNat ≤ (65520#64).toNat := by simpa [BitVec.ule] using hs1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [Ctx.S, BASE] at hS0 ⊢; omega)] at h'
    simp only [Ctx.S, BASE] at hS0 h'; simp at h'; omega
  · have hpz : c.p.toNat ≠ 0 := by
      intro h; apply absurd hp0; simp [show c.p = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h)]
    have hnn := n_lt c
    have hn0 : c.n ≠ 0 := by
      intro h; apply absurd hz; simp [h]
    have hn1 : c.n ≠ 1 := by
      intro h; apply absurd h1; simp [h]
    have hn15 : c.n ≤ 15 := by
      have h' : (BitVec.ofNat 64 c.n).toNat ≤ (15#64).toNat := by simpa [BitVec.ule] using hle15
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn] at h'; simpa using h'
    refine ⟨⟨⟨hP, by seg_read [hI.sp], hI.mem, hI.saved, hpz⟩, by omega, hn15, 0, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read [hI.rcx]; simp
    · seg_read []
    · seg_read [hI.r15]; rw [show c.R 0 0 = c.S 0 from R_zero _ _ _]
    · seg_read []; rw [show c.R 0 0 = c.S 0 from R_zero _ _ _]
    · simp only [meas]; seg_read [hI.rcx]; simp
  · -- 16 ≤ len ≤ 5551: to the last-chunk loop
    have hpz : c.p.toNat ≠ 0 := by
      intro h; apply absurd hp0; simp [show c.p = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h)]
    have hnn := n_lt c
    have h16 : 16 ≤ c.n := by
      have h' : ¬ (BitVec.ofNat 64 c.n).toNat ≤ (15#64).toNat := by simpa [BitVec.ule] using hgt15
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn] at h'; simp at h'; omega
    have hle' : c.n ≤ 5551 := by
      have h' : (BitVec.ofNat 64 c.n).toNat ≤ (5551#64).toNat := by simpa [BitVec.ule] using hle
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn] at h'; simpa using h'
    simp only [qm_eq _ h16 hnn, q1_eq _ h16 hnn]
    refine store_go hP hI.mem hI.saved (slot40 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 hD1 => ?_)
    simp only [hL1, true_and]
    refine store_go hP hF1 hS1 (slot32 hP) (by decide) (fun m2 hF2 hS2 hL2 hA2 hD2 => ?_)
    simp only [hL2, true_and]
    refine store_go hP hF2 hS2 (slot24 hP) (by decide) (fun m3 hF3 hS3 hL3 hA3 hD3 => ?_)
    simp only [hL3, true_and]
    have k16 := keep hD3 (slot24 hP) (slot16 hP) (by decide) (keep hD2 (slot32 hP) (slot16 hP)
      (by decide) (keep hD1 (slot40 hP) (slot16 hP) (by decide) hI.s2))
    have k32 := keep hD3 (slot24 hP) (slot32 hP) (by decide) hA2
    have k40 := keep hD3 (slot24 hP) (slot40 hP) (by decide) (keep hD2 (slot32 hP) (slot40 hP)
      (by decide) hA1)
    refine ⟨⟨⟨hP, by seg_read [hI.sp], hF3, hS3, hpz⟩, 0, 0, by omega, by omega, by omega, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · seg_read [hI.rcx]; simp
    · seg_read [hI.r15]; rw [show c.R 0 (16 * 0) = c.S 0 from R_zero _ _ _]
    · rw [show c.R 0 (16 * 0) = c.S 0 from R_zero _ _ _]; exact k16
    · simpa using hA3
    · simpa using k32
    · simpa using k40
    · simp only [meas]; seg_read [hI.rcx]; simp
  · -- len ≥ 5552: to the NMAX chunk loop
    have hpz : c.p.toNat ≠ 0 := by
      intro h; apply absurd hp0; simp [show c.p = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h)]
    have hnn := n_lt c
    have hbig : 5552 ≤ c.n := by
      have h' : ¬ (BitVec.ofNat 64 c.n).toNat ≤ (5551#64).toNat := by simpa [BitVec.ule] using hgt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn] at h'; simp at h'; omega
    refine store_go hP hI.mem hI.saved (slot24 hP) (by decide) (fun m1 hF1 hS1 hL1 hA1 hD1 => ?_)
    simp only [hL1, true_and]
    refine store_go hP hF1 hS1 (slot40 hP) (by decide) (fun m2 hF2 hS2 hL2 hA2 hD2 => ?_)
    simp only [hL2, true_and]
    have k24 := keep hD2 (slot40 hP) (slot24 hP) (by decide) hA1
    adler_vc [hrip, hl, hI.sp, Mem.ofReg, hL2, k24]
    refine store_go hP hF2 hS2 (slot32 hP) (by decide) (fun m3 hF3 hS3 hL3 hA3 hD3 => ?_)
    simp only [hL3, true_and]
    have k16 := keep hD3 (slot32 hP) (slot16 hP) (by decide) (keep hD2 (slot40 hP) (slot16 hP)
      (by decide) (keep hD1 (slot24 hP) (slot16 hP) (by decide) hI.s2))
    have k24' := keep hD3 (slot32 hP) (slot24 hP) (by decide) k24
    have k40 := keep hD3 (slot32 hP) (slot40 hP) (by decide) hA2
    have e32 : BitVec.ofNat 64 c.n - 5552#64 = BitVec.ofNat 64 (c.n - 0 - NMAX) := by
      rw [show c.n - 0 - NMAX = c.n - 5552 from rfl]
      rw [show (5552#64 : Word) = BitVec.ofNat 64 5552 from rfl, show c.n = (c.n - 5552) + 5552 from by omega,
        BitVec.ofNat_add]
      simp
    rw [e32] at hA3
    refine ⟨⟨⟨hP, by seg_read [hI.sp], hF3, hS3, hpz⟩, 0, 0, by unfold NMAX; omega, by unfold NMAX; omega,
      by decide, ?_, ?_, ?_, ?_, hA3, ?_⟩, ?_⟩
    · seg_read [hI.rcx]; simp
    · seg_read [hI.r15]; rw [show c.R 0 0 = c.S 0 from R_zero _ _ _]
    · rw [show c.R 0 0 = c.S 0 from R_zero _ _ _]; exact k16
    · simpa [NMAX] using k24'
    · simpa using k40
    · simp only [meas]; seg_read [hI.rcx]; simp

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
