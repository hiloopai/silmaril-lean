module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.BodyA
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.ExitA
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Total

/-!
# `adler32_z`: the VC of the `NMAX` chunk loop `0x80`

One `DO16` block (`a1`, `a2`, `a3` over abstract bytes `x j = c.b (k + j + i)`), the
read-modify-write of `s2` at `0x146` (`rmw`), then `exitA1` (back to `0x80`, or the chunk-end
reductions up to `0x1c5`) and `exitA2` (the four ways out of a finished chunk). The offsets
inside the composition are variables (see `Do16`).
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

/-- **The VC of the `NMAX` chunk loop `0x80`.** -/
theorem vcA (c : Ctx) (s : MState) (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 128) (hI : InvA c s) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (meas c .r8 s)) 110 128 s := by
  obtain ⟨hF, k, j, hkn, hj, hj16, hr8, hr15, h20, h18, h10, h08⟩ := hI
  have hP := hF.pre
  have hn := n_lt c
  have hj1 : j + 16 ≤ NMAX := by unfold NMAX at *; omega
  have hpos : k + j + 16 ≤ c.n := by omega
  have hpfit : c.p.toNat + (c.n - 1) < 2 ^ 64 := p_fit hP hF.nz (by unfold NMAX at *; omega)
  have hmeas : meas c .r8 s = c.n - (k + j) := by
    simp only [meas]; rw [hr8, p_sub c (by omega)]
  rw [hmeas]
  generalize h128 : (128 : Nat) = o0 at hrip ⊢
  obtain ⟨o1, h1⟩ : ∃ o, o = 183 := ⟨_, rfl⟩
  obtain ⟨o2, h2⟩ : ∃ o, o = 239 := ⟨_, rfl⟩
  obtain ⟨o3, h3⟩ : ∃ o, o = 326 := ⟨_, rfl⟩
  obtain ⟨o4, h4⟩ : ∃ o, o = 453 := ⟨_, rfl⟩
  have hR16 := R16W c (k := k) (j := j) (by omega)
  have hx : ∀ mem, FM c mem → ∀ i, i < 16 →
      loadN mem (c.p + BitVec.ofNat 64 (k + j) + BitVec.ofNat 64 i) 1 = some (c.b (k + j + i)) :=
    fun mem hFm i hi => load_buf_off hP hFm hF.nz rfl i (by omega)
  have hz : ∀ i, (((c.b (k + j + i)).setWidth 8).setWidth 32).setWidth 64 = c.b (k + j + i) :=
    fun i => zx_b c _
  have hx' := hx _ hF.mem
  refine a1 c 97 _ s o0 o1 h128.symm h1 hl _ hr8 (fun i => c.b (k + j + i)) _ hx' hz hrip hr15
    (fun t1 hm1 hsp1 hrip1 hX1 a1' a2' a3' a4' a5' a6' a7' => ?_)
  have hl1 : Loaded t1.memory c.base adler32zCode := hm1 ▸ hl
  have hx1 := hm1 ▸ hx'
  refine a2 c 82 _ t1 o1 o2 h1 h2 hl1 _ hX1 _ _ hx1 hz hrip1 a1' a2' a3' a4' a5' a6' a7'
    (fun t2 hm2 hsp2 hrip2 hX2 b1 b2 b3 b4 b5 b6 b7 => ?_)
  have hm : t2.memory = s.memory := hm2.trans hm1
  have hF2 : Fr c t2 := hF.with hm (by rw [hsp2, hsp1, hF.sp])
  refine a3 c 58 _ t2 o2 o3 h2 h3 hF2 hrip2 _ hX2 _ hx hz _ b1 b2 b3 b4 b5 b6 b7
    (fun t3 hF3 hl3 hrip3 hX3 e1 e2 k16 k24 k32 k40 => ?_)
  rw [hm] at k16 k24 k32 k40
  rw [pre16] at e1
  rw [tri16] at e2
  have hP3 := hF3.pre
  refine rmw c _ 57 o3 t3 _ _ (h3 ▸ lk326) (by omega) (by subst h3; rfl) (by subst h3; rfl) hrip3
    hF3.sp e2 (k16.trans h20) (spill_perm hP3 hF3.mem (slot16 hP3) (by decide))
    (fun after hst => ?_)
  obtain ⟨hF4, hS4, hL4, hA4, hD4⟩ := spill hP3 hF3.mem hF3.saved (slot16 hP3) (by decide) hst
  have hq : BitVec.ofNat 64 (c.R k j).2 + (16 * BitVec.ofNat 64 (c.R k j).1 + 16 * c.b (k + j + 0) +
      15 * c.b (k + j + 1) + 14 * c.b (k + j + 2) + 13 * c.b (k + j + 3) + 12 * c.b (k + j + 4) +
      11 * c.b (k + j + 5) + 10 * c.b (k + j + 6) + 9 * c.b (k + j + 7) + 8 * c.b (k + j + 8) +
      7 * c.b (k + j + 9) + 6 * c.b (k + j + 10) + 5 * c.b (k + j + 11) + 4 * c.b (k + j + 12) +
      3 * c.b (k + j + 13) + 2 * c.b (k + j + 14) + 1 * c.b (k + j + 15)) =
      BitVec.ofNat 64 (c.R k (j + 16)).2 := by
    rw [hR16.2]
    exact add17 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hq] at hA4
  refine ⟨hL4, exitA1 c _ 30 k j (o3 + 5) o4 (by omega) h4
    (hF3.withMem hF4 hS4 (by seg_read [hF3.sp])) hL4 rfl hkn hj hj16 ?_ ?_ hA4
    (keep hD4 (slot16 hP3) (slot24 hP3) (by decide) (k24.trans h18))
    (keep hD4 (slot16 hP3) (slot32 hP3) (by decide) (k32.trans h10))
    (keep hD4 (slot16 hP3) (slot40 hP3) (by decide) (k40.trans h08))
    (fun t4 hFt hlt hript hr8t hrcxt hrsit hr15t h20t h18t h10t h08t => ?_)⟩
  · seg_read [hX3]; rw [BitVec.add_assoc, p_add16 c]
  · seg_read [e1]; exact hR16.1.symm
  · have e10 : c.n - k - NMAX = c.n - (k + NMAX) := Nat.sub_sub _ _ _
    have e08 : c.n - k = c.n - (k + NMAX) + NMAX := by omega
    rw [e10] at hrsit h10t
    rw [e08] at h08t
    exact exitA2 c t4 (k + NMAX) _ o4 h4 hFt hlt hript hkn (Nat.le_add_left _ _)
      (by unfold NMAX at *; omega) hr8t hrcxt hrsit hr15t h20t h18t h10t h08t

theorem vcA_holds : VcA 110 := fun c s hl hrip hI => vcA c s hl hrip hI

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
