module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.BodyC
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.ExitC
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Total

/-!
# `adler32_z`: the VC of the last-chunk `DO16` loop `0x2e3`

`bodyC` composes the four segments of one block (`c1`…`c4`) over abstract bytes; `vcC`
instantiates the bytes with the buffer (`x j = c.b (k + 16 t + j)`), turns the block sums
`pre x r 16`/`tri x r 16` into the raw sums `R k (16 t + 16)` (`pre16`, `tri16`, `R16W`) and
continues with `tailC` (the read-modify-write of `s2` and the exits). The offsets inside the
composition are variables (`∃ o, o = 787`, …) so that nothing unfolds `wpN` at a literal
offset (see `Do16`).
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

/-- One `DO16` block of `0x2e3`, from the loop head to the read-modify-write at `0x39e`. -/
theorem bodyC (c : Ctx) (K : Nat) (μ : Option Nat) (s : MState) (o0 o4 : Nat) (h0 : o0 = 739)
    (h4 : o4 = 926) (hF : Fr c s) (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o0) (X : Word) (hX : s.core.read .rcx = X)
    (x : Nat → Word)
    (hx : ∀ mem, FM c mem → ∀ j, j < 16 → loadN mem (X + BitVec.ofNat 64 j) 1 = some (x j))
    (hz : ∀ j, (((x j).setWidth 8).setWidth 32).setWidth 64 = x j)
    (r : Word) (hr : s.core.read .r15 = r)
    (hk : ∀ t : MState, Fr c t → Loaded t.memory c.base adler32zCode →
      t.core.rip = c.base + BitVec.ofNat 64 o4 → t.core.read .rcx = X →
      t.core.read .r15 = pre x r 16 → t.core.read .rax = tri x r 16 →
      loadN t.memory (c.sp + 18446744073709551584#64) 8 = loadN s.memory (c.sp + 18446744073709551584#64) 8 →
      loadN t.memory (c.sp + 18446744073709551592#64) 8 = loadN s.memory (c.sp + 18446744073709551592#64) 8 →
      loadN t.memory (c.sp + 18446744073709551600#64) 8 = loadN s.memory (c.sp + 18446744073709551600#64) 8 →
      loadN t.memory (c.sp + 18446744073709551608#64) 8 = loadN s.memory (c.sp + 18446744073709551608#64) 8 →
      wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ K o4 t) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ (K + 52) o0 s := by
  obtain ⟨o1, h1⟩ : ∃ o, o = 787 := ⟨_, rfl⟩
  obtain ⟨o2, h2⟩ : ∃ o, o = 834 := ⟨_, rfl⟩
  obtain ⟨o3, h3⟩ : ∃ o, o = 865 := ⟨_, rfl⟩
  have hx' := hx _ hF.mem
  refine c1 c (K + 40) μ s o0 o1 h0 h1 hl X hX x r hx' hz hrip hr
    (fun t1 hm1 hsp1 hrip1 hX1 a1 a2 a3 a4 a5 a6 a7 => ?_)
  have hl1 : Loaded t1.memory c.base adler32zCode := hm1 ▸ hl
  have hx1 : ∀ j, j < 16 → loadN t1.memory (X + BitVec.ofNat 64 j) 1 = some (x j) := hm1 ▸ hx'
  refine c2 c (K + 27) μ t1 o1 o2 h1 h2 hl1 X hX1 x r hx1 hz hrip1 a1 a2 a3 a4 a5 a6 a7
    (fun t2 hm2 hsp2 hrip2 hX2 b1 b2 b3 b4 b5 b6 b7 b8 => ?_)
  have hl2 : Loaded t2.memory c.base adler32zCode := hm2 ▸ hl1
  have hx2 : ∀ j, j < 16 → loadN t2.memory (X + BitVec.ofNat 64 j) 1 = some (x j) := hm2 ▸ hx1
  refine c3 c (K + 17) μ t2 o2 o3 h2 h3 hl2 X hX2 x r hx2 hz hrip2 b1 b2 b3 b4 b5 b6 b7 b8
    (fun t3 hm3 hsp3 hrip3 hX3 d1 d2 d3 d4 d5 => ?_)
  have hm : t3.memory = s.memory := hm3.trans (hm2.trans hm1)
  have hF3 : Fr c t3 := hF.with hm (by rw [hsp3, hsp2, hsp1, hF.sp])
  refine c4 c K μ t3 o3 o4 h3 h4 hF3 hrip3 X hX3 x hx hz r d1 d2 d3 d4 d5
    (fun t hFt hlt hript hXt e1 e2 k16 k24 k32 k40 => ?_)
  rw [hm] at k16 k24 k32 k40
  exact hk t hFt hlt hript hXt e1 e2 k16 k24 k32 k40

/-- **The VC of the last-chunk loop `0x2e3`.** -/
theorem vcC (c : Ctx) (s : MState) (hl : Loaded s.memory c.base adler32zCode)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 739) (hI : InvC c s) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base
      (some (meas c .rcx s)) 113 739 s := by
  obtain ⟨hF, k, t, hr16, hrem, hkn, ht, hrcx, hr15, h20, h18, h10, h08⟩ := hI
  have hP := hF.pre
  have hn := n_lt c
  have hq := Nat.div_mul_le_self (c.n - k - 16) 16
  have hpos : k + 16 * t + 16 ≤ c.n := by omega
  have hpfit : c.p.toNat + (c.n - 1) < 2 ^ 64 := p_fit hP hF.nz (by omega)
  have hmeas : meas c .rcx s = c.n - (k + 16 * t) := by
    simp only [meas]; rw [hrcx, p_sub c (by omega)]
  rw [hmeas]
  generalize h739 : (739 : Nat) = o0 at hrip ⊢
  obtain ⟨o4, h4⟩ : ∃ o, o = 926 := ⟨_, rfl⟩
  have hR16 := R16W c (k := k) (j := 16 * t) (by omega)
  refine bodyC c 61 _ s o0 o4 h739.symm h4 hF hl hrip _ hrcx (fun j => c.b (k + 16 * t + j))
    (fun mem hFm j hj => load_buf_off hP hFm hF.nz rfl j (by omega)) (fun j => zx_b c _) _ hr15
    (fun t' hFt hlt hript hXt e1 e2 k16 k24 k32 k40 => ?_)
  rw [pre16] at e1
  rw [tri16] at e2
  refine tailC c t' o4 k t h4 hFt hript hr16 hrem hkn ht hXt (e1.trans hR16.1.symm) _ _ e2
    (k16.trans h20) ?_ (k24.trans h18) (k32.trans h10) (k40.trans h08)
  rw [hR16.2]
  exact add17 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem vcC_holds : VcC 113 := fun c s hl hrip hI => vcC c s hl hrip hI

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
