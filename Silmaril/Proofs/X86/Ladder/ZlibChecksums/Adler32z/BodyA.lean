module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Do16

/-!
# `adler32_z`: one `DO16` block of the `NMAX` chunk loop `0x80`, in segments

As `BodyC` for the other loop: `a1` (`0x80`–`0xb7`) and `a2` (`0xb7`–`0xef`) compute in
registers (`r8` is advanced by 16 at `0x89`, the later loads use negative displacements);
`a3` (`0xef`–`0x146`) has the two spills to `-0x30`/`-0x28(%rsp)` and stops before the
read-modify-write of `s2` at `0x146` (`rmw`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
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
/-- `0x80`–`0xb7`. -/
theorem a1 (c : Ctx) (K : Nat) (μ : Option Nat) (s : MState) (o0 o1 : Nat) (h0 : o0 = 128)
    (h1 : o1 = 183) (hl : Loaded s.memory c.base adler32zCode) (X : Word)
    (hX : s.core.read .r8 = X) (x : Nat → Word) (r : Word)
    (hx : ∀ j, j < 16 → loadN s.memory (X + BitVec.ofNat 64 j) 1 = some (x j))
    (hz : ∀ j, (((x j).setWidth 8).setWidth 32).setWidth 64 = x j)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o0)
    (hr15 : s.core.read .r15 = r)
    (hk : ∀ t : MState, t.memory = s.memory → t.core.read .rsp = s.core.read .rsp →
      t.core.rip = c.base + BitVec.ofNat 64 o1 → t.core.read .r8 = X + 16#64 →
      t.core.read .rax = tri x r 2 →
      t.core.read .r13 = pre x r 3 →
      t.core.read .r12 = x 3 →
      t.core.read .rbp = x 4 →
      t.core.read .rbx = x 5 →
      t.core.read .r11 = x 6 →
      t.core.read .rdx = x 7 →
      wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ K o1 t) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ (K + 13) o0 s := by
  subst h0 h1
  have hp := pre_succ x r
  have hp1 := pre_one x r
  have ht2 := tri_two x r
  have ht := tri_succ x r
  have hx0 : loadN s.memory X 1 = some (x 0) := by simpa using hx 0 (by decide)
  adler_vc [hrip, hl, Mem.ofReg, hX, hx0, hx, Nat.reduceLT, hz, hr15, hp, hp1, ht2, ht]
  apply hk <;> first | rfl | seg_read [hX, Silmaril.X86.State.write_rip, hr15]

set_option maxHeartbeats 40000000 in
/-- `0xb7`–`0xef`. -/
theorem a2 (c : Ctx) (K : Nat) (μ : Option Nat) (s : MState) (o0 o1 : Nat) (h0 : o0 = 183)
    (h1 : o1 = 239) (hl : Loaded s.memory c.base adler32zCode) (X : Word)
    (hX : s.core.read .r8 = X + 16#64) (x : Nat → Word) (r : Word)
    (hx : ∀ j, j < 16 → loadN s.memory (X + BitVec.ofNat 64 j) 1 = some (x j))
    (hz : ∀ j, (((x j).setWidth 8).setWidth 32).setWidth 64 = x j)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o0)
    (hrax : s.core.read .rax = tri x r 2)
    (hr13 : s.core.read .r13 = pre x r 3)
    (hr12 : s.core.read .r12 = x 3)
    (hrbp : s.core.read .rbp = x 4)
    (hrbx : s.core.read .rbx = x 5)
    (hr11 : s.core.read .r11 = x 6)
    (hrdx : s.core.read .rdx = x 7)
    (hk : ∀ t : MState, t.memory = s.memory → t.core.read .rsp = s.core.read .rsp →
      t.core.rip = c.base + BitVec.ofNat 64 o1 → t.core.read .r8 = X + 16#64 →
      t.core.read .rax = tri x r 7 →
      t.core.read .rdi = pre x r 8 →
      t.core.read .rdx = x 8 →
      t.core.read .r10 = x 9 →
      t.core.read .r9 = x 10 →
      t.core.read .rcx = x 13 →
      t.core.read .r15 = x 15 →
      wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ K o1 t) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ (K + 15) o0 s := by
  subst h0 h1
  have hp := pre_succ x r
  have hp1 := pre_one x r
  have ht2 := tri_two x r
  have ht := tri_succ x r
  have hx0 : loadN s.memory X 1 = some (x 0) := by simpa using hx 0 (by decide)
  adler_vc [hrip, hl, Mem.ofReg, hX, hx0, hx, Nat.reduceLT, hz, hrax, hr13, hr12, hrbp, hrbx, hr11, hrdx, hp, hp1, ht2, ht]
  apply hk <;> first | rfl | seg_read [hX, Silmaril.X86.State.write_rip, hrax, hr13, hr12, hrbp, hrbx, hr11, hrdx]

set_option maxHeartbeats 40000000 in
/-- `0xef`–`0x146`: the spills of `pre 8`, `pre 9` and their reloads. -/
theorem a3 (c : Ctx) (K : Nat) (μ : Option Nat) (s : MState) (o0 o1 : Nat) (h0 : o0 = 239)
    (h1 : o1 = 326) (hF : Fr c s)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o0) (X : Word) (hX : s.core.read .r8 = X + 16#64)
    (x : Nat → Word)
    (hx : ∀ mem, FM c mem → ∀ j, j < 16 → loadN mem (X + BitVec.ofNat 64 j) 1 = some (x j))
    (hz : ∀ j, (((x j).setWidth 8).setWidth 32).setWidth 64 = x j)
    (r : Word) (hrax : s.core.read .rax = tri x r 7) (hrdi : s.core.read .rdi = pre x r 8)
    (hrdx : s.core.read .rdx = x 8) (hr10 : s.core.read .r10 = x 9) (hr9 : s.core.read .r9 = x 10)
    (hrcx : s.core.read .rcx = x 13) (hr15 : s.core.read .r15 = x 15)
    (hk : ∀ t : MState, Fr c t → Loaded t.memory c.base adler32zCode →
      t.core.rip = c.base + BitVec.ofNat 64 o1 → t.core.read .r8 = X + 16#64 →
      t.core.read .r15 = pre x r 16 → t.core.read .rax = tri x r 16 →
      loadN t.memory (c.sp + 18446744073709551584#64) 8 = loadN s.memory (c.sp + 18446744073709551584#64) 8 →
      loadN t.memory (c.sp + 18446744073709551592#64) 8 = loadN s.memory (c.sp + 18446744073709551592#64) 8 →
      loadN t.memory (c.sp + 18446744073709551600#64) 8 = loadN s.memory (c.sp + 18446744073709551600#64) 8 →
      loadN t.memory (c.sp + 18446744073709551608#64) 8 = loadN s.memory (c.sp + 18446744073709551608#64) 8 →
      wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ K o1 t) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ (K + 24) o0 s := by
  subst h0 h1
  have hP := hF.pre
  have hl := hF.mem.loaded hP
  have hp := pre_succ x r
  have hp1 := pre_one x r
  have ht2 := tri_two x r
  have ht := tri_succ x r
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, hX, hx _ hF.mem, Nat.reduceLT, hz, hrax, hrdi, hrdx, hr10,
    hr9, hrcx, hr15, hp, hp1, ht2, ht]
  refine ⟨spill_perm hP hF.mem (slot0 hP) (by decide), fun m1 hst1 => ?_⟩
  obtain ⟨hF1, hS1, hL1, hA1, hD1⟩ := spill hP hF.mem hF.saved (slot0 hP) (by decide) hst1
  simp only [hL1, true_and, hA1]
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, hX, hx _ hF1, Nat.reduceLT, hz, hrax, hrdi, hrdx, hr10,
    hr9, hrcx, hr15, hA1, hL1, hp, hp1, ht2, ht]
  refine ⟨spill_perm hP hF1 (slot8 hP) (by decide), fun m2 hst2 => ?_⟩
  obtain ⟨hF2, hS2, hL2, hA2, hD2⟩ := spill hP hF1 hS1 (slot8 hP) (by decide) hst2
  simp only [hL2, true_and, hA2]
  adler_vc [hrip, hl, hF.sp, Mem.ofReg, hX, hx _ hF2, Nat.reduceLT, hz, hrax, hrdi, hrdx, hr10,
    hr9, hrcx, hr15, hA2, hL2, hp, hp1, ht2, ht]
  have k16 := (keep' hD2 (slot8 hP) (slot16 hP) (by decide)).trans
    (keep' hD1 (slot0 hP) (slot16 hP) (by decide))
  have k24 := (keep' hD2 (slot8 hP) (slot24 hP) (by decide)).trans
    (keep' hD1 (slot0 hP) (slot24 hP) (by decide))
  have k32 := (keep' hD2 (slot8 hP) (slot32 hP) (by decide)).trans
    (keep' hD1 (slot0 hP) (slot32 hP) (by decide))
  have k40 := (keep' hD2 (slot8 hP) (slot40 hP) (by decide)).trans
    (keep' hD1 (slot0 hP) (slot40 hP) (by decide))
  apply hk _ (hF.withMem hF2 hS2 (by seg_read [hF.sp])) hL2
  · seg_read [Silmaril.X86.State.write_rip]
  · seg_read [hX]
  · seg_read []
  · seg_read []
  · exact k16
  · exact k24
  · exact k32
  · exact k40

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
