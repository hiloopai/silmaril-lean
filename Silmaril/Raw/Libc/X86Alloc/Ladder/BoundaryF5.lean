module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF4

/-!
# Proofs: rung 08 (boundary tags) — `free` looks for a previous free block

`fprev` (`0x401494`): the pending block `(b, S)` (after the merge with the next block, if any).
At granule 0 nothing precedes it; otherwise `last[g - 1]` says whether a free block ends at `b`.
That byte is right for the current list (it is not the pending block's own last granule), so a
set byte names a block of the list, and `fmerge_prev` merges with it; otherwise the block is
pushed as it is.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.X86.Ext (ShiftOp)
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Boundary
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.MemStep

theorem eval_ne_sub0 (v : Byte) :
    Silmaril.X86.Ext.Cond.ne.eval (Silmaril.X86.Ext.subFlagsN v 0) = some (decide (v ≠ 0)) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN,
    Silmaril.X86.Ext.kNot]
  rw [Bool.eq_iff_iff]; simp [beq_iff_eq]

theorem eval_e_sub0 (v : Byte) :
    Silmaril.X86.Ext.Cond.e.eval (Silmaril.X86.Ext.subFlagsN v 0) = some (decide (v = 0)) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN]
  rw [Bool.eq_iff_iff]; simp [beq_iff_eq]

variable {sp ret : Word}

/-- **`0x401494`: merge with a previous free block, if the table names one.** -/
theorem fprev (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (fs1 : List (Nat × Nat))
    (b S g : Nat) (tl : Nat → Byte) (hw : WF fs1) (hgb : Good (b, S))
    (hap : ∀ y ∈ fs1, Apart (b, S) y) (hb : b = heap + 16 * g)
    (htl : ∀ j < 256, j ≠ g + S / 16 - 1 → tl j = lastT fs1 j)
    (hrax : f .rax = wd S) (hrcx : f .rcx = wd b) (hrdx : f .rdx = wd g)
    (hrdi : f .rdi = wd (b + 16)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401494 f fl
      (blockAny b S ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs1 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT fs1) ∗ dll fs1 0 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hL : lastA = 0x4030c0 := rfl
  have hg := hgb; unfold Good at hg; simp only at hg
  have hg2 := hw.1
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 356) (k := 3) (pc := 0x401494)
    (by decide) (fit 356 3) (r := .rdx) (by decide) d356) ?_
  by_cases hg0 : g = 0
  · subst hg0
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 359) (k := 2)
      (pc := 0x401494 + BitVec.ofNat 64 3) (pc' := 0x401499) (by decide) (fit 359 2) (c := .ne)
      (rel := 0x47) (by rw [hrdx, eval_ne_wd (by decide)]; rfl) d359 (by decide)) ?_
    refine SPEC.mem (M' := wordPt flistA (wd (hdOr fs1 0)) ∗ (blockAny b S ∗
        wordPt sp.toNat ret ∗ blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗
        tblPt firstA (firstT fs1) ∗ dll fs1 0 0)) (by ac_rfl) ?_
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 361) (k := 7)
      (pc := 0x401499) (pc' := 0x4014a0) (by decide) (fit 361 7) (dst := .rsi) (by decide)
      (disp := 0x1c00) d361 (by decide) (by decide)) ?_
    refine SPEC.trans (c_movIQ E (b := 0x401330) (code := code) (o := 368) (k := 7)
      (pc := 0x4014a0) (by decide) (fit 368 7) (r := .r8) (by decide) (imm := 0xffffffff) d368) ?_
    refine SPEC.mem ?_ (ftail x _ _ fs1 b S 0 (hdOr fs1 0) tl (firstT fs1) hw hgb hap hb
      (fun _ _ _ => rfl) htl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
      (by simp only [Function.update_self]; decide +kernel)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
    ac_rfl
  · have hg64 : g < 2 ^ 64 := by omega
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 359) (k := 2)
      (pc := 0x401494 + BitVec.ofNat 64 3) (pc' := 0x4014e0) (by decide) (fit 359 2) (c := .ne)
      (rel := 0x47) (by rw [hrdx, eval_ne_wd hg64]; simp [hg0]) d359 (by decide)) ?_
    have hgl : g - 1 < 256 := by omega
    have htlg : tl (g - 1) = lastT fs1 (g - 1) := htl (g - 1) hgl (by omega)
    refine SPEC.mem (M' := bytePt (lastA + (g - 1)) (tl (g - 1)) ∗ (tblR lastA tl (g - 1) ∗
        blockAny b S ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs1 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt firstA (firstT fs1) ∗ dll fs1 0 0))
      (by rw [tbl_split lastA tl hgl]; ac_rfl) ?_
    refine SPEC.trans (c_cmpB E (b := 0x401330) (code := code) (o := 432) (k := 7)
      (pc := 0x4014e0) (by decide) (fit 432 7) d432
      (addr_reg (r := .rdx) (by decide) hrdx ((addr_tbl (D := 0x4030bf) (by decide +kernel) (by omega)).trans
        (by omega)))) ?_
    refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 439) (k := 4)
      (pc := 0x4014e0 + BitVec.ofNat 64 7) (by decide) (fit 439 4) (dst := .r8) (by decide) d439
      (a := wd g + wd (2 ^ 64 - 1)) (fun st hregs next => by
        rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdx (by decide), hrdx,
          show BitVec.signExtend 64 (0xffffffff : BitVec 32) = wd (2 ^ 64 - 1) by
            decide +kernel])) ?_
    rcases lastT_cases fs1 (g - 1) with h0 | h1
    · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 443) (k := 2)
        (pc := 0x4014e0 + BitVec.ofNat 64 7 + BitVec.ofNat 64 4) (pc' := 0x4014ed) (by decide)
        (fit 443 2) (c := .ne) (rel := 0x13) (by rw [eval_ne_sub0, htlg, h0]; rfl) d443
        (by decide)) ?_
      refine SPEC.mem (M' := wordPt flistA (wd (hdOr fs1 0)) ∗ (blockAny b S ∗
          wordPt sp.toNat ret ∗ blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗
          tblPt firstA (firstT fs1) ∗ dll fs1 0 0))
        (by rw [tbl_split lastA tl hgl]; ac_rfl) ?_
      refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 445) (k := 7)
        (pc := 0x4014ed) (pc' := 0x4014f4) (by decide) (fit 445 7) (dst := .rsi) (by decide)
        (disp := 0x1bac) d445 (by decide) (by decide)) ?_
      refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 452) (k := 2)
        (pc := 0x4014f4) (pc' := 0x4014a7) (by decide) (fit 452 2) d452 (by decide)) ?_
      refine SPEC.mem ?_ (ftail x _ _ fs1 b S g (hdOr fs1 0) tl (firstT fs1) hw hgb hap hb
        (fun _ _ _ => rfl) htl
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
      ac_rfl
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 443) (k := 2)
        (pc := 0x4014e0 + BitVec.ofNat 64 7 + BitVec.ofNat 64 4) (pc' := 0x401500) (by decide)
        (fit 443 2) (c := .ne) (rel := 0x13) (by rw [eval_ne_sub0, htlg, h1]; rfl) d443
        (by decide)) ?_
      obtain ⟨pb, hpbm, hpbe⟩ := lastT_one.1 h1
      obtain ⟨m1, m2, rfl⟩ := List.append_of_mem hpbm
      refine SPEC.mem ?_ (fmerge_prev x _ _ m1 m2 pb b S g tl hw hgb hap hb (by omega)
        (by omega) htl
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
        (by simp only [Function.update_self])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
      rw [tbl_split lastA tl hgl, dll_mid]; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
