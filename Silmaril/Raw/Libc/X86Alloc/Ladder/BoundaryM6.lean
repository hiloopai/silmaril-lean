module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM5

/-!
# Proofs: rung 08 (boundary tags) — `malloc` found a block

`found` (`0x401376`): `y` holds at least `a` bytes. Its size, granule `g` and last granule
`g + size/16 - 1` are computed, and the spare `size - a` chooses between handing out the whole
block (`tail_unlink`) and splitting it (`tail_split`).
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

theorem wd_minus {x y : Nat} (h : y ≤ x) (hx : x < 2 ^ 64) : wd x - wd y = wd (x - y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_wd hx, toNat_wd (by omega), toNat_wd (by omega)]
  omega

variable {nw sp ret : Word}

/-- **`0x401376`: the block `y` fits.** -/
theorem found (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat)) (y : Nat × Nat)
    (hw : WF (l1 ++ y :: l2)) (hn4 : nw.toNat ≤ 4096) (hfit : need nw.toNat ≤ y.2)
    (hrax : f .rax = wd y.1) (hrdx : f .rdx = wd (need nw.toNat)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401376 f fl
      (blk y (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hgy := (wf_mid hw).1
  have hy := hgy; unfold Good at hy
  obtain ⟨ha16, ha32, han, ha4⟩ := need_facts hn4
  refine SPEC.mem (M' := wordPt y.1 (wd y.2) ∗ (wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗
      wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
      tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 70) (k := 3)
    (pc := 0x401376) (pc' := 0x401379) (by decide) (fit 70 3) (base := .rax) (dst := .rcx)
    (by decide) (by decide) (by decide) (disp := 0x0) d70 (by decide)
    (by rw [hrax]; exact addr_add (v := y.1) (D := 0) (by decide +kernel) (by omega))) ?_
  refine SPEC.mem (M' := blk y (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0)
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 73) (k := 3) (pc := 0x401379)
    (by decide) (fit 73 3) (r := .rsi) (q := .rax) (by decide) (by decide) (by decide) d73) ?_
  refine SPEC.trans (c_aluI E (b := 0x401330) (code := code) (o := 76) (k := 7)
    (pc := 0x401379 + BitVec.ofNat 64 3) (by decide) (fit 76 7) (op := .sub) (by decide)
    (r := .rsi) (by decide) (imm := 0x4032c0) d76) ?_
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 83) (k := 3)
    (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7) (by decide) (fit 83 3) (r := .rdi)
    (q := .rcx) (by decide) (by decide) (by decide) d83) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 86) (k := 4)
    (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3) (by decide)
    (fit 86 4) (r := .rsi) (by decide) (c := 0x4) (by decide) d86) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 90) (k := 4)
    (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 4) (by decide) (fit 90 4) (r := .rcx) (by decide) (c := 0x4) (by decide)
    d90) ?_
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 94) (k := 3)
    (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 4 + BitVec.ofNat 64 4) (by decide) (fit 94 3) (op := .sub) (by decide)
    (r := .rdi) (q := .rdx) (by decide) (by decide) (by decide) d94) ?_
  have hsub : Silmaril.X86.Ext.AluOp.resultN .sub (wd y.1)
      (BitVec.signExtend 64 (0x4032c0 : BitVec 32)) = wd (y.1 - heap) := by
    rw [show BitVec.signExtend 64 (0x4032c0 : BitVec 32) = wd 0x4032c0 by decide +kernel]
    exact wd_minus (by omega) (by omega)
  have hsi : ShiftOp.shr.result (wd (y.1 - heap)) ((0x4 : BitVec 8).toNat % 64) =
      wd ((y.1 - heap) / 16) := shr4_wd (by omega)
  have hcx : ShiftOp.shr.result (wd y.2) ((0x4 : BitVec 8).toNat % 64) = wd (y.2 / 16) :=
    shr4_wd (by omega)
  have hdi : Silmaril.X86.Ext.AluOp.resultN .sub (wd y.2) (wd (need nw.toNat)) =
      wd (y.2 - need nw.toNat) := wd_minus hfit (by omega)
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 97) (k := 5)
    (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 4 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3) (by decide) (fit 97 5)
    (dst := .r8) (by decide) d97 (a := wd ((y.1 - heap) / 16 + y.2 / 16 - 1))
    (fun st hregs next => by
      rw [idx_addr, hregs .rsi (by decide), hregs .rcx (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax]
      rw [hsub, hsi, hcx, wd_add,
        show BitVec.signExtend 64 (0xffffffff : BitVec 32) = wd (2 ^ 64 - 1) by decide +kernel,
        wd_sub (by omega) (by omega)])) ?_
  refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 102) (k := 4)
    (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 4 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3 + BitVec.ofNat 64 5) (by decide)
    (fit 102 4) (r := .rdi) (imm := 0x1f) (by decide) d102) ?_
  have e31 : (BitVec.signExtend 64 (0x1f : BitVec 8)).toNat = 31 := by decide +kernel
  by_cases hsp : 31 < y.2 - need nw.toNat
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 106) (k := 2)
      (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3 +
        BitVec.ofNat 64 4 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3 + BitVec.ofNat 64 5 +
        BitVec.ofNat 64 4) (pc' := 0x4013d8) (by decide) (fit 106 2) (c := .a) (rel := 0x3c)
      ?_ d106 (by decide)) ?_
    · rw [eval_a_cmp, e31]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrdx]
      rw [hdi, toNat_wd (by omega)]; simp [hsp]
    exact tail_split _ _ l1 l2 y (need nw.toNat) hw ha16 ha32 han (by omega)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrdx]
          exact hdi)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax]
          rw [hsub, hsi])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 106) (k := 2)
      (pc := 0x401379 + BitVec.ofNat 64 3 + BitVec.ofNat 64 7 + BitVec.ofNat 64 3 +
        BitVec.ofNat 64 4 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3 + BitVec.ofNat 64 5 +
        BitVec.ofNat 64 4) (pc' := 0x40139c) (by decide) (fit 106 2) (c := .a) (rel := 0x3c)
      ?_ d106 (by decide)) ?_
    · rw [eval_a_cmp, e31]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrdx]
      rw [hdi, toNat_wd (by omega)]; simp [hsp]
    exact tail_unlink _ _ l1 l2 y hw (by omega)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax]
          rw [hsub, hsi])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
