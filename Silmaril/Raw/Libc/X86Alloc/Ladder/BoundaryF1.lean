module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryDisj

/-!
# Proofs: rung 08 (boundary tags) — `free` pushes the merged block

`ftail2` (`0x4014c3`): the merged block `(B, S)`, its size word and footer written and both table
bytes set, gets its links (`next` the old head `H` in `rsi`, `prev` 0), the old head's `prev`
becomes `B`, and `flist = B`: the state is `(B, S) :: fs2`.
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

/-- The postcondition of `free`. -/
abbrev FQ (x : Word × Option Nat) (sp ret : Word) : SProp := (freeSpec iface).SysVPost x sp ret

variable {sp ret : Word}

/-- **`0x4014c3`: link the merged block in at the head.** -/
theorem ftail2 (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (fs2 : List (Nat × Nat))
    (B S X : Nat) (hw : WF ((B, S) :: fs2))
    (hrcx : f .rcx = wd B) (hrsi : f .rsi = wd (hdOr fs2 0)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4014c3 f fl
      (blockAny (B + 8) 8 ∗ blockAny (B + 16) 8 ∗ wordPt B (wd S) ∗ blockAny (B + 24) (S - 32) ∗
        wordPt (B + S - 8) (wd S) ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd X) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT ((B, S) :: fs2)) ∗
        tblPt firstA (firstT ((B, S) :: fs2)) ∗ dll fs2 0 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hgB := hw.1 (B, S) (by simp); unfold Good at hgB; simp only at hgB
  have hg2 : ∀ y ∈ fs2, Good y := fun y hy => hw.1 y (by simp [hy])
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 403) (k := 4)
    (pc := 0x4014c3) (pc' := 0x4014c7) (by decide) (fit 403 4) (base := .rcx) (src := .rsi)
    (by decide) (by decide) (by decide) (disp := 0x8) (entails_refl _) d403 (by decide)
    (by rw [hrcx]; exact addr_add (by decide +kernel) (by omega))) ?_
  refine SPEC.mem (M' := blockAny (B + 16) 8 ∗ (wordPt (B + 8) (f .rsi) ∗ wordPt B (wd S) ∗
      blockAny (B + 24) (S - 32) ∗
      wordPt (B + S - 8) (wd S) ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd X) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT ((B, S) :: fs2)) ∗
      tblPt firstA (firstT ((B, S) :: fs2)) ∗ dll fs2 0 0)) (by ac_rfl) ?_
  refine SPEC.trans (c_movIM E (b := 0x401330) (code := code) (o := 407) (k := 8)
    (pc := 0x4014c7) (by decide) (fit 407 8) (entails_refl _) d407
    (addr_reg (r := .rcx) (by decide) hrcx (addr_add (by decide +kernel) (by omega)))) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 415) (k := 3)
    (pc := 0x4014c7 + BitVec.ofNat 64 8) (by decide) (fit 415 3) (r := .rsi) (by decide) d415) ?_
  have hz0 : (BitVec.signExtend 64 (0x0 : BitVec 32)) = wd 0 := by decide +kernel
  rw [hz0, hrsi]
  have hfin : ∀ (pc : Word) (f' : Reg → Word) (fl' : Flags) (o : Nat) (hpc : pc.toNat = 0x401330 + o)
      (hk : o + 1 ≤ code.length) (hr : (code.drop o).take 1 = Silmaril.X86.Insn.encode .ret)
      (hsp : f' .rsp = sp),
      SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St pc f' fl' (wordPt sp.toNat ret ∗
        mmOf ((B, S) :: fs2))) (FQ x sp ret) := by
    intro pc f' fl' o hpc hk hr hsp
    refine SPEC.conseq (entails_refl _) (c_retAt E hpc hk hsp hr) ?_
    exact St_post rfl (by simp only [Function.update_self]) (mm_of hw)
  cases fs2 with
  | nil =>
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 418) (k := 2)
      (pc := 0x4014c7 + BitVec.ofNat 64 8 + BitVec.ofNat 64 3) (pc' := 0x4014d8) (by decide)
      (fit 418 2) (c := .e) (rel := 0x4) (by rw [eval_e_wd (by decide)]; rfl) d418
      (by decide)) ?_
    refine SPEC.mem (M' := wordPt flistA (wd X) ∗ (wordPt (B + 16) (wd 0) ∗
      wordPt (B + 8) (wd (hdOr [] 0)) ∗ wordPt B (wd S) ∗ blockAny (B + 24) (S - 32) ∗
      wordPt (B + S - 8) (wd S) ∗ wordPt sp.toNat ret ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT [(B, S)]) ∗
      tblPt firstA (firstT [(B, S)]) ∗ dll [] 0 0)) (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 424) (k := 7)
      (pc := 0x4014d8) (pc' := 0x4014df) (by decide) (fit 424 7) (src := .rcx) (by decide)
      (disp := 0x1bc1) (wordPt_blockAny _ _) d424 (by decide) (by decide)) ?_
    refine SPEC.mem ?_ (hfin 0x4014df f _ 431 (by decide) (fit 431 1) r431 hrsp)
    rw [hrcx, mmOf, dll_cons]; simp only [blk, hdOr, dll_nil]; ac_rfl
  | cons z l =>
    have hz := good_lt hg2 ⟨z, by simp, rfl⟩
    have hz0 : hdOr (z :: l) 0 ≠ 0 := by simp only [hdOr]; omega
    have hz64 : hdOr (z :: l) 0 < 2 ^ 64 := by simp only [hdOr]; omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 418) (k := 2)
      (pc := 0x4014c7 + BitVec.ofNat 64 8 + BitVec.ofNat 64 3) (pc' := 0x4014d4) (by decide)
      (fit 418 2) (c := .e) (rel := 0x4) (by rw [eval_e_wd hz64]; simp [hz0]) d418
      (by decide)) ?_
    refine SPEC.mem (M' := wordPt (z.1 + 16) (wd 0) ∗ (wordPt (B + 16) (wd 0) ∗
      wordPt (B + 8) (wd (hdOr (z :: l) 0)) ∗ wordPt B (wd S) ∗ blockAny (B + 24) (S - 32) ∗
      wordPt (B + S - 8) (wd S) ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd X) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT ((B, S) :: z :: l)) ∗
      tblPt firstA (firstT ((B, S) :: z :: l)) ∗ wordPt z.1 (wd z.2) ∗
      wordPt (z.1 + 8) (wd (hdOr l 0)) ∗ blockAny (z.1 + 24) (z.2 - 32) ∗
      wordPt (z.1 + z.2 - 8) (wd z.2) ∗ dll l z.1 0))
      (by rw [dll_cons]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 420) (k := 4)
      (pc := 0x4014d4) (pc' := 0x4014d8) (by decide) (fit 420 4) (base := .rsi) (src := .rcx)
      (by decide) (by decide) (by decide) (disp := 0x10) (wordPt_blockAny _ _) d420 (by decide)
      (by rw [hrsi]; simp only [hdOr]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem (M' := wordPt flistA (wd X) ∗ (wordPt (z.1 + 16) (f .rcx) ∗
      wordPt (B + 16) (wd 0) ∗
      wordPt (B + 8) (wd (hdOr (z :: l) 0)) ∗ wordPt B (wd S) ∗ blockAny (B + 24) (S - 32) ∗
      wordPt (B + S - 8) (wd S) ∗ wordPt sp.toNat ret ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT ((B, S) :: z :: l)) ∗
      tblPt firstA (firstT ((B, S) :: z :: l)) ∗ wordPt z.1 (wd z.2) ∗
      wordPt (z.1 + 8) (wd (hdOr l 0)) ∗ blockAny (z.1 + 24) (z.2 - 32) ∗
      wordPt (z.1 + z.2 - 8) (wd z.2) ∗ dll l z.1 0)) (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 424) (k := 7)
      (pc := 0x4014d8) (pc' := 0x4014df) (by decide) (fit 424 7) (src := .rcx) (by decide)
      (disp := 0x1bc1) (wordPt_blockAny _ _) d424 (by decide) (by decide)) ?_
    refine SPEC.mem ?_ (hfin 0x4014df f _ 431 (by decide) (fit 431 1) r431 hrsp)
    rw [hrcx, mmOf, dll_cons, dll_cons]; simp only [blk, hdOr]; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
