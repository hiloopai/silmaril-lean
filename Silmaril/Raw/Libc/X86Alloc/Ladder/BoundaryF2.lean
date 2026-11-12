module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF1
public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM6

/-!
# Proofs: rung 08 (boundary tags) — `free` writes the merged block's tags

`ftail` (`0x4014a7`): the merged block `(B, S)` (granule `G`, `r8 = G - 1`) owns `[B, B + S)`
with unknown contents. Its size word and footer are written, then `first[G]` and
`last[G - 1 + S/16]`. The tables were right for `fs2` except at those two bytes, so afterwards
they are right for `(B, S) :: fs2`.
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

theorem split5 (B S : Nat) (hS : 32 ≤ S) :
    blockAny B S = (blockAny B 8 ∗ blockAny (B + 8) 8 ∗ blockAny (B + 16) 8 ∗
      blockAny (B + 24) (S - 32) ∗ blockAny (B + S - 8) 8) := by
  have e : S = 8 + (8 + (8 + ((S - 32) + 8))) := by omega
  conv_lhs => rw [e]
  rw [blockAny_add, blockAny_add, blockAny_add, blockAny_add,
    show B + 8 + 8 = B + 16 by omega, show B + 16 + 8 = B + 24 by omega,
    show B + 24 + (S - 32) = B + S - 8 by omega]

theorem first_push {fs2 : List (Nat × Nat)} {B S G : Nat} {tf : Nat → Byte}
    (hB : B = heap + 16 * G) (htf : ∀ j < 256, j ≠ G → tf j = firstT fs2 j) :
    ∀ j < 256, Function.update tf G 1 j = firstT ((B, S) :: fs2) j := by
  intro j hj
  rw [firstT_cons]
  by_cases e : j = G
  · subst e; simp [hB]
  · rw [Function.update_of_ne e, htf j hj e]
    split
    · rename_i h; simp only at h; omega
    · rfl

theorem last_push {fs2 : List (Nat × Nat)} {B S E : Nat} {tl : Nat → Byte}
    (hE : B + S = heap + 16 * (E + 1)) (htl : ∀ j < 256, j ≠ E → tl j = lastT fs2 j) :
    ∀ j < 256, Function.update tl E 1 j = lastT ((B, S) :: fs2) j := by
  intro j hj
  rw [lastT_cons]
  by_cases e : j = E
  · subst e; simp [hE]
  · rw [Function.update_of_ne e, htl j hj e]
    split
    · rename_i h; simp only at h; omega
    · rfl

variable {sp ret : Word}

/-- **`0x4014a7`: size word, footer and table bytes of the merged block.** -/
theorem ftail (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (fs2 : List (Nat × Nat))
    (B S G X : Nat) (tl tf : Nat → Byte) (hw : WF fs2) (hgB : Good (B, S))
    (hap : ∀ y ∈ fs2, Apart (B, S) y) (hB : B = heap + 16 * G)
    (htf : ∀ j < 256, j ≠ G → tf j = firstT fs2 j)
    (htl : ∀ j < 256, j ≠ G + S / 16 - 1 → tl j = lastT fs2 j)
    (hrcx : f .rcx = wd B) (hrax : f .rax = wd S) (hrdx : f .rdx = wd G)
    (hr8 : f .r8 = wd G + wd (2 ^ 64 - 1)) (hrsi : f .rsi = wd (hdOr fs2 0))
    (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4014a7 f fl
      (blockAny B S ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA tl ∗ tblPt firstA tf ∗ dll fs2 0 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hF : firstA = 0x4031c0 := rfl
  have hL : lastA = 0x4030c0 := rfl
  have hg := hgB; unfold Good at hg; simp only at hg
  have hG : G < 256 := by omega
  have hE : G + S / 16 - 1 < 256 := by omega
  have hBS : B + S = heap + 16 * (G + S / 16 - 1 + 1) := by omega
  refine SPEC.mem (M' := blockAny B 8 ∗ (blockAny (B + 8) 8 ∗ blockAny (B + 16) 8 ∗
      blockAny (B + 24) (S - 32) ∗ blockAny (B + S - 8) 8 ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗
      tblPt lastA tl ∗ tblPt firstA tf ∗ dll fs2 0 0))
    (by rw [split5 B S hg.2.2.2.2]; ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 375) (k := 3)
    (pc := 0x4014a7) (pc' := 0x4014aa) (by decide) (fit 375 3) (base := .rcx) (src := .rax)
    (by decide) (by decide) (by decide) (disp := 0x0) (entails_refl _) d375 (by decide)
    (by rw [hrcx]; exact addr_add (v := B) (D := 0) (by decide +kernel) (by omega))) ?_
  refine SPEC.mem (M' := blockAny (B + S - 8) 8 ∗ (wordPt B (f .rax) ∗ blockAny (B + 8) 8 ∗
      blockAny (B + 16) 8 ∗ blockAny (B + 24) (S - 32) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗
      tblPt lastA tl ∗ tblPt firstA tf ∗ dll fs2 0 0)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeM E (b := 0x401330) (code := code) (o := 378) (k := 5)
    (pc := 0x4014aa) (by decide) (fit 378 5) (src := .rax) (by decide) (entails_refl _) d378
    (addr_idx (r := .rcx) (q := .rax) (by decide) (by decide) (by decide) (v := wd B) (u := wd S)
      hrcx hrax (by rw [wd_add]; exact addr_sub (by decide +kernel) (by omega) (by omega)))) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 383) (k := 4)
    (pc := 0x4014aa + BitVec.ofNat 64 5) (by decide) (fit 383 4) (r := .rax) (by decide)
    (c := 0x4) (by decide) d383) ?_
  rw [hrax, shr4_wd (by omega)]
  refine SPEC.mem (M' := bytePt (firstA + G) (tf G) ∗ (tblR firstA tf G ∗
      wordPt (B + S - 8) (wd S) ∗ wordPt B (wd S) ∗ blockAny (B + 8) 8 ∗
      blockAny (B + 16) 8 ∗ blockAny (B + 24) (S - 32) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ dll fs2 0 0))
    (by rw [tbl_split firstA tf hG]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 387) (k := 7)
    (pc := 0x4014aa + BitVec.ofNat 64 5 + BitVec.ofNat 64 4) (by decide) (fit 387 7)
    (bytePt_blockAny _ _) d387
    (addr_reg (r := .rdx) (by decide) (by simp only [Function.update_apply, reduceCtorEq,
      ↓reduceIte, hrdx]) (addr_tbl (by decide +kernel) (by omega)))) ?_
  refine SPEC.mem (M' := bytePt (lastA + (G + S / 16 - 1)) (tl (G + S / 16 - 1)) ∗
      (tblR lastA tl (G + S / 16 - 1) ∗ bytePt (firstA + G) 1 ∗ tblR firstA tf G ∗
      wordPt (B + S - 8) (wd S) ∗ wordPt B (wd S) ∗ blockAny (B + 8) 8 ∗
      blockAny (B + 16) 8 ∗ blockAny (B + 24) (S - 32) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗ dll fs2 0 0))
    (by rw [tbl_split lastA tl hE]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 394) (k := 9)
    (pc := 0x4014aa + BitVec.ofNat 64 5 + BitVec.ofNat 64 4 + BitVec.ofNat 64 7) (by decide)
    (fit 394 9) (bytePt_blockAny _ _) d394
    (addr_idx (r := .r8) (q := .rax) (by decide) (by decide) (by decide)
      (v := wd G + wd (2 ^ 64 - 1)) (u := wd (S / 16))
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr8])
      (by simp only [Function.update_self])
      (by rw [show BitVec.signExtend 64 (0x4030c0 : BitVec 32) = wd 0x4030c0 by decide +kernel,
            wd_add, wd_add, wd_add]
          simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega))) ?_
  refine SPEC.mem ?_ (ftail2 x _ _ fs2 B S X (wf_cons hw hgB hap)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
  rw [← tblPt_congr lastA (last_push hBS htl), ← tblPt_congr firstA (first_push hB htf),
    ← tbl_write lastA tl hE, ← tbl_write firstA tf hG]
  ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
