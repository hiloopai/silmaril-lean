module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF7

/-!
# Proofs: rung 08 (boundary tags) — the entry of `free`

`fentry` (`0x401420`, `p ≠ 0`): the size `s` is read from the token's size word, the token and
the request are folded into the block `[b, b + s)` (`b = p - 16`), and its granule `g` and the
granule `e = g + s/16` after it are computed. The block is apart from every free block (by
separation, `apart_of_sep`). `fdispatch` (`0x401449`): for `e ≤ 255` with `first[e]` set, merge
with the next block (`fmerge_next`); otherwise go on to the previous one (`fprev`).
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

variable {sp ret : Word}

/-- **`0x401449`: is there a free block after the freed one?** -/
theorem fdispatch (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (fs : List (Nat × Nat))
    (b s g e : Nat) (hw : WF fs) (hgb : Good (b, s)) (hap : ∀ y ∈ fs, Apart (b, s) y)
    (hb : b = heap + 16 * g) (he : e = g + s / 16)
    (hrsi : f .rsi = wd e) (hrax : f .rax = wd s) (hrcx : f .rcx = wd b) (hrdx : f .rdx = wd g)
    (hrdi : f .rdi = wd (b + 16)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401449 f fl
      (blockAny b s ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT fs) ∗ tblPt firstA (firstT fs) ∗
        dll fs 0 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hF : firstA = 0x4031c0 := rfl
  have hg := hgb; unfold Good at hg; simp only at hg
  refine SPEC.trans (c_cmpI E (b := 0x401330) (code := code) (o := 281) (k := 7) (pc := 0x401449)
    (by decide) (fit 281 7) (r := .rsi) (imm := 0xff) (by decide) d281) ?_
  have e255 : (BitVec.signExtend 64 (0xff : BitVec 32)).toNat = 255 := by decide +kernel
  have hprev := fun fl' => fprev (sp := sp) (ret := ret) x f fl' fs b s g (lastT fs) hw hgb hap hb (fun _ _ _ => rfl) hrax hrcx hrdx
    hrdi hrsp
  by_cases hbig : 255 < e
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 288) (k := 2)
      (pc := 0x401449 + BitVec.ofNat 64 7) (pc' := 0x401494) (by decide) (fit 288 2) (c := .a)
      (rel := 0x42) (by rw [eval_a_cmp, hrsi, e255, toNat_wd (by omega)]; simp [hbig]) d288
      (by decide)) ?_
    exact hprev _
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 288) (k := 2)
      (pc := 0x401449 + BitVec.ofNat 64 7) (pc' := 0x401452) (by decide) (fit 288 2) (c := .a)
      (rel := 0x42) (by rw [eval_a_cmp, hrsi, e255, toNat_wd (by omega)]; simp [hbig]) d288
      (by decide)) ?_
    have he256 : e < 256 := by omega
    refine SPEC.mem (M' := bytePt (firstA + e) (firstT fs e) ∗ (tblR firstA (firstT fs) e ∗
        blockAny b s ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT fs) ∗ dll fs 0 0))
      (by rw [tbl_split firstA _ he256]; ac_rfl) ?_
    refine SPEC.trans (c_cmpB E (b := 0x401330) (code := code) (o := 290) (k := 7)
      (pc := 0x401452) (by decide) (fit 290 7) d290
      (addr_reg (r := .rsi) (by decide) hrsi (addr_tbl (by decide +kernel) (by omega)))) ?_
    have hfold : (bytePt (firstA + e) (firstT fs e) ∗ (tblR firstA (firstT fs) e ∗
        blockAny b s ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT fs) ∗ dll fs 0 0)) =
        (blockAny b s ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT fs) ∗ tblPt firstA (firstT fs) ∗
        dll fs 0 0) := by rw [tbl_split firstA _ he256]; ac_rfl
    rcases firstT_cases fs e with h0 | h1
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 297) (k := 2)
        (pc := 0x401452 + BitVec.ofNat 64 7) (pc' := 0x401494) (by decide) (fit 297 2) (c := .e)
        (rel := 0x39) (by rw [eval_e_sub0, h0]; rfl) d297 (by decide)) ?_
      rw [hfold]; exact hprev _
    · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 297) (k := 2)
        (pc := 0x401452 + BitVec.ofNat 64 7) (pc' := 0x40145b) (by decide) (fit 297 2) (c := .e)
        (rel := 0x39) (by rw [eval_e_sub0, h1]; rfl) d297 (by decide)) ?_
      rw [hfold]
      obtain ⟨nb, hnbm, hnbe⟩ := firstT_one.1 h1
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hnbm
      refine SPEC.mem ?_ (fmerge_next x f _ l1 l2 nb b s g e hw hgb hap hb (by omega) hnbe hrsi
        hrax hrcx hrdx hrdi hrsp)
      rw [dll_mid]

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
