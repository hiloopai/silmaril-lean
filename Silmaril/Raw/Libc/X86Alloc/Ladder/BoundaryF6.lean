module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF5

/-!
# Proofs: rung 08 (boundary tags) — `free` merges with the next free block

`nm_fin` (`0x401486`): the free block `nb` that starts where the freed block ends (granule `e`)
is unlinked; `first[e]` is cleared and the size grows by `nb`'s size, read from its size word.
`last` still marks `nb`'s last granule, which is now the pending block's: right for the new list
except at that byte, which the push sets anyway. `nm_l2` (`0x40147d`): `nb`'s successor.
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

/-- **`0x401486`: absorb `nb`.** -/
theorem nm_fin (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat))
    (nb : Nat × Nat) (b s g e nx pv : Nat) (hw : WF (l1 ++ nb :: l2)) (hgb : Good (b, s))
    (hap : ∀ y ∈ l1 ++ nb :: l2, Apart (b, s) y) (hb : b = heap + 16 * g) (hnb : nb.1 = b + s)
    (he : nb.1 = heap + 16 * e)
    (hrsi : f .rsi = wd e) (hr10 : f .r10 = wd (16 * e)) (hrax : f .rax = wd s)
    (hrcx : f .rcx = wd b) (hrdx : f .rdx = wd g) (hrdi : f .rdi = wd (b + 16))
    (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401486 f fl
      (blockAny b s ∗ blk nb nx pv ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT (l1 ++ nb :: l2)) ∗ tblPt firstA (firstT (l1 ++ nb :: l2)) ∗
        dll l1 0 (hdOr l2 0) ∗ dll l2 (lastOr l1 0) 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hF : firstA = 0x4031c0 := rfl
  obtain ⟨hgn, hw', hapn⟩ := wf_mid hw
  have hn := hgn; unfold Good at hn
  have hg := hgb; unfold Good at hg; simp only at hg
  have he256 : e < 256 := by omega
  refine SPEC.mem (M' := bytePt (firstA + e) (firstT (l1 ++ nb :: l2) e) ∗
      (tblR firstA (firstT (l1 ++ nb :: l2)) e ∗ blockAny b s ∗ blk nb nx pv ∗
        wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ nb :: l2)) ∗
        dll l1 0 (hdOr l2 0) ∗ dll l2 (lastOr l1 0) 0))
    (by rw [tbl_split firstA _ he256]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 342) (k := 7)
    (pc := 0x401486) (by decide) (fit 342 7) (bytePt_blockAny _ _) d342
    (addr_reg (r := .rsi) (by decide) hrsi (addr_tbl (by decide +kernel) (by omega)))) ?_
  refine SPEC.mem (M' := wordPt nb.1 (wd nb.2) ∗ (bytePt (firstA + e) 0 ∗
      tblR firstA (firstT (l1 ++ nb :: l2)) e ∗ blockAny b s ∗
      wordPt (nb.1 + 8) (wd nx) ∗ wordPt (nb.1 + 16) (wd pv) ∗
      blockAny (nb.1 + 24) (nb.2 - 32) ∗ wordPt (nb.1 + nb.2 - 8) (wd nb.2) ∗
      wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ nb :: l2)) ∗
      dll l1 0 (hdOr l2 0) ∗ dll l2 (lastOr l1 0) 0))
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_aluM E (b := 0x401330) (code := code) (o := 349) (k := 7)
    (pc := 0x401486 + BitVec.ofNat 64 7) (by decide) (fit 349 7) (op := .add) (by decide)
    (dst := .rax) (by decide) d349
    (addr_reg (r := .r10) (by decide) hr10 ((addr_add (D := 0x4032c0) (by decide +kernel)
      (by omega)).trans (by omega)))) ?_
  refine SPEC.memPre (M' := blockAny b (s + nb.2) ∗ (wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ l2) 0)) ∗ blockAny (flistA + 8) 24 ∗
      tblPt lastA (lastT (l1 ++ nb :: l2)) ∗ tblPt firstA (firstT (l1 ++ l2)) ∗
      dll (l1 ++ l2) 0 0)) ?_ ?_
  · refine entails_trans (entails_of_eq (show _ = ((blk nb nx pv ∗ blockAny b s) ∗
        (wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr (l1 ++ l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ nb :: l2)) ∗
        tblPt firstA (firstT (l1 ++ l2)) ∗ dll (l1 ++ l2) 0 0)) by
          rw [dll_append, hdOr_append, ← tblPt_congr firstA (first_clear hw he),
            ← tbl_write firstA _ he256]
          unfold blk; ac_rfl)) (sep_mono_left _ ?_)
    rw [blockAny_add, show b + s = nb.1 by omega, sep_comm]
    exact sep_mono_right _ (blk_blockAny nb hn.2.2.2.2 nx pv)
  exact fprev x _ _ (l1 ++ l2) b (s + nb.2) g (lastT (l1 ++ nb :: l2)) hw'
    (by unfold Good; simp only; omega)
    (fun y hy => by
      have h1 := hapn y hy; have h2 := hap y (mem_mid hy); have h3 := hw'.1 y hy
      unfold Apart at h1 h2 ⊢; unfold Good at h3; simp only at h1 h2 ⊢; omega) hb
    (fun j _ hj => (lastT_mid_ne (l1 := l1) (l2 := l2) (x := nb) (by omega)).symm)
    (by simp only [Function.update_self, hrax]; exact wd_add _ _)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])

/-- **`0x40147d`: `nb`'s successor.** -/
theorem nm_l2 (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat))
    (nb : Nat × Nat) (b s g e : Nat) (hw : WF (l1 ++ nb :: l2)) (hgb : Good (b, s))
    (hap : ∀ y ∈ l1 ++ nb :: l2, Apart (b, s) y) (hb : b = heap + 16 * g) (hnb : nb.1 = b + s)
    (he : nb.1 = heap + 16 * e)
    (hrsi : f .rsi = wd e) (hr10 : f .r10 = wd (16 * e)) (hrax : f .rax = wd s)
    (hrcx : f .rcx = wd b) (hrdx : f .rdx = wd g) (hrdi : f .rdi = wd (b + 16))
    (hrsp : f .rsp = sp) (hr9 : f .r9 = wd (lastOr l1 0)) (hr8 : f .r8 = wd (hdOr l2 0)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40147d f fl
      (blockAny b s ∗ blk nb (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT (l1 ++ nb :: l2)) ∗ tblPt firstA (firstT (l1 ++ nb :: l2)) ∗
        dll l1 0 (hdOr l2 0) ∗ dll l2 nb.1 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hg := hw.1
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 333) (k := 3) (pc := 0x40147d)
    (by decide) (fit 333 3) (r := .r8) (by decide) d333) ?_
  cases l2 with
  | nil =>
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 336) (k := 2)
      (pc := 0x40147d + BitVec.ofNat 64 3) (pc' := 0x401486) (by decide) (fit 336 2) (c := .e)
      (rel := 0x4) (by rw [hr8, eval_e_wd (by decide)]; rfl) d336 (by decide)) ?_
    exact nm_fin x f _ l1 [] nb b s g e _ _ hw hgb hap hb hnb he hrsi hr10 hrax hrcx hrdx hrdi hrsp
  | cons z l2' =>
    have hz := good_lt hg ⟨z, by simp, rfl⟩
    have hz0 : hdOr (z :: l2') 0 ≠ 0 := by simp only [hdOr]; omega
    have hz64 : hdOr (z :: l2') 0 < 2 ^ 64 := by simp only [hdOr]; omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 336) (k := 2)
      (pc := 0x40147d + BitVec.ofNat 64 3) (pc' := 0x401482) (by decide) (fit 336 2) (c := .e)
      (rel := 0x4) (by rw [hr8, eval_e_wd hz64]; simp [hz0]) d336 (by decide)) ?_
    refine SPEC.mem (M' := wordPt (z.1 + 16) (wd nb.1) ∗ (wordPt z.1 (wd z.2) ∗
      wordPt (z.1 + 8) (wd (hdOr l2' 0)) ∗ blockAny (z.1 + 24) (z.2 - 32) ∗
      wordPt (z.1 + z.2 - 8) (wd z.2) ∗ dll l2' z.1 0 ∗
      blockAny b s ∗ blk nb (hdOr (z :: l2') 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr l1 (hdOr (z :: l2') 0))) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT (l1 ++ nb :: z :: l2')) ∗ tblPt firstA (firstT (l1 ++ nb :: z :: l2')) ∗
        dll l1 0 (hdOr (z :: l2') 0)))
      (by rw [dll_cons]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 338) (k := 4)
      (pc := 0x401482) (pc' := 0x401486) (by decide) (fit 338 4) (base := .r8) (src := .r9)
      (by decide) (by decide) (by decide) (disp := 0x10) (wordPt_blockAny _ _) d338 (by decide)
      (by rw [hr8]; simp only [hdOr]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem ?_ (nm_fin x f _ l1 (z :: l2') nb b s g e (hdOr (z :: l2') 0) (lastOr l1 0)
      hw hgb hap hb hnb he hrsi hr10 hrax hrcx hrdx hrdi hrsp)
    rw [hr9, dll_cons (l := l2')]; unfold blk; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
