module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM3

/-!
# Proofs: rung 08 (boundary tags) — `malloc` unlinks the block it hands out whole

`u_l2` (`0x4013ad`): the successor's `prev` becomes the predecessor; `u_l1` (`0x4013a4`): the
predecessor's `next` (or `flist`) becomes the successor; `tail_unlink` (`0x40139c`) loads both
links first.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Boundary
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.MemStep

theorem hdOr_lt {l : List (Nat × Nat)} (hg : ∀ y ∈ l, Good y) (n : Nat) (hn : n < 2 ^ 64) :
    hdOr l n < 2 ^ 64 := by
  cases l with
  | nil => exact hn
  | cons x l =>
    have := good_lt hg ⟨x, List.mem_cons_self, rfl⟩; have := heap_eq; simp only [hdOr]; omega

theorem lastOr_lt {l : List (Nat × Nat)} (hg : ∀ y ∈ l, Good y) (p : Nat) (hp : p < 2 ^ 64) :
    lastOr l p < 2 ^ 64 := by
  by_cases hl : l = []
  · subst hl; exact hp
  · have := good_lt hg (lastOr_mem p hl); have := heap_eq; omega

theorem hdOr_snoc (l : List (Nat × Nat)) (p : Nat × Nat) (m : List (Nat × Nat)) (n n' : Nat) :
    hdOr (l ++ [p] ++ m) n = hdOr (l ++ [p]) n' := by cases l <;> rfl

variable {nw sp ret : Word}

/-- `0x4013ad`: the successor's `prev`. -/
theorem u_l2 (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat)) (y : Nat × Nat)
    (hw : WF (l1 ++ y :: l2)) (hn : nw.toNat + 16 ≤ y.2)
    (hrax : f .rax = wd y.1) (hrsi : f .rsi = wd ((y.1 - heap) / 16))
    (hr8 : f .r8 = wd ((y.1 - heap) / 16 + y.2 / 16 - 1)) (hrsp : f .rsp = sp)
    (hrcx : f .rcx = wd (lastOr l1 0)) (hrdx : f .rdx = wd (hdOr l2 0)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013ad f fl
      (blk y (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 (hdOr l2 0) ∗ dll l2 y.1 0))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hg := hw.1
  have hH := heap_eq
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 125) (k := 3) (pc := 0x4013ad)
    (by decide) (fit 125 3) (r := .rdx) (by decide) d125) ?_
  cases l2 with
  | nil =>
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 128) (k := 2)
      (pc := 0x4013ad + BitVec.ofNat 64 3) (pc' := 0x4013b6) (by decide) (fit 128 2) (c := .e)
      (rel := 0x4) (by rw [hrdx, eval_e_wd (by decide)]; rfl) d128 (by decide)) ?_
    exact u_fin f _ l1 [] y hw hn _ _ hrax hrsi hr8 hrsp
  | cons z l2' =>
    have hz := good_lt hg ⟨z, by simp, rfl⟩
    have hz0 : hdOr (z :: l2') 0 ≠ 0 := by simp only [hdOr]; omega
    have hz64 : hdOr (z :: l2') 0 < 2 ^ 64 := by simp only [hdOr]; omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 128) (k := 2)
      (pc := 0x4013ad + BitVec.ofNat 64 3) (pc' := 0x4013b2) (by decide) (fit 128 2) (c := .e)
      (rel := 0x4) (by rw [hrdx, eval_e_wd hz64]; simp [hz0])
      d128 (by decide)) ?_
    refine SPEC.mem (M' := wordPt (z.1 + 16) (wd y.1) ∗ (wordPt z.1 (wd z.2) ∗
      wordPt (z.1 + 8) (wd (hdOr l2' 0)) ∗ blockAny (z.1 + 24) (z.2 - 32) ∗
      wordPt (z.1 + z.2 - 8) (wd z.2) ∗ dll l2' z.1 0 ∗
      blk y (hdOr (z :: l2') 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr l1 (hdOr (z :: l2') 0))) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: z :: l2')) ∗
        tblPt firstA (firstT (l1 ++ y :: z :: l2')) ∗ dll l1 0 (hdOr (z :: l2') 0)))
      (by rw [dll_cons]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 130) (k := 4)
      (pc := 0x4013b2) (pc' := 0x4013b6) (by decide) (fit 130 4) (base := .rdx) (src := .rcx)
      (by decide) (by decide) (by decide) (disp := 0x10) (wordPt_blockAny _ _) d130 (by decide)
      (by rw [hrdx]; simp only [hdOr]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem ?_ (u_fin f _ l1 (z :: l2') y hw hn (hdOr (z :: l2') 0) (lastOr l1 0) hrax hrsi
      hr8 hrsp)
    rw [hrcx, dll_cons (l := l2')]; unfold blk; ac_rfl

/-- `0x4013a4`: the predecessor's `next`, or `flist` when `y` is the head. -/
theorem u_l1 (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat)) (y : Nat × Nat)
    (hw : WF (l1 ++ y :: l2)) (hn : nw.toNat + 16 ≤ y.2)
    (hrax : f .rax = wd y.1) (hrsi : f .rsi = wd ((y.1 - heap) / 16))
    (hr8 : f .r8 = wd ((y.1 - heap) / 16 + y.2 / 16 - 1)) (hrsp : f .rsp = sp)
    (hrcx : f .rcx = wd (lastOr l1 0)) (hrdx : f .rdx = wd (hdOr l2 0)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013a4 f fl
      (blk y (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hg := hw.1
  have hH := heap_eq
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 116) (k := 3) (pc := 0x4013a4)
    (by decide) (fit 116 3) (r := .rcx) (by decide) d116) ?_
  rcases l1.eq_nil_or_concat with rfl | ⟨l1', p, rfl⟩
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 119) (k := 2)
      (pc := 0x4013a4 + BitVec.ofNat 64 3) (pc' := 0x401408) (by decide) (fit 119 2) (c := .e)
      (rel := 0x5f) (by rw [hrcx, eval_e_wd (by decide)]; rfl) d119 (by decide)) ?_
    refine SPEC.mem (M' := wordPt flistA (wd (hdOr ([] ++ y :: l2) 0)) ∗
      (blk y (hdOr l2 0) (lastOr [] 0) ∗ wordPt sp.toNat ret ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT ([] ++ y :: l2)) ∗
        tblPt firstA (firstT ([] ++ y :: l2)) ∗ dll [] 0 y.1 ∗ dll l2 y.1 0)) (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 216) (k := 7)
      (pc := 0x401408) (pc' := 0x40140f) (by decide) (fit 216 7) (src := .rdx) (by decide)
      (disp := 0x1c91) (wordPt_blockAny _ _) d216 (by decide) (by decide)) ?_
    refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 223) (k := 2)
      (pc := 0x40140f) (pc' := 0x4013ad) (by decide) (fit 223 2) d223 (by decide)) ?_
    refine SPEC.mem ?_ (u_l2 f _ [] l2 y hw hn hrax hrsi hr8 hrsp hrcx hrdx)
    rw [hrdx]; simp only [hdOr, dll_nil]; ac_rfl
  · simp only [List.concat_eq_append] at hw hrcx hg ⊢
    have hp := good_lt hg ⟨p, by simp, rfl⟩
    have hp0 : lastOr (l1' ++ [p]) 0 ≠ 0 := by rw [lastOr_snoc]; omega
    have hp64 : lastOr (l1' ++ [p]) 0 < 2 ^ 64 := by rw [lastOr_snoc]; omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 119) (k := 2)
      (pc := 0x4013a4 + BitVec.ofNat 64 3) (pc' := 0x4013a9) (by decide) (fit 119 2) (c := .e)
      (rel := 0x5f) (by rw [hrcx, eval_e_wd hp64]; simp [hp0]) d119 (by decide)) ?_
    refine SPEC.mem (M' := wordPt (p.1 + 8) (wd y.1) ∗ (wordPt p.1 (wd p.2) ∗
      wordPt (p.1 + 16) (wd (lastOr l1' 0)) ∗ blockAny (p.1 + 24) (p.2 - 32) ∗
      wordPt (p.1 + p.2 - 8) (wd p.2) ∗ dll l1' 0 p.1 ∗
      blk y (hdOr l2 0) (lastOr (l1' ++ [p]) 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1' ++ [p] ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1' ++ [p] ++ y :: l2)) ∗
        tblPt firstA (firstT (l1' ++ [p] ++ y :: l2)) ∗ dll l2 y.1 0))
      (by rw [dll_snoc]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 121) (k := 4)
      (pc := 0x4013a9) (pc' := 0x4013ad) (by decide) (fit 121 4) (base := .rcx) (src := .rdx)
      (by decide) (by decide) (by decide) (disp := 0x8) (wordPt_blockAny _ _) d121 (by decide)
      (by rw [hrcx, lastOr_snoc]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem ?_ (u_l2 f _ (l1' ++ [p]) l2 y hw hn hrax hrsi hr8 hrsp hrcx hrdx)
    rw [hrdx, dll_snoc, hdOr_snoc l1' p (y :: l2) 0 (hdOr l2 0)]; unfold blk; ac_rfl

/-- **`0x40139c`: hand out the whole block `y`.** -/
theorem tail_unlink (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat)) (y : Nat × Nat)
    (hw : WF (l1 ++ y :: l2)) (hn : nw.toNat + 16 ≤ y.2)
    (hrax : f .rax = wd y.1) (hrsi : f .rsi = wd ((y.1 - heap) / 16))
    (hr8 : f .r8 = wd ((y.1 - heap) / 16 + y.2 / 16 - 1)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40139c f fl
      (blk y (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hy := (wf_mid hw).1; unfold Good at hy
  refine SPEC.mem (M' := wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ (wordPt y.1 (wd y.2) ∗
      wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 108) (k := 4)
    (pc := 0x40139c) (pc' := 0x4013a0) (by decide) (fit 108 4) (base := .rax) (dst := .rcx)
    (by decide) (by decide) (by decide) (disp := 0x10) d108 (by decide)
    (by rw [hrax]; exact addr_add (by decide +kernel) (by omega))) ?_
  refine SPEC.mem (M' := wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ (wordPt y.1 (wd y.2) ∗
      wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 112) (k := 4)
    (pc := 0x4013a0) (pc' := 0x4013a4) (by decide) (fit 112 4) (base := .rax) (dst := .rdx)
    (by decide) (by decide) (by decide) (disp := 0x8) d112 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]
        exact addr_add (by decide +kernel) (by omega))) ?_
  refine SPEC.mem ?_ (u_l1 _ _ l1 l2 y hw hn
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr8])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
    (by simp only [Function.update_self]))
  unfold blk; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
