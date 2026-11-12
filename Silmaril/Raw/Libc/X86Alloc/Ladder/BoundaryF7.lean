module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF6

/-!
# Proofs: rung 08 (boundary tags) — `free` unlinks the next free block

`fmerge_next` (`0x40145b`): `first[e]` is set, so a free block `nb` starts at granule `e`, where
the freed block ends. Its links are loaded through `r10 = 16 e`, and `nm_l1` (`0x401470`)
rewrites its predecessor's `next` (or `flist`).
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

/-- `shl $4`. -/
theorem shl4_wd {x : Nat} (hx : 16 * x < 2 ^ 64) :
    ShiftOp.shl.result (wd x) ((0x4 : BitVec 8).toNat % 64) = wd (16 * x) := by
  show wd x <<< ((0x4 : BitVec 8).toNat % 64) = _
  rw [show (0x4 : BitVec 8).toNat % 64 = 4 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_wd (by omega), toNat_wd hx, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]
  omega

variable {sp ret : Word}

/-- **`0x401470`: `nb`'s predecessor.** -/
theorem nm_l1 (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat))
    (nb : Nat × Nat) (b s g e : Nat) (hw : WF (l1 ++ nb :: l2)) (hgb : Good (b, s))
    (hap : ∀ y ∈ l1 ++ nb :: l2, Apart (b, s) y) (hb : b = heap + 16 * g) (hnb : nb.1 = b + s)
    (he : nb.1 = heap + 16 * e)
    (hrsi : f .rsi = wd e) (hr10 : f .r10 = wd (16 * e)) (hrax : f .rax = wd s)
    (hrcx : f .rcx = wd b) (hrdx : f .rdx = wd g) (hrdi : f .rdi = wd (b + 16))
    (hrsp : f .rsp = sp) (hr9 : f .r9 = wd (lastOr l1 0)) (hr8 : f .r8 = wd (hdOr l2 0)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401470 f fl
      (blockAny b s ∗ blk nb (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ nb :: l2) 0)) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT (l1 ++ nb :: l2)) ∗ tblPt firstA (firstT (l1 ++ nb :: l2)) ∗
        dll l1 0 nb.1 ∗ dll l2 nb.1 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hg := hw.1
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 320) (k := 3) (pc := 0x401470)
    (by decide) (fit 320 3) (r := .r9) (by decide) d320) ?_
  rcases l1.eq_nil_or_concat with rfl | ⟨l1', q, rfl⟩
  · refine SPEC.trans (c_jcc32_taken E (b := 0x401330) (code := code) (o := 323) (k := 6)
      (pc := 0x401470 + BitVec.ofNat 64 3) (pc' := 0x401550) (by decide) (fit 323 6) (c := .e)
      (rel := 0xd7) (by rw [hr9, eval_e_wd (by decide)]; rfl) d323 (by decide)) ?_
    refine SPEC.mem (M' := wordPt flistA (wd (hdOr ([] ++ nb :: l2) 0)) ∗ (blockAny b s ∗
        blk nb (hdOr l2 0) (lastOr [] 0) ∗ wordPt sp.toNat ret ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT ([] ++ nb :: l2)) ∗ tblPt firstA (firstT ([] ++ nb :: l2)) ∗
        dll [] 0 nb.1 ∗ dll l2 nb.1 0)) (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 544) (k := 7)
      (pc := 0x401550) (pc' := 0x401557) (by decide) (fit 544 7) (src := .r8) (by decide)
      (disp := 0x1b49) (wordPt_blockAny _ _) d544 (by decide) (by decide)) ?_
    refine SPEC.trans (c_jmp32 E (b := 0x401330) (code := code) (o := 551) (k := 5)
      (pc := 0x401557) (pc' := 0x40147d) (by decide) (fit 551 5) d551 (by decide)) ?_
    refine SPEC.mem ?_ (nm_l2 x f _ [] l2 nb b s g e hw hgb hap hb hnb he hrsi hr10 hrax hrcx
      hrdx hrdi hrsp hr9 hr8)
    rw [hr8]; simp only [hdOr, dll_nil]; ac_rfl
  · simp only [List.concat_eq_append] at hw hr9 hg hap ⊢
    have hq := good_lt hg ⟨q, by simp, rfl⟩
    have hq0 : lastOr (l1' ++ [q]) 0 ≠ 0 := by rw [lastOr_snoc]; omega
    have hq64 : lastOr (l1' ++ [q]) 0 < 2 ^ 64 := by rw [lastOr_snoc]; omega
    refine SPEC.trans (c_jcc32_not E (b := 0x401330) (code := code) (o := 323) (k := 6)
      (pc := 0x401470 + BitVec.ofNat 64 3) (by decide) (fit 323 6) (c := .e)
      (rel := 0xd7) (by rw [hr9, eval_e_wd hq64]; simp [hq0]) d323) ?_
    refine SPEC.mem (M' := wordPt (q.1 + 8) (wd nb.1) ∗ (wordPt q.1 (wd q.2) ∗
      wordPt (q.1 + 16) (wd (lastOr l1' 0)) ∗ blockAny (q.1 + 24) (q.2 - 32) ∗
      wordPt (q.1 + q.2 - 8) (wd q.2) ∗ dll l1' 0 q.1 ∗
      blockAny b s ∗ blk nb (hdOr l2 0) (lastOr (l1' ++ [q]) 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1' ++ [q] ++ nb :: l2) 0)) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT (l1' ++ [q] ++ nb :: l2)) ∗
        tblPt firstA (firstT (l1' ++ [q] ++ nb :: l2)) ∗ dll l2 nb.1 0))
      (by rw [dll_snoc]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 329) (k := 4)
      (pc := 0x401470 + BitVec.ofNat 64 3 + BitVec.ofNat 64 6) (pc' := 0x40147d) (by decide)
      (fit 329 4) (base := .r9) (src := .r8)
      (by decide) (by decide) (by decide) (disp := 0x8) (wordPt_blockAny _ _) d329 (by decide)
      (by rw [hr9, lastOr_snoc]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem ?_ (nm_l2 x f _ (l1' ++ [q]) l2 nb b s g e hw hgb hap hb hnb he hrsi hr10 hrax
      hrcx hrdx hrdi hrsp hr9 hr8)
    rw [hr8, dll_snoc, hdOr_snoc l1' q (nb :: l2) 0 (hdOr l2 0)]; unfold blk; ac_rfl

/-- **`0x40145b`: the next free block, from `first[e]`.** -/
theorem fmerge_next (x : Word × Option Nat) (f : Reg → Word) (fl : Flags)
    (l1 l2 : List (Nat × Nat)) (nb : Nat × Nat) (b s g e : Nat) (hw : WF (l1 ++ nb :: l2))
    (hgb : Good (b, s)) (hap : ∀ y ∈ l1 ++ nb :: l2, Apart (b, s) y) (hb : b = heap + 16 * g)
    (hnb : nb.1 = b + s) (he : nb.1 = heap + 16 * e)
    (hrsi : f .rsi = wd e) (hrax : f .rax = wd s) (hrcx : f .rcx = wd b) (hrdx : f .rdx = wd g)
    (hrdi : f .rdi = wd (b + 16)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40145b f fl
      (blockAny b s ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr (l1 ++ nb :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ nb :: l2)) ∗
        tblPt firstA (firstT (l1 ++ nb :: l2)) ∗
        dll l1 0 nb.1 ∗ blk nb (hdOr l2 0) (lastOr l1 0) ∗ dll l2 nb.1 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hn := (wf_mid hw).1; unfold Good at hn
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 299) (k := 3)
    (pc := 0x40145b) (by decide) (fit 299 3) (r := .r10) (q := .rsi) (by decide) (by decide)
    (by decide) d299) ?_
  refine SPEC.trans (c_shl E (b := 0x401330) (code := code) (o := 302) (k := 4)
    (pc := 0x40145b + BitVec.ofNat 64 3) (by decide) (fit 302 4) (r := .r10) (by decide)
    (c := 0x4) (by decide) d302) ?_
  have h10 : ShiftOp.shl.result (wd e) ((0x4 : BitVec 8).toNat % 64) = wd (16 * e) :=
    shl4_wd (by omega)
  refine SPEC.mem (M' := wordPt (nb.1 + 16) (wd (lastOr l1 0)) ∗ (wordPt nb.1 (wd nb.2) ∗
      wordPt (nb.1 + 8) (wd (hdOr l2 0)) ∗ blockAny (nb.1 + 24) (nb.2 - 32) ∗
      wordPt (nb.1 + nb.2 - 8) (wd nb.2) ∗ blockAny b s ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ nb :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ nb :: l2)) ∗
      tblPt firstA (firstT (l1 ++ nb :: l2)) ∗ dll l1 0 nb.1 ∗ dll l2 nb.1 0))
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 306) (k := 7)
    (pc := 0x40145b + BitVec.ofNat 64 3 + BitVec.ofNat 64 4) (pc' := 0x401469) (by decide)
    (fit 306 7) (base := .r10) (dst := .r9) (by decide) (by decide) (by decide)
    (disp := 0x4032d0) d306 (by decide)
    (by simp only [Function.update_self, Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]
        rw [h10]
        exact (addr_add (D := 0x4032d0) (by decide +kernel) (by omega)).trans (by omega))) ?_
  refine SPEC.mem (M' := wordPt (nb.1 + 8) (wd (hdOr l2 0)) ∗
      (wordPt (nb.1 + 16) (wd (lastOr l1 0)) ∗ wordPt nb.1 (wd nb.2) ∗
      blockAny (nb.1 + 24) (nb.2 - 32) ∗
      wordPt (nb.1 + nb.2 - 8) (wd nb.2) ∗ blockAny b s ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ nb :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ nb :: l2)) ∗
      tblPt firstA (firstT (l1 ++ nb :: l2)) ∗ dll l1 0 nb.1 ∗ dll l2 nb.1 0))
    (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 313) (k := 7)
    (pc := 0x401469) (pc' := 0x401470) (by decide)
    (fit 313 7) (base := .r10) (dst := .r8) (by decide) (by decide) (by decide)
    (disp := 0x4032c8) d313 (by decide)
    (by simp only [Function.update_self, Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]
        rw [h10]
        exact (addr_add (D := 0x4032c8) (by decide +kernel) (by omega)).trans (by omega))) ?_
  refine SPEC.mem ?_ (nm_l1 x _ _ l1 l2 nb b s g e hw hgb hap hb hnb he
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrsi]
        exact h10)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
    (by simp only [Function.update_self]))
  unfold blk; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
