module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF3

/-!
# Proofs: rung 08 (boundary tags) — `free` finds and unlinks the previous free block

`fmerge_prev` (`0x401500`): `last[g - 1]` is set, so a free block `pb` ends where the freed
block starts; its footer, at `b - 8`, gives its size and so its start. Its links are loaded and
`pm_l1` (`0x40150f`) rewrites its predecessor's `next`; when `pb` is the head the new head is kept
in `rsi` (the push overwrites `flist`).
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

/-- **`0x40150f`: `pb`'s predecessor.** -/
theorem pm_l1 (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (m1 m2 : List (Nat × Nat))
    (pb : Nat × Nat) (b S g : Nat) (tl : Nat → Byte) (hw : WF (m1 ++ pb :: m2))
    (hgb : Good (b, S)) (hap : ∀ y ∈ m1 ++ pb :: m2, Apart (b, S) y) (hb : b = heap + 16 * g)
    (hpb : pb.1 + pb.2 = b) (hg1 : 1 ≤ g)
    (htl : ∀ j < 256, j ≠ g + S / 16 - 1 → tl j = lastT (m1 ++ pb :: m2) j)
    (hrcx : f .rcx = wd pb.1) (hr9 : f .r9 = wd pb.2) (hrax : f .rax = wd S)
    (hr8 : f .r8 = wd g + wd (2 ^ 64 - 1))
    (hrdi : f .rdi = wd (lastOr m1 0)) (hrdx : f .rdx = wd (hdOr m2 0)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40150f f fl
      (blockAny b S ∗ blk pb (hdOr m2 0) (lastOr m1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (m1 ++ pb :: m2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
        dll m1 0 pb.1 ∗ dll m2 pb.1 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hg := hw.1
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 479) (k := 3) (pc := 0x40150f)
    (by decide) (fit 479 3) (r := .rdi) (by decide) d479) ?_
  rcases m1.eq_nil_or_concat with rfl | ⟨m1', q, rfl⟩
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 482) (k := 2)
      (pc := 0x40150f + BitVec.ofNat 64 3) (pc' := 0x401560) (by decide) (fit 482 2) (c := .e)
      (rel := 0x4c) (by rw [hrdi, eval_e_wd (by decide)]; rfl) d482 (by decide)) ?_
    refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 560) (k := 3)
      (pc := 0x401560) (by decide) (fit 560 3) (r := .rsi) (q := .rdx) (by decide) (by decide)
      (by decide) d560) ?_
    refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 563) (k := 2)
      (pc := 0x401560 + BitVec.ofNat 64 3) (pc' := 0x40151f) (by decide) (fit 563 2) d563
      (by decide)) ?_
    refine SPEC.mem ?_ (pm_l2 x _ _ [] m2 pb b S g (hdOr ([] ++ pb :: m2) 0) tl hw hgb hap hb hpb
      hg1 htl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr9])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr8])
      (by simp only [Function.update_self, hrdx]; rfl)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
    simp only [dll_nil]
  · simp only [List.concat_eq_append] at hw hrdi hg hap htl ⊢
    have hq := good_lt hg ⟨q, by simp, rfl⟩
    have hq0 : lastOr (m1' ++ [q]) 0 ≠ 0 := by rw [lastOr_snoc]; omega
    have hq64 : lastOr (m1' ++ [q]) 0 < 2 ^ 64 := by rw [lastOr_snoc]; omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 482) (k := 2)
      (pc := 0x40150f + BitVec.ofNat 64 3) (pc' := 0x401514) (by decide) (fit 482 2) (c := .e)
      (rel := 0x4c) (by rw [hrdi, eval_e_wd hq64]; simp [hq0]) d482 (by decide)) ?_
    refine SPEC.mem (M' := wordPt (q.1 + 8) (wd pb.1) ∗ (wordPt q.1 (wd q.2) ∗
      wordPt (q.1 + 16) (wd (lastOr m1' 0)) ∗ blockAny (q.1 + 24) (q.2 - 32) ∗
      wordPt (q.1 + q.2 - 8) (wd q.2) ∗ dll m1' 0 q.1 ∗
      blockAny b S ∗ blk pb (hdOr m2 0) (lastOr (m1' ++ [q]) 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (m1' ++ [q] ++ pb :: m2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗
        tblPt firstA (firstT (m1' ++ [q] ++ pb :: m2)) ∗ dll m2 pb.1 0))
      (by rw [dll_snoc]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 484) (k := 4)
      (pc := 0x401514) (pc' := 0x401518) (by decide) (fit 484 4) (base := .rdi) (src := .rdx)
      (by decide) (by decide) (by decide) (disp := 0x8) (wordPt_blockAny _ _) d484 (by decide)
      (by rw [hrdi, lastOr_snoc]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem (M' := wordPt flistA (wd (hdOr (m1' ++ [q] ++ pb :: m2) 0)) ∗
      (wordPt (q.1 + 8) (f .rdx) ∗ wordPt q.1 (wd q.2) ∗
      wordPt (q.1 + 16) (wd (lastOr m1' 0)) ∗ blockAny (q.1 + 24) (q.2 - 32) ∗
      wordPt (q.1 + q.2 - 8) (wd q.2) ∗ dll m1' 0 q.1 ∗
      blockAny b S ∗ blk pb (hdOr m2 0) (lastOr (m1' ++ [q]) 0) ∗ wordPt sp.toNat ret ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗
        tblPt firstA (firstT (m1' ++ [q] ++ pb :: m2)) ∗ dll m2 pb.1 0)) (by ac_rfl) ?_
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 488) (k := 7)
      (pc := 0x401518) (pc' := 0x40151f) (by decide) (fit 488 7) (dst := .rsi) (by decide)
      (disp := 0x1b81) d488 (by decide) (by decide)) ?_
    refine SPEC.mem ?_ (pm_l2 x _ _ (m1' ++ [q]) m2 pb b S g
      (hdOr (m1' ++ [q] ++ pb :: m2) 0) tl hw hgb hap hb hpb hg1 htl
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr9])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr8])
      (by simp only [Function.update_self]; rw [hdOr_snoc m1' q (pb :: m2) 0 0,
            hdOr_snoc m1' q m2 0 0])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
    rw [hrdx, dll_snoc]; unfold blk; ac_rfl

/-- **`0x401500`: the previous free block, from the footer at `b - 8`.** -/
theorem fmerge_prev (x : Word × Option Nat) (f : Reg → Word) (fl : Flags)
    (m1 m2 : List (Nat × Nat)) (pb : Nat × Nat) (b S g : Nat) (tl : Nat → Byte)
    (hw : WF (m1 ++ pb :: m2)) (hgb : Good (b, S)) (hap : ∀ y ∈ m1 ++ pb :: m2, Apart (b, S) y)
    (hb : b = heap + 16 * g) (hpb : pb.1 + pb.2 = b) (hg1 : 1 ≤ g)
    (htl : ∀ j < 256, j ≠ g + S / 16 - 1 → tl j = lastT (m1 ++ pb :: m2) j)
    (hrdi : f .rdi = wd (b + 16)) (hrcx : f .rcx = wd b) (hrax : f .rax = wd S)
    (hr8 : f .r8 = wd g + wd (2 ^ 64 - 1)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401500 f fl
      (blockAny b S ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr (m1 ++ pb :: m2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
        dll m1 0 pb.1 ∗ blk pb (hdOr m2 0) (lastOr m1 0) ∗ dll m2 pb.1 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hp := (wf_mid hw).1; unfold Good at hp
  have hg := hgb; unfold Good at hg; simp only at hg
  refine SPEC.mem (M' := wordPt (pb.1 + pb.2 - 8) (wd pb.2) ∗ (wordPt pb.1 (wd pb.2) ∗
      wordPt (pb.1 + 8) (wd (hdOr m2 0)) ∗ wordPt (pb.1 + 16) (wd (lastOr m1 0)) ∗
      blockAny (pb.1 + 24) (pb.2 - 32) ∗ blockAny b S ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (m1 ++ pb :: m2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
      dll m1 0 pb.1 ∗ dll m2 pb.1 0))
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 464) (k := 4)
    (pc := 0x401500) (pc' := 0x401504) (by decide) (fit 464 4) (base := .rdi) (dst := .r9)
    (by decide) (by decide) (by decide) (disp := 0xffffffe8) d464 (by decide)
    (by rw [hrdi]
        exact (addr_sub (v := b + 16) (d := 24) (by decide +kernel) (by omega) (by omega)).trans
          (by omega))) ?_
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 468) (k := 3)
    (pc := 0x401504) (by decide) (fit 468 3) (op := .sub) (by decide) (r := .rcx) (q := .r9)
    (by decide) (by decide) (by decide) d468) ?_
  have hsub : Silmaril.X86.Ext.AluOp.resultN .sub (wd b) (wd pb.2) = wd pb.1 := by
    rw [show Silmaril.X86.Ext.AluOp.resultN .sub (wd b) (wd pb.2) = wd b - wd pb.2 from rfl,
      wd_minus (by omega) (by omega)]; congr 1; omega
  refine SPEC.mem (M' := wordPt (pb.1 + 16) (wd (lastOr m1 0)) ∗ (wordPt (pb.1 + pb.2 - 8) (wd pb.2) ∗
      wordPt pb.1 (wd pb.2) ∗ wordPt (pb.1 + 8) (wd (hdOr m2 0)) ∗
      blockAny (pb.1 + 24) (pb.2 - 32) ∗ blockAny b S ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (m1 ++ pb :: m2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
      dll m1 0 pb.1 ∗ dll m2 pb.1 0))
    (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 471) (k := 4)
    (pc := 0x401504 + BitVec.ofNat 64 3) (pc' := 0x40150b) (by decide) (fit 471 4) (base := .rcx)
    (dst := .rdi) (by decide) (by decide) (by decide) (disp := 0x10) d471 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrcx,
          hrdi]
        rw [hsub]; exact addr_add (by decide +kernel) (by omega))) ?_
  refine SPEC.mem (M' := wordPt (pb.1 + 8) (wd (hdOr m2 0)) ∗ (wordPt (pb.1 + 16) (wd (lastOr m1 0)) ∗
      wordPt (pb.1 + pb.2 - 8) (wd pb.2) ∗ wordPt pb.1 (wd pb.2) ∗
      blockAny (pb.1 + 24) (pb.2 - 32) ∗ blockAny b S ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (m1 ++ pb :: m2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
      dll m1 0 pb.1 ∗ dll m2 pb.1 0))
    (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 475) (k := 4)
    (pc := 0x40150b) (pc' := 0x40150f) (by decide) (fit 475 4) (base := .rcx)
    (dst := .rdx) (by decide) (by decide) (by decide) (disp := 0x8) d475 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrcx,
          hrdi]
        rw [hsub]; exact addr_add (by decide +kernel) (by omega))) ?_
  refine SPEC.mem ?_ (pm_l1 x _ _ m1 m2 pb b S g tl hw hgb hap hb hpb hg1 htl
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrcx]
        rw [hsub])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr8])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
    (by simp only [Function.update_self])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
  unfold blk; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
