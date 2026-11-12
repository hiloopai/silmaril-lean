module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF2

/-!
# Proofs: rung 08 (boundary tags) — `free` merges with the previous free block

`pm_fin` (`0x401528`): the previous free block `pb` (ending where the freed block starts) is
unlinked; `last[g - 1]` is cleared, the size grows by `pb`'s size and the merged block starts at
`pb` (granule `pg`, `r8 = pg - 1`); then the push (`ftail`). `pm_l2` (`0x40151f`): `pb`'s
successor gets `pb`'s predecessor as `prev`.
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

/-- `wd v - 1` (as `v + (2^64 - 1)`) plus `k ≥ 1`, plus a displacement. -/
theorem addr_m1 {v k D : Nat} (hk : 1 ≤ v + k) (h : v + k + D < 2 ^ 64) :
    (wd v + wd (2 ^ 64 - 1) + wd k + wd D).toNat = v + k - 1 + D := by
  rw [wd_add, wd_add, wd_add, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at h ⊢
  omega

/-- The table `last` after merging with the previous block. -/
theorem last_prev {m1 m2 : List (Nat × Nat)} {pb : Nat × Nat} {g E : Nat} {tl : Nat → Byte}
    (hw : WF (m1 ++ pb :: m2)) (hg1 : 1 ≤ g) (hpb : pb.1 + pb.2 = heap + 16 * g)
    (htl : ∀ j < 256, j ≠ E → tl j = lastT (m1 ++ pb :: m2) j) :
    ∀ j < 256, j ≠ E → Function.update tl (g - 1) 0 j = lastT (m1 ++ m2) j := by
  intro j hj hjE
  by_cases e : j = g - 1
  · subst e; rw [Function.update_self, lastT_mid_self hw (by omega)]
  · rw [Function.update_of_ne e, htl j hj hjE]
    exact (lastT_mid_ne (l1 := m1) (l2 := m2) (x := pb) (by omega)).symm

variable {sp ret : Word}

/-- **`0x401528`: the merged block starts at `pb`.** -/
theorem pm_fin (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (m1 m2 : List (Nat × Nat))
    (pb : Nat × Nat) (b S g X nx pv : Nat) (tl : Nat → Byte) (hw : WF (m1 ++ pb :: m2))
    (hgb : Good (b, S)) (hap : ∀ y ∈ m1 ++ pb :: m2, Apart (b, S) y) (hb : b = heap + 16 * g)
    (hpb : pb.1 + pb.2 = b) (hg1 : 1 ≤ g)
    (htl : ∀ j < 256, j ≠ g + S / 16 - 1 → tl j = lastT (m1 ++ pb :: m2) j)
    (hrcx : f .rcx = wd pb.1) (hr9 : f .r9 = wd pb.2) (hrax : f .rax = wd S)
    (hr8 : f .r8 = wd g + wd (2 ^ 64 - 1)) (hrsi : f .rsi = wd (hdOr (m1 ++ m2) 0))
    (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401528 f fl
      (blockAny b S ∗ blk pb nx pv ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd X) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
        dll m1 0 (hdOr m2 0) ∗ dll m2 (lastOr m1 0) 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hL : lastA = 0x4030c0 := rfl
  obtain ⟨hgp, hw', hap'⟩ := wf_mid hw
  have hp := hgp; unfold Good at hp
  have hg := hgb; unfold Good at hg; simp only at hg
  have hpg : pb.1 = heap + 16 * ((pb.1 - heap) / 16) := by omega
  have hgl : g - 1 < 256 := by omega
  refine SPEC.memPre (M' := blockAny pb.1 (pb.2 + S) ∗ (wordPt sp.toNat ret ∗
      wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗
      tblPt firstA (firstT (m1 ++ pb :: m2)) ∗ dll m1 0 (hdOr m2 0) ∗ dll m2 (lastOr m1 0) 0))
    ?_ ?_
  · refine entails_trans (entails_of_eq (show _ = ((blk pb nx pv ∗ blockAny b S) ∗
      (wordPt sp.toNat ret ∗ wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗
        tblPt firstA (firstT (m1 ++ pb :: m2)) ∗ dll m1 0 (hdOr m2 0) ∗
        dll m2 (lastOr m1 0) 0)) by ac_rfl)) (sep_mono_left _ ?_)
    rw [blockAny_add, hpb]
    exact sep_mono_left _ (blk_blockAny pb hp.2.2.2.2 nx pv)
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 504) (k := 3)
    (pc := 0x401528) (by decide) (fit 504 3) (r := .rdx) (q := .rcx) (by decide) (by decide)
    (by decide) d504) ?_
  refine SPEC.mem (M' := bytePt (lastA + (g - 1)) (tl (g - 1)) ∗ (tblR lastA tl (g - 1) ∗
      blockAny pb.1 (pb.2 + S) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd X) ∗ blockAny (flistA + 8) 24 ∗
      tblPt firstA (firstT (m1 ++ pb :: m2)) ∗ dll m1 0 (hdOr m2 0) ∗ dll m2 (lastOr m1 0) 0))
    (by rw [tbl_split lastA tl hgl]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 507) (k := 8)
    (pc := 0x401528 + BitVec.ofNat 64 3) (by decide) (fit 507 8) (bytePt_blockAny _ _) d507
    (addr_reg (r := .r8) (by decide) (v := wd g + wd (2 ^ 64 - 1))
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hr8])
      (by rw [show BitVec.signExtend 64 (0x4030c0 : BitVec 32) = wd 0x4030c0 by decide +kernel,
            wd_add, wd_add, BitVec.toNat_ofNat]
          simp only [Nat.reducePow]; omega))) ?_
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 515) (k := 3)
    (pc := 0x401528 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8) (by decide) (fit 515 3)
    (op := .add) (by decide) (r := .rax) (q := .r9) (by decide) (by decide) (by decide) d515) ?_
  refine SPEC.trans (c_aluI E (b := 0x401330) (code := code) (o := 518) (k := 7)
    (pc := 0x401528 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 3) (by decide)
    (fit 518 7) (op := .sub) (by decide) (r := .rdx) (by decide) (imm := 0x4032c0) d518) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 525) (k := 4)
    (pc := 0x401528 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 7) (by decide) (fit 525 4) (r := .rdx) (by decide) (c := 0x4) (by decide)
    d525) ?_
  have hsub : Silmaril.X86.Ext.AluOp.resultN .sub (wd pb.1)
      (BitVec.signExtend 64 (0x4032c0 : BitVec 32)) = wd (pb.1 - heap) := by
    rw [show BitVec.signExtend 64 (0x4032c0 : BitVec 32) = wd 0x4032c0 by decide +kernel]
    exact wd_minus (by omega) (by omega)
  have hpgv : ShiftOp.shr.result (wd (pb.1 - heap)) ((0x4 : BitVec 8).toNat % 64) =
      wd ((pb.1 - heap) / 16) := shr4_wd (by omega)
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 529) (k := 4)
    (pc := 0x401528 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 7 + BitVec.ofNat 64 4) (by decide) (fit 529 4) (dst := .r8) (by decide) d529
    (a := wd ((pb.1 - heap) / 16) + wd (2 ^ 64 - 1)) (fun st hregs next => by
      rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdx (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrcx]
      rw [hsub, hpgv, show BitVec.signExtend 64 (0xffffffff : BitVec 32) = wd (2 ^ 64 - 1) by
        decide +kernel])) ?_
  refine SPEC.trans (c_jmp32 E (b := 0x401330) (code := code) (o := 533) (k := 5)
    (pc := 0x401528 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 7 + BitVec.ofNat 64 4 + BitVec.ofNat 64 4) (pc' := 0x4014a7) (by decide)
    (fit 533 5) d533 (by decide)) ?_
  refine SPEC.mem ?_ (ftail x _ _ (m1 ++ m2) pb.1 (pb.2 + S) ((pb.1 - heap) / 16) X
    (Function.update tl (g - 1) 0) (firstT (m1 ++ pb :: m2)) hw'
    (by unfold Good; simp only; omega)
    (fun y hy => by
      have h1 := hap' y hy; have h2 := hap y (mem_mid hy); have h3 := hw'.1 y hy
      unfold Apart at h1 h2 ⊢; unfold Good at h3; simp only at h1 h2 ⊢; omega) hpg
    (fun j _ hj => (firstT_mid_ne (l1 := m1) (l2 := m2) (x := pb) (by omega)).symm)
    (last_prev hw hg1 (by omega) (fun j hj hjE => htl j hj (by omega)))
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax,
          hr9]
        show wd S + wd pb.2 = _
        rw [wd_add, Nat.add_comm])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrcx]
        rw [hsub, hpgv])
    (by simp only [Function.update_self])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
  rw [dll_append, ← tbl_write lastA tl hgl]; ac_rfl

/-- **`0x40151f`: `pb`'s successor.** -/
theorem pm_l2 (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (m1 m2 : List (Nat × Nat))
    (pb : Nat × Nat) (b S g X : Nat) (tl : Nat → Byte) (hw : WF (m1 ++ pb :: m2))
    (hgb : Good (b, S)) (hap : ∀ y ∈ m1 ++ pb :: m2, Apart (b, S) y) (hb : b = heap + 16 * g)
    (hpb : pb.1 + pb.2 = b) (hg1 : 1 ≤ g)
    (htl : ∀ j < 256, j ≠ g + S / 16 - 1 → tl j = lastT (m1 ++ pb :: m2) j)
    (hrcx : f .rcx = wd pb.1) (hr9 : f .r9 = wd pb.2) (hrax : f .rax = wd S)
    (hr8 : f .r8 = wd g + wd (2 ^ 64 - 1)) (hrsi : f .rsi = wd (hdOr (m1 ++ m2) 0))
    (hrdi : f .rdi = wd (lastOr m1 0)) (hrdx : f .rdx = wd (hdOr m2 0)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40151f f fl
      (blockAny b S ∗ blk pb (hdOr m2 0) (lastOr m1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd X) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: m2)) ∗
        dll m1 0 (hdOr m2 0) ∗ dll m2 pb.1 0))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hg := hw.1
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 495) (k := 3) (pc := 0x40151f)
    (by decide) (fit 495 3) (r := .rdx) (by decide) d495) ?_
  cases m2 with
  | nil =>
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 498) (k := 2)
      (pc := 0x40151f + BitVec.ofNat 64 3) (pc' := 0x401528) (by decide) (fit 498 2) (c := .e)
      (rel := 0x4) (by rw [hrdx, eval_e_wd (by decide)]; rfl) d498 (by decide)) ?_
    exact pm_fin x f _ m1 [] pb b S g X _ _ tl hw hgb hap hb hpb hg1 htl hrcx hr9 hrax hr8 hrsi hrsp
  | cons z m2' =>
    have hz := good_lt hg ⟨z, by simp, rfl⟩
    have hz0 : hdOr (z :: m2') 0 ≠ 0 := by simp only [hdOr]; omega
    have hz64 : hdOr (z :: m2') 0 < 2 ^ 64 := by simp only [hdOr]; omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 498) (k := 2)
      (pc := 0x40151f + BitVec.ofNat 64 3) (pc' := 0x401524) (by decide) (fit 498 2) (c := .e)
      (rel := 0x4) (by rw [hrdx, eval_e_wd hz64]; simp [hz0]) d498 (by decide)) ?_
    refine SPEC.mem (M' := wordPt (z.1 + 16) (wd pb.1) ∗ (wordPt z.1 (wd z.2) ∗
      wordPt (z.1 + 8) (wd (hdOr m2' 0)) ∗ blockAny (z.1 + 24) (z.2 - 32) ∗
      wordPt (z.1 + z.2 - 8) (wd z.2) ∗ dll m2' z.1 0 ∗
      blockAny b S ∗ blk pb (hdOr (z :: m2') 0) (lastOr m1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd X) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA tl ∗ tblPt firstA (firstT (m1 ++ pb :: z :: m2')) ∗
        dll m1 0 (hdOr (z :: m2') 0)))
      (by rw [dll_cons]; unfold blk; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 500) (k := 4)
      (pc := 0x401524) (pc' := 0x401528) (by decide) (fit 500 4) (base := .rdx) (src := .rdi)
      (by decide) (by decide) (by decide) (disp := 0x10) (wordPt_blockAny _ _) d500 (by decide)
      (by rw [hrdx]; simp only [hdOr]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.mem ?_ (pm_fin x f _ m1 (z :: m2') pb b S g X (hdOr (z :: m2') 0) (lastOr m1 0)
      tl hw hgb hap hb hpb hg1 htl hrcx hr9 hrax hr8 hrsi hrsp)
    rw [hrdi, dll_cons (l := m2')]; unfold blk; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
