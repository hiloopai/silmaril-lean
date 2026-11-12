module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM4

/-!
# Proofs: rung 08 (boundary tags) — `malloc` splits a block

`tail_split` (`0x4013d8`): the block `y` has at least `a + 32` bytes. It shrinks in place to
`ns = size - a` (size word and a new footer), `last` moves from its old last granule to the
new one, and the tail `[y + ns, y + size)` gets the header `a` and goes to the token. The free
list keeps its order and links: `l1 ++ (y, ns) :: l2`.
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

/-- `shr $4`. -/
theorem shr4_wd {x : Nat} (hx : x < 2 ^ 64) :
    ShiftOp.shr.result (wd x) ((0x4 : BitVec 8).toNat % 64) = wd (x / 16) := by
  show wd x >>> ((0x4 : BitVec 8).toNat % 64) = _
  rw [show (0x4 : BitVec 8).toNat % 64 = 4 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_wd hx, toNat_wd (by omega), Nat.shiftRight_eq_div_pow]

/-- `wd x - d` for a negative displacement. -/
theorem addr_sub {v d : Nat} {D : BitVec 32} (hD : D.signExtend 64 = wd (2 ^ 64 - d))
    (hd : d ≤ v) (hv : v < 2 ^ 64) : (wd v + D.signExtend 64).toNat = v - d := by
  rw [hD, wd_sub hd (by omega), toNat_wd (by omega)]

/-- The table `last` after a split: the block now ends with granule `j1`, not `j2`. -/
theorem last_split {l1 l2 : List (Nat × Nat)} {y : Nat × Nat} {ns j1 j2 : Nat}
    (hw : WF (l1 ++ y :: l2)) (hlt : ns < y.2)
    (h1 : y.1 + ns = heap + 16 * (j1 + 1)) (h2 : y.1 + y.2 = heap + 16 * (j2 + 1)) :
    ∀ i < 256, Function.update (Function.update (lastT (l1 ++ y :: l2)) j1 1) j2 0 i =
      lastT (l1 ++ (y.1, ns) :: l2) i := by
  intro i _
  by_cases e2 : i = j2
  · subst e2
    rw [Function.update_self, lastT_mid_ne (x := (y.1, ns)) (by simp only; omega) |>.symm,
      lastT_mid_self hw h2]
  · rw [Function.update_of_ne e2]
    by_cases e1 : i = j1
    · subst e1
      rw [Function.update_self, lastT_mid_one _ _ _ (by simp only; omega)]
    · rw [Function.update_of_ne e1]
      exact (lastT_replace l1 l2 (x := y) (x' := (y.1, ns)) (by omega)
        (show y.1 + ns ≠ heap + 16 * (i + 1) by omega)).symm

/-- The token of a split-off tail `[r, r + a)`; its last word is the old footer. -/
theorem post_split (nw : Word) (y : Nat × Nat) (a : Nat) (hy : Good y) (ha16 : a % 16 = 0)
    (ha : 32 ≤ a) (hn : nw.toNat + 16 ≤ a) (hfit : a + 32 ≤ y.2)
    {fs : List (Nat × Nat)} (hw : WF fs) :
    (mmOf fs ∗ (wordPt (y.1 + (y.2 - a)) (wd a) ∗
      blockAny (y.1 + (y.2 - a) + 8) (a - 16) ∗ wordPt (y.1 + y.2 - 8) (wd y.2))) ⊢ₛ
      (mallocSpec iface).post nw (wd (y.1 + (y.2 - a) + 16)) := by
  show _ ⊢ₛ (mm ∗ sor ⌜wd (y.1 + (y.2 - a) + 16) = 0⌝
    (iface.Fresh (wd (y.1 + (y.2 - a) + 16)) nw.toNat))
  have hy' := hy; unfold Good at hy'
  refine sep_mono (mm_of hw) (entails_trans ?_ (sor_intro_right _ _))
  refine entails_trans (sep_mono_right _ (sep_mono_right _ (wordPt_blockAny _ _))) ?_
  rw [show y.1 + y.2 - 8 = y.1 + (y.2 - a) + 8 + (a - 16) by omega, ← blockAny_add,
    show a - 16 + 8 = 8 + (a - 16) by omega, blockAny_add,
    show y.1 + (y.2 - a) + 8 + 8 = y.1 + (y.2 - a) + 16 by omega]
  exact fresh_of nw (y.1 + (y.2 - a)) a (by omega) (by omega) (by omega) ha16 ha hn

variable {nw sp ret : Word}

theorem interior_split (y : Nat × Nat) (a : Nat) (ha : 32 ≤ a) (hfit : a + 32 ≤ y.2) :
    blockAny (y.1 + 24) (y.2 - 32) = (blockAny (y.1 + 24) (y.2 - a - 32) ∗
      blockAny (y.1 + (y.2 - a) - 8) 8 ∗ blockAny (y.1 + (y.2 - a)) 8 ∗
      blockAny (y.1 + (y.2 - a) + 8) (a - 16)) := by
  rw [show y.1 + (y.2 - a) - 8 = y.1 + 24 + (y.2 - a - 32) by omega,
    show y.1 + (y.2 - a) = y.1 + 24 + (y.2 - a - 32) + 8 by omega,
    show y.1 + 24 + (y.2 - a - 32) + 8 + 8 = y.1 + 24 + (y.2 - a - 32) + 8 + 8 from rfl,
    ← blockAny_add (y.1 + 24 + (y.2 - a - 32) + 8) 8 (a - 16),
    ← blockAny_add (y.1 + 24 + (y.2 - a - 32)) 8 (8 + (a - 16)),
    ← blockAny_add (y.1 + 24) (y.2 - a - 32) (8 + (8 + (a - 16)))]
  congr 1; omega

/-- **`0x4013d8`: split `y`, hand out its tail.** -/
theorem tail_split (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat)) (y : Nat × Nat)
    (a : Nat) (hw : WF (l1 ++ y :: l2)) (ha16 : a % 16 = 0) (ha : 32 ≤ a)
    (hn : nw.toNat + 16 ≤ a) (hfit : a + 32 ≤ y.2)
    (hrax : f .rax = wd y.1) (hrdi : f .rdi = wd (y.2 - a)) (hrdx : f .rdx = wd a)
    (hrsi : f .rsi = wd ((y.1 - heap) / 16))
    (hr8 : f .r8 = wd ((y.1 - heap) / 16 + y.2 / 16 - 1)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013d8 f fl
      (blk y (hdOr l2 0) (lastOr l1 0) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  have hL : lastA = 0x4030c0 := rfl
  have hgy := (wf_mid hw).1
  have hy := hgy; unfold Good at hy
  have hg1 : y.1 = heap + 16 * ((y.1 - heap) / 16) := by omega
  have hj1 : y.1 + (y.2 - a) = heap + 16 * ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1 + 1) := by omega
  have hj2 : y.1 + y.2 = heap + 16 * ((y.1 - heap) / 16 + y.2 / 16 - 1 + 1) := by omega
  have hj1l : (y.1 - heap) / 16 + (y.2 - a) / 16 - 1 < 256 := by omega
  have hj2l : (y.1 - heap) / 16 + y.2 / 16 - 1 < 256 := by omega
  -- mov %rdi,%rcx; mov %rdi,(%rax): the shrunk size
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 168) (k := 3) (pc := 0x4013d8)
    (by decide) (fit 168 3) (r := .rcx) (q := .rdi) (by decide) (by decide) (by decide) d168) ?_
  refine SPEC.mem (M' := wordPt y.1 (wd y.2) ∗ (wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗
      wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
      tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 171) (k := 3)
    (pc := 0x4013d8 + BitVec.ofNat 64 3) (pc' := 0x4013de) (by decide) (fit 171 3) (base := .rax)
    (src := .rdi) (by decide) (by decide) (by decide) (disp := 0x0) (wordPt_blockAny _ _) d171
    (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]
                    exact addr_add (v := y.1) (D := 0) (by decide +kernel) (by omega))) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 174) (k := 4) (pc := 0x4013de)
    (by decide) (fit 174 4) (r := .rcx) (by decide) (c := 0x4) (by decide) d174) ?_
  -- mov %rdi,-0x8(%rax,%rdi,1): the new footer
  refine SPEC.mem (M' := blockAny (y.1 + (y.2 - a) - 8) 8 ∗ (wordPt y.1 (wd (y.2 - a)) ∗
      wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗
      blockAny (y.1 + 24) (y.2 - a - 32) ∗ blockAny (y.1 + (y.2 - a)) 8 ∗
      blockAny (y.1 + (y.2 - a) + 8) (a - 16) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
      tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by rw [interior_split y a ha hfit]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi]; ac_rfl) ?_
  refine SPEC.trans (c_storeM E (b := 0x401330) (code := code) (o := 178) (k := 5)
    (pc := 0x4013de + BitVec.ofNat 64 4) (by decide) (fit 178 5) (src := .rdi) (by decide)
    (entails_refl _) d178
    (addr_idx (r := .rax) (q := .rdi) (by decide) (by decide) (by decide) (v := wd y.1)
      (u := wd (y.2 - a)) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
      (by rw [wd_add]; exact addr_sub (by decide +kernel) (by omega) (by omega)))) ?_
  -- add %rdi,%rax; movb $1,last[g + ns/16 - 1]
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 183) (k := 3)
    (pc := 0x4013de + BitVec.ofNat 64 4 + BitVec.ofNat 64 5) (by decide) (fit 183 3) (op := .add)
    (by decide) (r := .rax) (q := .rdi) (by decide) (by decide) (by decide) d183) ?_
  refine SPEC.mem (M' := bytePt (lastA + ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1))
      (lastT (l1 ++ y :: l2) ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1)) ∗
      (tblR lastA (lastT (l1 ++ y :: l2)) ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1) ∗
      wordPt (y.1 + (y.2 - a) - 8) (wd (y.2 - a)) ∗ wordPt y.1 (wd (y.2 - a)) ∗
      wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗
      blockAny (y.1 + 24) (y.2 - a - 32) ∗ blockAny (y.1 + (y.2 - a)) 8 ∗
      blockAny (y.1 + (y.2 - a) + 8) (a - 16) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt firstA (firstT (l1 ++ y :: l2)) ∗
      dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by rw [tbl_split lastA _ hj1l]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 186) (k := 8)
    (pc := 0x4013de + BitVec.ofNat 64 4 + BitVec.ofNat 64 5 + BitVec.ofNat 64 3) (by decide)
    (fit 186 8) (bytePt_blockAny _ _) d186
    (addr_idx (r := .rsi) (q := .rcx) (by decide) (by decide) (by decide)
      (v := wd ((y.1 - heap) / 16)) (u := wd ((y.2 - a) / 16)) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrdi]
          exact shr4_wd (by omega))
      (by rw [wd_add, show BitVec.signExtend 64 (0x4030bf : BitVec 32) = wd 0x4030bf by
            decide +kernel, wd_add, toNat_wd (by omega)]; omega))) ?_
  have hv1 : Silmaril.X86.Ext.AluOp.resultN .add (wd y.1) (wd (y.2 - a)) = wd (y.1 + (y.2 - a)) :=
    wd_add _ _
  have hv2 : Silmaril.X86.Ext.AluOp.resultN .add (wd (y.1 + (y.2 - a)))
      (BitVec.signExtend 64 (0x10 : BitVec 8)) = wd (y.1 + (y.2 - a) + 16) := by
    rw [show BitVec.signExtend 64 (0x10 : BitVec 8) = wd 16 by decide +kernel]; exact wd_add _ _
  refine SPEC.mem (M' := blockAny (y.1 + (y.2 - a)) 8 ∗ (wordPt sp.toNat ret ∗
      tblPt lastA (Function.update (lastT (l1 ++ y :: l2))
        ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1) 1) ∗
      wordPt (y.1 + (y.2 - a) - 8) (wd (y.2 - a)) ∗ wordPt y.1 (wd (y.2 - a)) ∗
      wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗
      blockAny (y.1 + 24) (y.2 - a - 32) ∗ blockAny (y.1 + (y.2 - a) + 8) (a - 16) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt firstA (firstT (l1 ++ y :: l2)) ∗
      dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by rw [← tbl_write lastA _ hj1l]; ac_rfl) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := code) (o := 194) (k := 4)
    (pc := 0x4013de + BitVec.ofNat 64 4 + BitVec.ofNat 64 5 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 8) (by decide) (fit 194 4) (op := .add) (by decide) (r := .rax) (by decide)
    (imm := 0x10) d194) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 198) (k := 4)
    (pc := 0x4013de + BitVec.ofNat 64 4 + BitVec.ofNat 64 5 + BitVec.ofNat 64 3 +
      BitVec.ofNat 64 8 + BitVec.ofNat 64 4) (pc' := 0x4013fa) (by decide) (fit 198 4)
    (base := .rax) (src := .rdx) (by decide) (by decide) (by decide) (disp := 0xfffffff0)
    (entails_refl _) d198 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax,
          hrdi]
        rw [hv1, hv2]
        exact (addr_sub (v := y.1 + (y.2 - a) + 16) (d := 16) (by decide +kernel) (by omega)
          (by omega)).trans (by omega))) ?_
  refine SPEC.mem (M' := bytePt (lastA + ((y.1 - heap) / 16 + y.2 / 16 - 1))
      (Function.update (lastT (l1 ++ y :: l2)) ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1) 1
        ((y.1 - heap) / 16 + y.2 / 16 - 1)) ∗
      (tblR lastA (Function.update (lastT (l1 ++ y :: l2))
        ((y.1 - heap) / 16 + (y.2 - a) / 16 - 1) 1) ((y.1 - heap) / 16 + y.2 / 16 - 1) ∗
      wordPt (y.1 + (y.2 - a)) (wd a) ∗ wordPt sp.toNat ret ∗
      wordPt (y.1 + (y.2 - a) - 8) (wd (y.2 - a)) ∗ wordPt y.1 (wd (y.2 - a)) ∗
      wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗
      blockAny (y.1 + 24) (y.2 - a - 32) ∗ blockAny (y.1 + (y.2 - a) + 8) (a - 16) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt firstA (firstT (l1 ++ y :: l2)) ∗
      dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by rw [tbl_split lastA _ hj2l]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 202) (k := 8)
    (pc := 0x4013fa) (by decide) (fit 202 8) (bytePt_blockAny _ _) d202
    (addr_reg (r := .r8) (by decide) (by simp only [Function.update_apply, reduceCtorEq,
      ↓reduceIte, hr8]) (addr_tbl (by decide +kernel) (by omega)))) ?_
  have hgn : Good (y.1, y.2 - a) := by unfold Good; simp only; omega
  have hw' := wf_replace hw hgn (by simp only; omega)
  have hfe : firstT (l1 ++ (y.1, y.2 - a) :: l2) = firstT (l1 ++ y :: l2) :=
    funext (firstT_replace l1 l2 rfl)
  have hhe : hdOr (l1 ++ (y.1, y.2 - a) :: l2) 0 = hdOr (l1 ++ y :: l2) 0 := by cases l1 <;> rfl
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (mmOf (l1 ++ (y.1, y.2 - a) :: l2) ∗
      (wordPt (y.1 + (y.2 - a)) (wd a) ∗ blockAny (y.1 + (y.2 - a) + 8) (a - 16) ∗
        wordPt (y.1 + y.2 - 8) (wd y.2))))
    (by rw [mmOf, hfe, hhe, dll_mid, ← tblPt_congr lastA (last_split hw (by omega) hj1 hj2),
          ← tbl_write lastA _ hj2l]
        simp only [blk]; ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 210) (k := 1)
    (pc := 0x4013fa + BitVec.ofNat 64 8) (by decide) (fit 210 1)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r210) ?_
  refine St_post rfl (by simp only [Function.update_self]) ?_
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax, hrdi]
  rw [hv1, hv2]
  exact post_split nw y a hgy ha16 ha hn hfit hw'

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
