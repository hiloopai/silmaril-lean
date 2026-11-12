module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM1

/-!
# Proofs: rung 08 (boundary tags) — `malloc` hands out a whole block

`tail_unlink` (`0x40139c`): the block `y` of the split `l1 ++ y :: l2` fits with less than 32
bytes to spare. Its links are loaded, its predecessor's `next` (or `flist`) and its successor's
`prev` are rewritten, `first[g]` and `last[g + size/16 - 1]` are cleared and `y + 16` returned:
the state is `l1 ++ l2`, the token owns `y`'s size word, its `next` word and the slack.
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

/-! ## Blocks of unknown contents -/

theorem ba3 (a k m j : Nat) :
    (blockAny a k ∗ blockAny (a + k) m ∗ blockAny (a + k + m) j) = blockAny a (k + m + j) := by
  rw [blockAny_add, blockAny_add, sep_assoc, Nat.add_assoc]

/-- A free block's payload (from its `prev` word to its footer) is `blockAny`. -/
theorem blk_tail (y : Nat × Nat) (hy : 32 ≤ y.2) (pv : Nat) :
    (wordPt (y.1 + 16) (wd pv) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗ wordPt (y.1 + y.2 - 8) (wd y.2))
      ⊢ₛ blockAny (y.1 + 16) (y.2 - 16) := by
  refine entails_trans (sep_mono (wordPt_blockAny _ _) (sep_mono_right _ (wordPt_blockAny _ _))) ?_
  rw [show y.1 + 24 = y.1 + 16 + 8 by omega, show y.1 + y.2 - 8 = y.1 + 16 + 8 + (y.2 - 32) by omega,
    ba3, show 8 + (y.2 - 32) + 8 = y.2 - 16 by omega]
  exact entails_refl _

/-- The token of the block of size `s` at `b` with request `n`, and the request's bytes. -/
theorem fresh_of (nw : Word) (b s : Nat) (hb : heap ≤ b) (hbs : b + s ≤ heap + 4096)
    (hb16 : b % 16 = 0) (hs16 : s % 16 = 0) (hs : 32 ≤ s) (hn : nw.toNat + 16 ≤ s) :
    (wordPt b (wd s) ∗ blockAny (b + 8) 8 ∗ blockAny (b + 16) (s - 16)) ⊢ₛ
      iface.Fresh (wd (b + 16)) nw.toNat := by
  have hH := heap_eq
  have hv : (wd (b + 16)).toNat = b + 16 := toNat_wd (by omega)
  show _ ⊢ₛ (⌜wd (b + 16) ≠ 0 ∧ (wd (b + 16)).toNat % 16 = 0⌝ ∗ tok (wd (b + 16)) nw.toNat ∗
    blockAny (wd (b + 16)).toNat nw.toNat)
  rw [hv]
  refine spure_sep_intro ⟨wd_ne_zero (by omega) (by omega), by omega⟩ ?_
  unfold tok
  rw [hv, sexists_sep]
  refine sexists_intro s (entails_trans ?_ (entails_of_eq (by rw [sep_assoc])))
  refine spure_sep_intro ⟨by omega, by omega, by omega, hs16, hs, hn⟩ ?_
  have hsplit : blockAny (b + 16) (s - 16) =
      (blockAny (b + 16) nw.toNat ∗ blockAny (b + 16 + nw.toNat) (s - 16 - nw.toNat)) := by
    rw [← blockAny_add]; congr 1; omega
  rw [show b + 16 - 16 = b by omega, show b + 16 - 8 = b + 8 by omega, hsplit]
  exact entails_of_eq (by ac_rfl)

theorem post_whole (nw : Word) (y : Nat × Nat) (hy : Good y) (hn : nw.toNat + 16 ≤ y.2)
    (nx pv : Nat) {fs : List (Nat × Nat)} (hw : WF fs) :
    (blk y nx pv ∗ mmOf fs) ⊢ₛ (mallocSpec iface).post nw (wd (y.1 + 16)) := by
  show _ ⊢ₛ (mm ∗ sor ⌜wd (y.1 + 16) = 0⌝ (iface.Fresh (wd (y.1 + 16)) nw.toNat))
  rw [sep_comm]
  refine sep_mono (mm_of hw) (entails_trans ?_ (sor_intro_right _ _))
  unfold Good at hy
  unfold blk
  refine entails_trans (sep_mono_right _ (sep_mono (wordPt_blockAny _ _)
    (blk_tail y hy.2.2.2.2 pv))) ?_
  exact fresh_of nw y.1 y.2 hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2 hn

theorem addr_add {v D : Nat} {d : BitVec 32} (hd : d.signExtend 64 = wd D) (h : v + D < 2 ^ 64) :
    (wd v + d.signExtend 64).toNat = v + D := by rw [hd, wd_add, toNat_wd h]

theorem addr_tbl {v D : Nat} {d : BitVec 32} (hd : d.signExtend 64 = wd D) (h : v + D < 2 ^ 64) :
    (wd v + d.signExtend 64).toNat = D + v := by rw [hd, wd_add, toNat_wd h, Nat.add_comm]

/-- Clearing table byte `j` of the block `x` removed from the list. -/
theorem first_clear {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} {g : Nat}
    (hw : WF (l1 ++ x :: l2)) (hg : x.1 = heap + 16 * g) :
    ∀ i < 256, Function.update (firstT (l1 ++ x :: l2)) g 0 i = firstT (l1 ++ l2) i := by
  intro i _
  by_cases e : i = g
  · subst e; rw [Function.update_self, firstT_mid_self hw hg]
  · rw [Function.update_of_ne e]; exact (firstT_mid_ne (l1 := l1) (l2 := l2) (x := x) (by omega)).symm

theorem last_clear {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} {j : Nat}
    (hw : WF (l1 ++ x :: l2)) (hj : x.1 + x.2 = heap + 16 * (j + 1)) :
    ∀ i < 256, Function.update (lastT (l1 ++ x :: l2)) j 0 i = lastT (l1 ++ l2) i := by
  intro i _
  by_cases e : i = j
  · subst e; rw [Function.update_self, lastT_mid_self hw hj]
  · rw [Function.update_of_ne e]; exact (lastT_mid_ne (l1 := l1) (l2 := l2) (x := x) (by omega)).symm

variable {nw sp ret : Word}

/-- `0x4013b6`: clear `first[g]` and `last[g + size/16 - 1]`, return `y + 16`. -/
theorem u_fin (f : Reg → Word) (fl : Flags) (l1 l2 : List (Nat × Nat)) (y : Nat × Nat)
    (hw : WF (l1 ++ y :: l2)) (hn : nw.toNat + 16 ≤ y.2) (nx pv : Nat)
    (hrax : f .rax = wd y.1) (hrsi : f .rsi = wd ((y.1 - heap) / 16))
    (hr8 : f .r8 = wd ((y.1 - heap) / 16 + y.2 / 16 - 1)) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013b6 f fl
      (blk y nx pv ∗ wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 (hdOr l2 0) ∗ dll l2 (lastOr l1 0) 0))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  obtain ⟨hgy, hw', -⟩ := wf_mid hw
  have hH := heap_eq
  have hF : firstA = 0x4031c0 := rfl
  have hL : lastA = 0x4030c0 := rfl
  have hy := hgy; unfold Good at hy
  have hg1 : y.1 = heap + 16 * ((y.1 - heap) / 16) := by omega
  have hj1 : y.1 + y.2 = heap + 16 * ((y.1 - heap) / 16 + y.2 / 16 - 1 + 1) := by omega
  have hg256 : (y.1 - heap) / 16 < 256 := by omega
  have hj256 : (y.1 - heap) / 16 + y.2 / 16 - 1 < 256 := by omega
  refine SPEC.mem (M' := bytePt (firstA + (y.1 - heap) / 16)
    (firstT (l1 ++ y :: l2) ((y.1 - heap) / 16)) ∗
    (tblR firstA (firstT (l1 ++ y :: l2)) ((y.1 - heap) / 16) ∗ blk y nx pv ∗
      wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
      dll l1 0 (hdOr l2 0) ∗ dll l2 (lastOr l1 0) 0))
    (by rw [tbl_split firstA _ hg256]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 134) (k := 7)
    (pc := 0x4013b6) (by decide) (fit 134 7) (bytePt_blockAny _ _) d134
    (addr_reg (r := .rsi) (by decide) hrsi (addr_tbl (by decide +kernel) (by omega)))) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := code) (o := 141) (k := 4)
    (pc := 0x4013b6 + BitVec.ofNat 64 7) (by decide) (fit 141 4) (op := .add) (by decide)
    (r := .rax) (by decide) (imm := 0x10) d141) ?_
  refine SPEC.mem (M' := bytePt (lastA + ((y.1 - heap) / 16 + y.2 / 16 - 1))
    (lastT (l1 ++ y :: l2) ((y.1 - heap) / 16 + y.2 / 16 - 1)) ∗
    (tblR lastA (lastT (l1 ++ y :: l2)) ((y.1 - heap) / 16 + y.2 / 16 - 1) ∗
      bytePt (firstA + (y.1 - heap) / 16) 0 ∗
      tblR firstA (firstT (l1 ++ y :: l2)) ((y.1 - heap) / 16) ∗ blk y nx pv ∗
      wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr l1 (hdOr l2 0))) ∗
      blockAny (flistA + 8) 24 ∗ dll l1 0 (hdOr l2 0) ∗ dll l2 (lastOr l1 0) 0))
    (by rw [tbl_split lastA _ hj256]; ac_rfl) ?_
  refine SPEC.trans (c_movI8M E (b := 0x401330) (code := code) (o := 145) (k := 8)
    (pc := 0x4013b6 + BitVec.ofNat 64 7 + BitVec.ofNat 64 4) (by decide) (fit 145 8)
    (bytePt_blockAny _ _) d145
    (addr_reg (r := .r8) (by decide) (by simp only [Function.update_apply, reduceCtorEq,
      ↓reduceIte, hr8]) (addr_tbl (by decide +kernel) (by omega)))) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (blk y nx pv ∗ mmOf (l1 ++ l2))) ?_ ?_
  · rw [mmOf, ← tblPt_congr lastA (last_clear hw hj1), ← tblPt_congr firstA (first_clear hw hg1),
      ← tbl_write lastA _ hj256, ← tbl_write firstA _ hg256, dll_append, hdOr_append]
    ac_rfl
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 153) (k := 1)
    (pc := 0x4013b6 + BitVec.ofNat 64 7 + BitVec.ofNat 64 4 + BitVec.ofNat 64 8) (by decide)
    (fit 153 1) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r153) ?_
  refine St_post rfl (by simp only [Function.update_self]) ?_
  have hv : (Function.update (Function.update f .rax (Silmaril.X86.Ext.AluOp.resultN .add (f .rax)
      (BitVec.signExtend 64 (0x10 : BitVec 8)))) .rsp (sp + 8#64)) .rax = wd (y.1 + 16) := by
    simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrax]
    rw [show BitVec.signExtend 64 (0x10 : BitVec 8) = wd 16 by decide +kernel]
    exact wd_add _ _
  rw [hv]
  exact post_whole nw y hgy hn nx pv hw'

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
