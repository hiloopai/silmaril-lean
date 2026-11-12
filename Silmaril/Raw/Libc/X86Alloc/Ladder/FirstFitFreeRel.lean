module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree

/-! # Proofs: rung 05 (first-fit) `free` against the relational model `ffRel` (exact free list) -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.FirstFit
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps

theorem unpackR (s : List Block) (p : Word) (n : Nat) :
    (ifaceR.mmS s ∗ ifaceR.tok p n ∗ blockAny p.toNat n) ⊢ₛ
      sexists fun (h : Word) => sexists fun (sz : Nat) =>
        ⌜n ≤ sz ∧ Block.WF ⟨p - 16#64, sz⟩ ∧ p = (p - 16#64) + 16#64⌝ ∗
        (wordPt flAddr.toNat h ∗ hdrSeg s h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
          blockAny ((p - 16#64) + 8#64).toNat 8 ∗ blockAny (p.toNat + n) (sz - n) ∗
          blockAny p.toNat n) := by
  show ((sexists fun (h : Word) => wordPt flAddr.toNat h ∗ hdrSeg s h ∗ strue) ∗
    (sexists fun (sz : Nat) => ⌜n ≤ sz ∧ (Block.WF ⟨p - 16#64, sz⟩) ∧ p = (p - 16#64) + 16#64⌝ ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
      blockAny (p.toNat + n) (sz - n)) ∗ blockAny p.toNat n) ⊢ₛ _
  simp only [sexists_sep, sep_sexists]
  refine sexists_elim fun sz => sexists_elim fun h => ?_
  refine sexists_intro h (sexists_intro sz ?_)
  refine entails_trans (entails_of_eq (show _ = (
    ⌜n ≤ sz ∧ (Block.WF ⟨p - 16#64, sz⟩) ∧ p = (p - 16#64) + 16#64⌝ ∗
    (wordPt flAddr.toNat h ∗ hdrSeg s h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
      blockAny ((p - 16#64) + 8#64).toNat 8 ∗ blockAny (p.toNat + n) (sz - n) ∗
      blockAny p.toNat n)) by ac_rfl)) (entails_refl _)

theorem repackR (s : List Block) (h p w : Word) (sz n : Nat)
    (hf : n ≤ sz ∧ Block.WF ⟨p - 16#64, sz⟩ ∧ p = (p - 16#64) + 16#64) (hw : w = p - 16#64) :
    (wordPt flAddr.toNat w ∗ wordPt ((p - 16#64) + 8#64).toNat h ∗ hdrSeg s h ∗ strue ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny (p.toNat + n) (sz - n) ∗
      blockAny p.toNat n) ⊢ₛ
      sexists fun s' => ⌜ffRel.dealloc s p n s'⌝ ∗ ifaceR.mmS s' := by
  subst hw
  obtain ⟨hpn, -⟩ := tok_facts hf
  refine sexists_intro (⟨p - 16#64, sz⟩ :: s) (spure_sep_intro ⟨sz, rfl⟩
    (sexists_intro (p - 16#64) ?_))
  rw [hdrSeg_cons]
  have hpay : (blockAny p.toNat n ∗ blockAny (p.toNat + n) (sz - n)) =
      blockAny ((p - 16#64).toNat + 16) sz := by
    rw [← blockAny_add, ← hpn, Nat.add_sub_cancel' hf.1]
  refine entails_trans (entails_of_eq (show _ = (wordPt flAddr.toNat (p - 16#64) ∗
    ((wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ wordPt ((p - 16#64) + 8#64).toNat h ∗
      (blockAny p.toNat n ∗ blockAny (p.toNat + n) (sz - n)) ∗ hdrSeg s h) ∗ strue)) by ac_rfl)) ?_
  rw [hpay]
  refine sep_mono_right _ (sep_mono_left _ ?_)
  exact spure_sep_intro ⟨rfl, hf.2.1⟩ (sexists_intro h (entails_refl _))

theorem free_sat_rel :
    (freeSpecR ifaceR).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.p) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  rcases x with ⟨s, p, _ | n⟩
  · -- free(NULL)
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (ifaceR.mmS s ∗ ⌜p = 0⌝))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜p = 0⌝ ∗ ifaceR.mmS s)) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hp => ?_
    dsimp only at hdi
    subst hp
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 128) (k := 3)
      (pc := 0x4013b0) rfl (fit 128 3) (r := .rdi) (by decide) d128) ?_
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 131) (k := 2)
      (pc := 0x4013b0 + 3#64) (pc' := 0x4013cb) (by decide) (fit 131 2) (c := .e) (rel := 0x16) ?_
      d131 (by decide)) ?_
    · rw [eval_e_test, hdi]; rfl
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 155)
      (k := 1) (pc := 0x4013cb) (by decide) (fit 155 1) hsp r155) ?_
    exact St_post rfl (by simp only [Function.update_self]) (entails_refl _)
  · -- free(p) of a live block
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (ifaceR.mmS s ∗ ifaceR.tok p n ∗ blockAny p.toNat n))) _
    dsimp only at hdi
    refine SPEC.memPre (sep_mono_right _ (unpackR s p n)) ?_
    rw [St_ex]; refine SPEC.sexists fun h => ?_
    rw [St_ex]; refine SPEC.sexists fun sz => ?_
    rw [St_pure]
    refine SPEC.spure fun hf => ?_
    obtain ⟨hpn, hp0⟩ := tok_facts hf
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 128) (k := 3)
      (pc := 0x4013b0) rfl (fit 128 3) (r := .rdi) (by decide) d128) ?_
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 131) (k := 2)
      (pc := 0x4013b0 + 3#64) (pc' := 0x4013b5) (by decide) (fit 131 2) (c := .e) (rel := 0x16) ?_
      d131 (by decide)) ?_
    · rw [eval_e_test, hdi]; simpa using hp0
    refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ wordPt sp.toNat ret ∗ hdrSeg s h ∗ strue ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
      blockAny (p.toNat + n) (sz - n) ∗ blockAny p.toNat n) (by ac_rfl) ?_
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 133) (k := 7)
      (pc := 0x4013b5) (pc' := 0x4013bc) (by decide) (fit 133 7) (dst := .rax) (by decide)
      (disp := 0x1ce4) d133 (by decide) (by decide)) ?_
    refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := code) (o := 140) (k := 4)
      (pc := 0x4013bc) (by decide) (fit 140 4) (op := .sub) (by decide) (r := .rdi) (imm := 0x10)
      (by decide) d140) ?_
    have hrdi : Silmaril.X86.Ext.AluOp.resultN .sub p (BitVec.signExtend 64 (0x10 : BitVec 8)) =
        p - 16#64 := by
      show p - BitVec.signExtend 64 (0x10 : BitVec 8) = _
      rw [show BitVec.signExtend 64 (0x10 : BitVec 8) = 16#64 by decide +kernel]
    refine SPEC.mem (M' := blockAny ((p - 16#64) + 8#64).toNat 8 ∗ wordPt flAddr.toNat h ∗
      wordPt sp.toNat ret ∗ hdrSeg s h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
      blockAny (p.toNat + n) (sz - n) ∗ blockAny p.toNat n) (by ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 144) (k := 4)
      (pc := 0x4013bc + 4#64) (pc' := 0x4013c4) (by decide) (fit 144 4) (base := .rdi) (src := .rax)
      (by decide) (by decide) (by decide) (disp := 8) (entails_refl _) d144 (by decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi, hrdi]; rfl)) ?_
    refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ wordPt ((p - 16#64) + 8#64).toNat _ ∗
      wordPt sp.toNat ret ∗ hdrSeg s h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
      blockAny (p.toNat + n) (sz - n) ∗ blockAny p.toNat n) (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 148) (k := 7)
      (pc := 0x4013c4) (pc' := 0x4013cb) (by decide) (fit 148 7) (src := .rdi) (by decide)
      (disp := 0x1cd5) (wordPt_blockAny _ _) d148 (by decide) (by decide)) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt flAddr.toNat _ ∗
      wordPt ((p - 16#64) + 8#64).toNat _ ∗ hdrSeg s h ∗ strue ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny (p.toNat + n) (sz - n) ∗
      blockAny p.toNat n)) (by ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 155)
      (k := 1) (pc := 0x4013cb) (by decide) (fit 155 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) r155) ?_
    refine St_post rfl (by simp only [Function.update_self]) ?_
    have hrax : (Function.update (Function.update f .rax h) .rdi
        (Silmaril.X86.Ext.AluOp.resultN .sub (Function.update f .rax h .rdi)
          (BitVec.signExtend 64 (0x10 : BitVec 8)))) .rax = h := by
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
    simp only [Function.update_apply, reduceCtorEq, ↓reduceIte] at *
    refine repackR s h p _ sz n hf ?_
    simp only [hdi, hrdi]

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree
