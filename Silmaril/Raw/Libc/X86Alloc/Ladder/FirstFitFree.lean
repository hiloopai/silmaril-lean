module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.Raw.Libc.X86Alloc.HdrSeg
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 05 (first-fit) `free` meets `freeSpecL` of the first-fit capacity model -/

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

/-! ## The listing of `free`, decoded once -/

theorem d128 : Silmaril.X86.Ext.decode ((code.drop 128).take 3) = some (.test .q (.reg .rdi) .rdi, 3) := by
  decide +kernel
theorem d131 : Silmaril.X86.Ext.decode ((code.drop 131).take 2) = some (.jcc8 .e 0x16, 2) := by
  decide +kernel
theorem d133 : Silmaril.X86.Ext.decode ((code.drop 133).take 7) = some (.load .q .rax (ripMem 0x1ce4), 7) := by
  decide +kernel
theorem d140 : Silmaril.X86.Ext.decode ((code.drop 140).take 4) = some (.aluI8 .q .sub (.reg .rdi) 0x10, 4) := by
  decide +kernel
theorem d144 : Silmaril.X86.Ext.decode ((code.drop 144).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rdi 8)) .rax, 4) := by
  decide +kernel
theorem d148 : Silmaril.X86.Ext.decode ((code.drop 148).take 7) = some (.mov .q (.mem (ripMem 0x1cd5)) .rdi, 7) := by
  decide +kernel
theorem r155 : (code.drop 155).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem hlen : code.length = 160 := by decide +kernel
theorem fit (o k : Nat) (h : o + k ≤ 160 := by decide) : o + k ≤ code.length := hlen ▸ h

/-! ## Unpacking and repacking the allocator state -/

/-- The pure facts a token carries, about its block `b = p - 16`. -/
theorem tok_facts {p : Word} {sz n : Nat} (h : n ≤ sz ∧ Block.WF ⟨p - 16#64, sz⟩ ∧
    p = (p - 16#64) + 16#64) : p.toNat = (p - 16#64).toNat + 16 ∧ p ≠ 0 := by
  obtain ⟨-, ⟨-, -, hb⟩, he⟩ := h
  simp only at hb
  have e : ((p - 16#64) + 16#64).toNat = (p - 16#64).toNat + 16 := by
    rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hpn : p.toNat = (p - 16#64).toNat + 16 := (congrArg BitVec.toNat he).trans e
  refine ⟨hpn, fun h0 => ?_⟩
  rw [h0] at hpn
  simp at hpn

theorem unpack (s : List Block) (p : Word) (n : Nat) :
    (iface.mmS s ∗ iface.tok p n ∗ blockAny p.toNat n) ⊢ₛ
      sexists fun (fl : List Block) => sexists fun (h : Word) => sexists fun (sz : Nat) =>
        ⌜(∀ b ∈ s, b ∈ fl) ∧ (n ≤ sz ∧ Block.WF ⟨p - 16#64, sz⟩ ∧ p = (p - 16#64) + 16#64)⌝ ∗
        (wordPt flAddr.toNat h ∗ hdrSeg fl h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
          blockAny ((p - 16#64) + 8#64).toNat 8 ∗ blockAny (p.toNat + n) (sz - n) ∗
          blockAny p.toNat n) := by
  show ((sexists fun (fl : List Block) => sexists fun (h : Word) =>
      ⌜∀ b ∈ s, b ∈ fl⌝ ∗ wordPt flAddr.toNat h ∗ hdrSeg fl h ∗ strue) ∗
    (sexists fun (sz : Nat) => ⌜n ≤ sz ∧ (Block.WF ⟨p - 16#64, sz⟩) ∧ p = (p - 16#64) + 16#64⌝ ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
      blockAny (p.toNat + n) (sz - n)) ∗ blockAny p.toNat n) ⊢ₛ _
  simp only [sexists_sep, sep_sexists]
  refine sexists_elim fun sz => sexists_elim fun fl => sexists_elim fun h => ?_
  refine sexists_intro fl (sexists_intro h (sexists_intro sz ?_))
  refine entails_trans (entails_of_eq (show _ = (⌜∀ b ∈ s, b ∈ fl⌝ ∗
    ⌜n ≤ sz ∧ (Block.WF ⟨p - 16#64, sz⟩) ∧ p = (p - 16#64) + 16#64⌝ ∗
    (wordPt flAddr.toNat h ∗ hdrSeg fl h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
      blockAny ((p - 16#64) + 8#64).toNat 8 ∗ blockAny (p.toNat + n) (sz - n) ∗
      blockAny p.toNat n)) by ac_rfl)) ?_
  exact spure_sep_elim fun a => spure_sep_elim fun b => spure_sep_intro ⟨a, b⟩ (entails_refl _)

/-- After the push: the freed block heads the list. -/
theorem repack (s fl : List Block) (h p w : Word) (sz n : Nat) (hs : ∀ b ∈ s, b ∈ fl)
    (hf : n ≤ sz ∧ Block.WF ⟨p - 16#64, sz⟩ ∧ p = (p - 16#64) + 16#64) (hw : w = p - 16#64) :
    (wordPt flAddr.toNat w ∗ wordPt ((p - 16#64) + 8#64).toNat h ∗ hdrSeg fl h ∗ strue ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny (p.toNat + n) (sz - n) ∗
      blockAny p.toNat n) ⊢ₛ iface.mmS s := by
  subst hw
  obtain ⟨hpn, -⟩ := tok_facts hf
  refine sexists_intro (⟨p - 16#64, sz⟩ :: fl) (sexists_intro (p - 16#64) ?_)
  refine entails_trans ?_ (spure_sep_intro (fun b hb => List.mem_cons_of_mem _ (hs b hb))
    (entails_refl _))
  rw [hdrSeg_cons]
  have hpay : (blockAny p.toNat n ∗ blockAny (p.toNat + n) (sz - n)) =
      blockAny ((p - 16#64).toNat + 16) sz := by
    rw [← blockAny_add, ← hpn, Nat.add_sub_cancel' hf.1]
  refine entails_trans (entails_of_eq (show _ = (wordPt flAddr.toNat (p - 16#64) ∗
    ((wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ wordPt ((p - 16#64) + 8#64).toNat h ∗
      (blockAny p.toNat n ∗ blockAny (p.toNat + n) (sz - n)) ∗ hdrSeg fl h) ∗ strue)) by ac_rfl)) ?_
  rw [hpay]
  refine sep_mono_right _ (sep_mono_left _ ?_)
  exact spure_sep_intro ⟨rfl, hf.2.1⟩ (sexists_intro h (entails_refl _))

theorem free_sat :
    (freeSpecL iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.p) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  rcases x with ⟨s, p, _ | n⟩
  · -- free(NULL)
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (iface.mmS s ∗ ⌜p = 0⌝))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜p = 0⌝ ∗ iface.mmS s)) (by ac_rfl) ?_
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
      (iface.mmS s ∗ iface.tok p n ∗ blockAny p.toNat n))) _
    dsimp only at hdi
    refine SPEC.memPre (sep_mono_right _ (unpack s p n)) ?_
    rw [St_ex]; refine SPEC.sexists fun fs => ?_
    rw [St_ex]; refine SPEC.sexists fun h => ?_
    rw [St_ex]; refine SPEC.sexists fun sz => ?_
    rw [St_pure]
    refine SPEC.spure fun ⟨hs, hf⟩ => ?_
    obtain ⟨hpn, hp0⟩ := tok_facts hf
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 128) (k := 3)
      (pc := 0x4013b0) rfl (fit 128 3) (r := .rdi) (by decide) d128) ?_
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 131) (k := 2)
      (pc := 0x4013b0 + 3#64) (pc' := 0x4013b5) (by decide) (fit 131 2) (c := .e) (rel := 0x16) ?_
      d131 (by decide)) ?_
    · rw [eval_e_test, hdi]; simpa using hp0
    refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ wordPt sp.toNat ret ∗ hdrSeg fs h ∗ strue ∗
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
      wordPt sp.toNat ret ∗ hdrSeg fs h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
      blockAny (p.toNat + n) (sz - n) ∗ blockAny p.toNat n) (by ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 144) (k := 4)
      (pc := 0x4013bc + 4#64) (pc' := 0x4013c4) (by decide) (fit 144 4) (base := .rdi) (src := .rax)
      (by decide) (by decide) (by decide) (disp := 8) (entails_refl _) d144 (by decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi, hrdi]; rfl)) ?_
    refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ wordPt ((p - 16#64) + 8#64).toNat _ ∗
      wordPt sp.toNat ret ∗ hdrSeg fs h ∗ strue ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
      blockAny (p.toNat + n) (sz - n) ∗ blockAny p.toNat n) (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 148) (k := 7)
      (pc := 0x4013c4) (pc' := 0x4013cb) (by decide) (fit 148 7) (src := .rdi) (by decide)
      (disp := 0x1cd5) (wordPt_blockAny _ _) d148 (by decide) (by decide)) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt flAddr.toNat _ ∗
      wordPt ((p - 16#64) + 8#64).toNat _ ∗ hdrSeg fs h ∗ strue ∗
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
    refine repack s fs h p _ sz n hs hf ?_
    simp only [hdi, hrdi]

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree
