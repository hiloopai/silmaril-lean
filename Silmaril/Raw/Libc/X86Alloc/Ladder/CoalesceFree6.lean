module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree5

/-! # Proofs: rung 06 (coalescing) `free` — the entry and the result -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Coalesce
open Silmaril.Libc.X86Alloc.Ladder.FirstFit (iface flAddr)
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.Loop
open Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree (unpack tok_facts)

theorem free_sat :
    (freeSpec iface.toIface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.1) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  rcases x with ⟨p, _ | n⟩
  · -- free(NULL)
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (iface.toIface.mm ∗ ⌜p = 0⌝))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜p = 0⌝ ∗ iface.toIface.mm)) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hp => ?_
    dsimp only at hdi
    subst hp
    refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 128) (k := 3)
      (pc := 0x4013b0) rfl (fit 128 3) (r := .rsi) (q := .rdi) (by decide) (by decide) (by decide)
      e128) ?_
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 131) (k := 3)
      (pc := 0x4013b0 + 3#64) (by decide) (fit 131 3) (r := .rdi) (by decide) e131) ?_
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 134) (k := 2)
      (pc := 0x4013b0 + 3#64 + 3#64) (pc' := 0x401408) (by decide) (fit 134 2) (c := .e)
      (rel := 0x50) ?_ e134 (by decide)) ?_
    · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]; rfl
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 216)
      (k := 1) (pc := 0x401408) (by decide) (fit 216 1) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) q216) ?_
    exact St_post rfl (by simp only [Function.update_self]) (entails_refl _)
  · -- free(p) of a live block
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (sexists iface.mmS ∗ iface.tok p n ∗ blockAny p.toNat n))) _
    dsimp only at hdi
    rw [sexists_sep, St_ex]
    refine SPEC.sexists fun s => ?_
    refine SPEC.memPre (sep_mono_right _ (unpack s p n)) ?_
    rw [St_ex]; refine SPEC.sexists fun fs => ?_
    rw [St_ex]; refine SPEC.sexists fun h => ?_
    rw [St_ex]; refine SPEC.sexists fun sz => ?_
    rw [St_pure]
    refine SPEC.spure fun ⟨_, hf⟩ => ?_
    obtain ⟨hpn, hp0⟩ := tok_facts hf
    have hF : Block.WF ⟨p - 16#64, sz⟩ := hf.2.1
    have hpe : p = (p - 16#64) + 16#64 := hf.2.2
    -- the freed block's payload in one piece
    have hpay : (blockAny (p.toNat + n) (sz - n) ∗ blockAny p.toNat n) =
        blockAny ((p - 16#64).toNat + 16) sz := by
      rw [sep_comm, ← blockAny_add, ← hpn, Nat.add_sub_cancel' hf.1]
    refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ (wordPt sp.toNat ret ∗ hdrSeg fs h ∗
        wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
        blockAny ((p - 16#64).toNat + 16) sz ∗ strue))
      (by rw [← hpay]; ac_rfl) ?_
    refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 128) (k := 3)
      (pc := 0x4013b0) rfl (fit 128 3) (r := .rsi) (q := .rdi) (by decide) (by decide) (by decide)
      e128) ?_
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 131) (k := 3)
      (pc := 0x4013b0 + 3#64) (by decide) (fit 131 3) (r := .rdi) (by decide) e131) ?_
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 134) (k := 2)
      (pc := 0x4013b0 + 3#64 + 3#64) (pc' := 0x4013b8) (by decide) (fit 134 2) (c := .e)
      (rel := 0x50) ?_ e134 (by decide)) ?_
    · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]; simpa using hp0
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 136) (k := 7)
      (pc := 0x4013b8) (pc' := 0x4013bf) (by decide) (fit 136 7) (dst := .rax) (by decide)
      (disp := 0x1ce1) e136 (by decide) (by decide)) ?_
    refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 143) (k := 4) (pc := 0x4013bf)
      (by decide) (fit 143 4) (dst := .rdx) (by decide) e143
      (a := p - 16#64) (fun st hregs next => by
        rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdi (by decide)]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]
        rw [show BitVec.signExtend 64 (0xfffffff0 : BitVec 32) = -16#64 by decide +kernel]
        exact (BitVec.sub_eq_add_neg _ _).symm)) ?_
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 147) (k := 3)
      (pc := 0x4013bf + 4#64) (by decide) (fit 147 3) (r := .rax) (by decide) e147) ?_
    have hrsi : ∀ g : Reg → Word, g .rsi = p → g .rsi = (p - 16#64) + 16#64 := fun g hg => hg.trans hpe
    -- the head-insertion exit
    have exit248 : ∀ (g : Reg → Word) (gl : Flags), g .rax = h → g .rdx = p - 16#64 →
        g .rsi = p → g .rsp = sp →
        SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401428 g gl
          (wordPt flAddr.toNat h ∗ (wordPt sp.toNat ret ∗ hdrSeg fs h ∗
          wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
          blockAny ((p - 16#64).toNat + 16) sz ∗ strue)))
          ((freeSpec iface.toIface).SysVPost (p, some n) sp ret) := by
      intro g gl h1 h2 h3 h4
      refine SPEC.mem ?_ (path248 p n fs (p - 16#64) h sp ret sz g gl h1 h2 (hrsi g h3) h4 hF)
      ac_rfl
    by_cases hz : h = 0
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 150) (k := 2)
        (pc := 0x4013bf + 4#64 + 3#64) (pc' := 0x401428) (by decide) (fit 150 2) (c := .e)
        (rel := 0x60) ?_ e150 (by decide)) ?_
      · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hz]; rfl
      exact exit248 _ _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 150) (k := 2)
      (pc := 0x4013bf + 4#64 + 3#64) (pc' := 0x4013c8) (by decide) (fit 150 2) (c := .e)
      (rel := 0x60) ?_ e150 (by decide)) ?_
    · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; simpa using hz
    refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 152) (k := 3) (pc := 0x4013c8)
      (by decide) (fit 152 3) (r := .rax) (q := .rdx) (by decide) (by decide) (by decide) e152) ?_
    by_cases hge : (p - 16#64).toNat ≤ h.toNat
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 155) (k := 2)
        (pc := 0x4013c8 + 3#64) (pc' := 0x401428) (by decide) (fit 155 2) (c := .ae)
        (rel := 0x5b) ?_ e155 (by decide)) ?_
      · rw [eval_ae_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, decide_eq_true hge]
      exact exit248 _ _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 155) (k := 2)
      (pc := 0x4013c8 + 3#64) (pc' := 0x4013cd) (by decide) (fit 155 2) (c := .ae)
      (rel := 0x5b) ?_ e155 (by decide)) ?_
    · rw [eval_ae_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, decide_eq_false hge]
    refine SPEC.trans (c_nop E (b := 0x401330) (code := code) (o := 157) (k := 3) (pc := 0x4013cd)
      (by decide) (fit 157 3) e157) ?_
    -- enter the walk
    cases fs with
    | nil =>
      refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ (⌜h = 0⌝ ∗ (wordPt sp.toNat ret ∗
          wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
          blockAny ((p - 16#64).toNat + 16) sz ∗ strue))) (by rw [hdrSeg_nil]; ac_rfl) ?_
      rw [St_pure]
      exact SPEC.spure fun h0 => absurd h0 hz
    | cons c rest' =>
      refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_left _
        (hdrSeg_head c rest' h)))) ?_
      refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ (⌜h = c.addr ∧ c.WF⌝ ∗ (wordPt sp.toNat ret ∗
          hdrSeg (c :: rest') h ∗ wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗
          blockAny ((p - 16#64) + 8#64).toNat 8 ∗ blockAny ((p - 16#64).toNat + 16) sz ∗ strue)))
        (by ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun ⟨hc, _⟩ => ?_
      subst hc
      refine SPEC.conseq ?_ (SPEC.loop wμ _ (WInv (p - 16#64) sz sp ret) _
        (wbody p n (p - 16#64) sp ret sz hF) ⟨[], c, rest'⟩) (entails_refl _)
      refine sexists_intro _ (sexists_intro _ (spure_sep_intro ⟨?_, ?_, ?_, ?_⟩
        (St_mono' (entails_of_eq ?_))))
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]; exact hpe
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]
      · rw [plist_nil]; simp only [FB]; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree
