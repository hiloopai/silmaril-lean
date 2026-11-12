module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree3

/-!
# Proofs: rung 06 (coalescing) `free` — inserting at the head (offset 248)

The list is empty or its head is not below `H`: `H`'s next pointer takes the head; if the head
starts exactly where `H` ends, `H` absorbs it (offset 304); then `tail270` makes `H` the head.
-/

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

theorem path248 (p : Word) (n : Nat) (fs : List Block) (hb h0 sp ret : Word) (sz : Nat)
    (f : Reg → Word) (fl : Flags) (hrax : f .rax = h0) (hrdx : f .rdx = hb)
    (hrsi : f .rsi = hb + 16#64) (hrsp : f .rsp = sp) (hF : Block.WF ⟨hb, sz⟩) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401428 f fl (wordPt sp.toNat ret ∗
      wordPt flAddr.toNat h0 ∗ hdrSeg fs h0 ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
      blockAny (hb + 8#64).toNat 8 ∗ blockAny (hb.toNat + 16) sz ∗ strue))
      (Post p n sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hsz : sz < 2 ^ 64 := by have := hF.2.2; simp only at this; omega
  -- mov %rax, -0x8(%rsi)
  refine SPEC.mem (M' := blockAny (hb + 8#64).toNat 8 ∗ (wordPt sp.toNat ret ∗
      wordPt flAddr.toNat h0 ∗ hdrSeg fs h0 ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
      blockAny (hb.toNat + 16) sz ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 248) (k := 4)
    (pc := 0x401428) (pc' := 0x40142c) (by decide) (fit 248 4) (base := .rsi) (src := .rax)
    (by decide) (by decide) (by decide) (disp := 0xfffffff8) (entails_refl _) e248 (by decide)
    (by rw [hrsi, w_m8])) ?_
  rw [hrax]
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 252) (k := 3) (pc := 0x40142c)
    (by decide) (fit 252 3) (r := .rax) (by decide) e252) ?_
  by_cases hz : h0 = 0
  · subst hz
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 255) (k := 2)
      (pc := 0x40142c + 3#64) (pc' := 0x40143e) (by decide) (fit 255 2) (c := .e) (rel := 0x0d) ?_
      e255 (by decide)) ?_
    · rw [eval_e_test, hrax]; rfl
    refine SPEC.mem ?_ (tail270 p n ⟨hb, sz⟩ 0 0 sp ret fs f _ hrdx hrsp hF)
    dsimp only; ac_rfl
  refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 255) (k := 2)
    (pc := 0x40142c + 3#64) (pc' := 0x401431) (by decide) (fit 255 2) (c := .e) (rel := 0x0d) ?_
    e255 (by decide)) ?_
  · rw [eval_e_test, hrax]; simpa using hz
  refine SPEC.mem (M' := wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ (wordPt sp.toNat ret ∗
      wordPt flAddr.toNat h0 ∗ hdrSeg fs h0 ∗ wordPt (hb + 8#64).toNat h0 ∗
      blockAny (hb.toNat + 16) sz ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 257) (k := 4)
    (pc := 0x401431) (pc' := 0x401435) (by decide) (fit 257 4) (base := .rsi) (dst := .rcx)
    (by decide) (by decide) (by decide) (disp := 0xfffffff0) e257 (by decide)
    (by rw [hrsi, w_m16])) ?_
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 261) (k := 4) (pc := 0x401435)
    (by decide) (fit 261 4) (dst := .rdi) (by decide) e261
    (a := hb + 16#64 + BitVec.ofNat 64 sz) (fun st hregs next => by
      rw [idx_addr, hregs .rsi (by decide), hregs .rcx (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_z])) ?_
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 265) (k := 3)
    (pc := 0x401435 + 4#64) (by decide) (fit 265 3) (r := .rax) (q := .rdi) (by decide) (by decide)
    (by decide) e265) ?_
  by_cases hm : h0 = hb + 16#64 + BitVec.ofNat 64 sz
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 268) (k := 2)
      (pc := 0x401435 + 4#64 + 3#64) (pc' := 0x401460) (by decide) (fit 268 2) (c := .e)
      (rel := 0x22) ?_ e268 (by decide)) ?_
    · rw [eval_e_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]; simp [hm]
    cases fs with
    | nil =>
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜h0 = 0⌝ ∗ (wordPt flAddr.toNat h0 ∗
          wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ wordPt (hb + 8#64).toNat h0 ∗
          blockAny (hb.toNat + 16) sz ∗ strue))) (by rw [hdrSeg_nil]; ac_rfl) ?_
      rw [St_pure]
      exact SPEC.spure fun h0' => absurd h0' hz
    | cons c rest' =>
      refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
        (sep_mono_left _ (hdrSeg_head c rest' h0))))) ?_
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜h0 = c.addr ∧ c.WF⌝ ∗
          (wordPt flAddr.toNat h0 ∗ hdrSeg (c :: rest') h0 ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat h0 ∗ blockAny (hb.toNat + 16) sz ∗ strue))) (by ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun ⟨hnc, hcW⟩ => ?_
      subst hnc
      obtain ⟨hc', hbnd⟩ := contig' hb sz c hF hcW hm
      have hcs : c.size < 2 ^ 64 := by omega
      refine SPEC.mem (M' := (wordPt sp.toNat ret ∗ wordPt flAddr.toNat c.addr ∗
          wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ wordPt (hb + 8#64).toNat c.addr ∗
          blockAny (hb.toNat + 16) sz ∗ strue) ∗
          (⌜c.addr = c.addr ∧ c.WF⌝ ∗ sexists fun cn =>
            wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ wordPt (c.addr + 8#64).toNat cn ∗
            blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn))
        (by rw [hdrSeg_cons]; ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun _ => ?_
      rw [St_ex]
      refine SPEC.sexists fun cn => ?_
      refine SPEC.mem (M' := wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ (wordPt sp.toNat ret ∗
          wordPt flAddr.toNat c.addr ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat c.addr ∗ blockAny (hb.toNat + 16) sz ∗ strue ∗
          wordPt (c.addr + 8#64).toNat cn ∗ blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn))
        (by ac_rfl) ?_
      refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 304) (k := 3)
        (pc := 0x401460) (pc' := 0x401463) (by decide) (fit 304 3) (base := .rax) (dst := .rdi)
        (by decide) (by decide) (by decide) (disp := 0) e304 (by decide)
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, w_z])) ?_
      refine SPEC.mem (M' := wordPt (c.addr + 8#64).toNat cn ∗ (wordPt sp.toNat ret ∗
          wordPt flAddr.toNat c.addr ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat c.addr ∗ blockAny (hb.toNat + 16) sz ∗ strue ∗
          wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ blockAny (c.addr.toNat + 16) c.size ∗
          hdrSeg rest' cn)) (by ac_rfl) ?_
      refine SPEC.trans (c_loadSelf E (b := 0x401330) (code := code) (o := 307) (k := 4)
        (pc := 0x401463) (pc' := 0x401467) (by decide) (fit 307 4) (r := .rax) (by decide)
        (disp := 8) e307 (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, w_8])) ?_
      refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 311) (k := 5)
        (pc := 0x401467) (by decide) (fit 311 5) (dst := .rcx) (by decide) e311
        (a := BitVec.ofNat 64 (sz + 16 + c.size)) (fun st hregs next => by
          rw [idx_addr, hregs .rcx (by decide), hregs .rdi (by decide)]
          simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
          rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = 16#64 by decide +kernel]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz,
            Nat.mod_eq_of_lt hcs]
          rw [Nat.mod_eq_of_lt (a := sz + c.size) (by omega), Nat.mod_eq_of_lt (a := 16) (by omega),
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega)) ?_
      refine SPEC.mem (M' := wordPt (hb + 8#64).toNat c.addr ∗ (wordPt sp.toNat ret ∗
          wordPt flAddr.toNat c.addr ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          blockAny (hb.toNat + 16) sz ∗ strue ∗ wordPt (c.addr + 8#64).toNat cn ∗
          wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ blockAny (c.addr.toNat + 16) c.size ∗
          hdrSeg rest' cn)) (by ac_rfl) ?_
      refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 316) (k := 4)
        (pc := 0x401467 + 5#64) (pc' := 0x401470) (by decide) (fit 316 4) (base := .rsi)
        (src := .rax) (by decide) (by decide) (by decide) (disp := 0xfffffff8) (wordPt_blockAny _ _)
        e316 (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_m8])) ?_
      refine SPEC.mem (M' := wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ (wordPt sp.toNat ret ∗
          wordPt flAddr.toNat c.addr ∗ wordPt (hb + 8#64).toNat cn ∗
          blockAny (hb.toNat + 16) sz ∗ strue ∗ wordPt (c.addr + 8#64).toNat cn ∗
          wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ blockAny (c.addr.toNat + 16) c.size ∗
          hdrSeg rest' cn)) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl) ?_
      refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 320) (k := 4)
        (pc := 0x401470) (pc' := 0x401474) (by decide) (fit 320 4) (base := .rsi) (src := .rcx)
        (by decide) (by decide) (by decide) (disp := 0xfffffff0) (wordPt_blockAny _ _) e320
        (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_m16])) ?_
      refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 324) (k := 2)
        (pc := 0x401474) (by decide) (fit 324 2) (pc' := 0x40143e) e324 (by decide)) ?_
      refine SPEC.memPre (M' := wordPt hb.toNat (BitVec.ofNat 64 (sz + 16 + c.size)) ∗
          (wordPt sp.toNat ret ∗ wordPt flAddr.toNat c.addr ∗ wordPt (hb + 8#64).toNat cn ∗ strue ∗
          blockAny (hb.toNat + 16) (sz + 16 + c.size) ∗ hdrSeg rest' cn)) ?_ ?_
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
        refine sep_mono_right _ (entails_trans (entails_of_eq (show _ =
          ((wordPt sp.toNat ret ∗ wordPt flAddr.toNat c.addr ∗ wordPt (hb + 8#64).toNat cn ∗ strue ∗
          hdrSeg rest' cn) ∗ (blockAny (hb.toNat + 16) sz ∗
            wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ wordPt (c.addr + 8#64).toNat cn ∗
            blockAny (c.addr.toNat + 16) c.size)) by ac_rfl))
          (entails_trans (sep_mono_right _ (merge_pay hb.toNat sz c _ _ hc' hcW))
            (entails_of_eq (by ac_rfl))))
      refine SPEC.mem ?_ (tail270 p n ⟨hb, sz + 16 + c.size⟩ cn c.addr sp ret rest' _ _ ?_ ?_
        (merge_WF hb sz c hF hc' hcW))
      · dsimp only; ac_rfl
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 268) (k := 2)
      (pc := 0x401435 + 4#64 + 3#64) (pc' := 0x40143e) (by decide) (fit 268 2) (c := .e)
      (rel := 0x22) ?_ e268 (by decide)) ?_
    · rw [eval_e_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]; simp [hm]
    refine SPEC.mem ?_ (tail270 p n ⟨hb, sz⟩ h0 h0 sp ret fs _ _ ?_ ?_ hF)
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree
