module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClassMalloc

/-! # Proofs: rung 07 (size classes) — `free` meets the reference model

`free(p)` reads the class word of the header (held by the token), compares it with 16, 32 and
64 (else 128), loads that class's head and pushes `p` (`free_tail`). -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.SizeClass
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole

variable {sp ret : Word} {fl : Silmaril.X86.Flags}

/-- `mov %rdx,(%rdi); mov %rdi,(%rax); ret`: push the block. -/
theorem free_tail (f : Reg → Word) (hrsp : f .rsp = sp) (s : St) (p h : Word) (n : Nat)
    (hi : s.u ≤ 4096 ∧ s.u % 16 = 0) (hp : p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat)
    (hrdi : f .rdi = p) (hrdx : f .rdx = h) (hrax : f .rax = BitVec.ofNat 64 (headA (cls n))) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401427 f fl
      (blockAny p.toNat 8 ∗ wordPt (headA (cls n)) h ∗ wordPt sp.toNat ret ∗
        (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
          others s (cls n) ∗ arenaPt s.u ∗ strue)))
      ((freeSpecF iface).SysVPost ⟨s, p, some n⟩ sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hh : headA (cls n) < 2 ^ 64 := by have := headA_le (cls n); simp only [h16A] at this; omega
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 247) (k := 3)
    (pc := 0x401427) (pc' := 0x40142a) (by decide) (fit 247 3) (base := .rdi) (src := .rdx)
    (by decide) (by decide) (by decide) (disp := 0) (entails_refl _) d247 (by decide)
    (by simp [hrdi])) ?_
  refine SPEC.mem (M' := wordPt (headA (cls n)) h ∗ wordPt p.toNat (f .rdx) ∗ wordPt sp.toNat ret ∗
    (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
      blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
      others s (cls n) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 250) (k := 3)
    (pc := 0x40142a) (pc' := 0x40142d) (by decide) (fit 250 3) (base := .rax) (src := .rdi)
    (by decide) (by decide) (by decide) (disp := 0) (wordPt_blockAny _ _) d250 (by decide)
    (by simp [hrax, toNat_small _ hh])) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt p.toNat h ∗ wordPt (headA (cls n)) p ∗
    wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
    blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
    others s (cls n) ∗ arenaPt s.u ∗ strue)) (by rw [hrdi, hrdx]; ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 253) (k := 1)
    (pc := 0x40142d) (by decide) (fit 253 1) hrsp r253) ?_
  exact St_post rfl (by simp only [Function.update_self]) (post_push s p h n hi hp)

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.p) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  rcases x with ⟨(s : St), p, _ | n⟩
  · -- free(NULL)
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (iface.mmS s ∗ ⌜p = 0⌝))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜p = 0⌝ ∗ iface.mmS s)) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hp => ?_
    dsimp only at hdi
    subst hp
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 208) (k := 3) (pc := 0x401400)
      rfl (fit 208 3) (r := .rdi) (by decide) d208) ?_
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 211) (k := 2)
      (pc := 0x401400 + BitVec.ofNat 64 3) (pc' := 0x40142d) (by decide) (fit 211 2) (c := .e)
      (rel := 0x28) (by rw [eval_e_test, hdi]; rfl) d211 (by decide)) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 253)
      (k := 1) (pc := 0x40142d) (by decide) (fit 253 1) hsp r253) ?_
    exact St_post rfl (by simp only [Function.update_self]) (entails_refl _)
  · -- free(p) of a block of requested size n
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      ((⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗ (others s 0 ∗ arenaPt s.u ∗ strue)) ∗
        (⌜n ≤ 128 ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗
          wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny (p.toNat + n) (cls n - n)) ∗ blockAny p.toNat n))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗
      (⌜n ≤ 128 ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗
        ((wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny p.toNat n ∗ blockAny (p.toNat + n) (cls n - n)) ∗
          (others s 0 ∗ arenaPt s.u ∗ strue))))) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hi => ?_
    rw [St_pure]
    refine SPEC.spure fun ⟨hn, hp⟩ => ?_
    dsimp only at hdi
    have hc := isCls_cls n
    have hcf := hc.facts
    have hle := le_cls n hn
    rw [block_join _ _ _ (by omega) hle]
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 208) (k := 3) (pc := 0x401400)
      rfl (fit 208 3) (r := .rdi) (by decide) d208) ?_
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 211) (k := 2)
      (pc := 0x401400 + BitVec.ofNat 64 3) (pc' := 0x401405) (by decide) (fit 211 2) (c := .e)
      (rel := 0x28) (by rw [eval_e_test, hdi]; simpa using hp.1) d211 (by decide)) ?_
    have hpl := p.isLt
    refine SPEC.mem (M' := wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ wordPt sp.toNat ret ∗
      blockAny (p.toNat - 8) 8 ∗ blockAny p.toNat 8 ∗ blockAny (p.toNat + 8) (cls n - 8) ∗
      (others s 0 ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
    refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 213) (k := 4)
      (pc := 0x401405) (pc' := 0x401409) (by decide) (fit 213 4) (base := .rdi) (dst := .rax)
      (by decide) (by decide) (by decide) (disp := 0xfffffff0) d213 (by decide) (by
        rw [hdi, show BitVec.signExtend 64 (0xfffffff0 : BitVec 32) = BitVec.ofNat 64 (2 ^ 64 - 16)
          by decide +kernel, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega)) ?_
    refine SPEC.mem (M' := (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ wordPt sp.toNat ret ∗
      blockAny (p.toNat - 8) 8 ∗ blockAny p.toNat 8 ∗ blockAny (p.toNat + 8) (cls n - 8)) ∗
      (others s 0 ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
    rw [view_head hc]
    refine SPEC.sexists fun h => ?_
    refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 217) (k := 4)
      (pc := 0x401409) (by decide) (fit 217 4) (r := .rax) (imm := 0x10) (by decide) d217) ?_
    rcases hc with hcv | hcv | hcv | hcv
    · -- class 16
      refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 221) (k := 2)
        (pc := 0x401409 + BitVec.ofNat 64 4) (pc' := 0x401440) (by decide) (fit 221 2) (c := .e)
        (rel := 0x31) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d221
        (by decide)) ?_
      refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 272) (k := 7)
        (pc := 0x401440) (pc' := 0x401447) (by decide) (fit 272 7) (dst := .rdx) (by decide)
        (disp := 0x1c99) d272 (by decide) (by rw [hcv]; decide)) ?_
      refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 279) (k := 5)
        (pc := 0x401447) (pc' := 0x40144c) (by decide) (fit 279 5) (r := .rax) (by decide)
        d279 (by decide)) ?_
      refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 284) (k := 2)
        (pc := 0x40144c) (pc' := 0x401427) (by decide) (fit 284 2) d284 (by decide)) ?_
      refine SPEC.mem (M' := blockAny p.toNat 8 ∗ wordPt (headA (cls n)) h ∗ wordPt sp.toNat ret ∗
        (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
          others s (cls n) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
      exact free_tail _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
        s p h n hi hp (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
    · -- class 32
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 221) (k := 2)
        (pc := 0x401409 + BitVec.ofNat 64 4) (pc' := 0x40140f) (by decide) (fit 221 2) (c := .e)
        (rel := 0x31) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d221
        (by decide)) ?_
      refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 223) (k := 4)
        (pc := 0x40140f) (by decide) (fit 223 4) (r := .rax) (imm := 0x20) (by decide) d223) ?_
      refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 227) (k := 2)
        (pc := 0x40140f + BitVec.ofNat 64 4) (pc' := 0x401450) (by decide) (fit 227 2) (c := .e)
        (rel := 0x3b) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d227
        (by decide)) ?_
      refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 288) (k := 7)
        (pc := 0x401450) (pc' := 0x401457) (by decide) (fit 288 7) (dst := .rdx) (by decide)
        (disp := 0x1c81) d288 (by decide) (by rw [hcv]; decide)) ?_
      refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 295) (k := 5)
        (pc := 0x401457) (pc' := 0x40145c) (by decide) (fit 295 5) (r := .rax) (by decide)
        d295 (by decide)) ?_
      refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 300) (k := 2)
        (pc := 0x40145c) (pc' := 0x401427) (by decide) (fit 300 2) d300 (by decide)) ?_
      refine SPEC.mem (M' := blockAny p.toNat 8 ∗ wordPt (headA (cls n)) h ∗ wordPt sp.toNat ret ∗
        (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
          others s (cls n) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
      exact free_tail _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
        s p h n hi hp (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
    · -- class 64
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 221) (k := 2)
        (pc := 0x401409 + BitVec.ofNat 64 4) (pc' := 0x40140f) (by decide) (fit 221 2) (c := .e)
        (rel := 0x31) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d221
        (by decide)) ?_
      refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 223) (k := 4)
        (pc := 0x40140f) (by decide) (fit 223 4) (r := .rax) (imm := 0x20) (by decide) d223) ?_
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 227) (k := 2)
        (pc := 0x40140f + BitVec.ofNat 64 4) (pc' := 0x401415) (by decide) (fit 227 2) (c := .e)
        (rel := 0x3b) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d227
        (by decide)) ?_
      refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 229) (k := 4)
        (pc := 0x401415) (by decide) (fit 229 4) (r := .rax) (imm := 0x40) (by decide) d229) ?_
      refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 233) (k := 2)
        (pc := 0x401415 + BitVec.ofNat 64 4) (pc' := 0x401430) (by decide) (fit 233 2) (c := .e)
        (rel := 0x15) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d233
        (by decide)) ?_
      refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 256) (k := 7)
        (pc := 0x401430) (pc' := 0x401437) (by decide) (fit 256 7) (dst := .rdx) (by decide)
        (disp := 0x1c99) d256 (by decide) (by rw [hcv]; decide)) ?_
      refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 263) (k := 5)
        (pc := 0x401437) (pc' := 0x40143c) (by decide) (fit 263 5) (r := .rax) (by decide)
        d263 (by decide)) ?_
      refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 268) (k := 2)
        (pc := 0x40143c) (pc' := 0x401427) (by decide) (fit 268 2) d268 (by decide)) ?_
      refine SPEC.mem (M' := blockAny p.toNat 8 ∗ wordPt (headA (cls n)) h ∗ wordPt sp.toNat ret ∗
        (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
          others s (cls n) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
      exact free_tail _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
        s p h n hi hp (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
    · -- class 128
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 221) (k := 2)
        (pc := 0x401409 + BitVec.ofNat 64 4) (pc' := 0x40140f) (by decide) (fit 221 2) (c := .e)
        (rel := 0x31) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d221
        (by decide)) ?_
      refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 223) (k := 4)
        (pc := 0x40140f) (by decide) (fit 223 4) (r := .rax) (imm := 0x20) (by decide) d223) ?_
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 227) (k := 2)
        (pc := 0x40140f + BitVec.ofNat 64 4) (pc' := 0x401415) (by decide) (fit 227 2) (c := .e)
        (rel := 0x3b) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d227
        (by decide)) ?_
      refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 229) (k := 4)
        (pc := 0x401415) (by decide) (fit 229 4) (r := .rax) (imm := 0x40) (by decide) d229) ?_
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 233) (k := 2)
        (pc := 0x401415 + BitVec.ofNat 64 4) (pc' := 0x40141b) (by decide) (fit 233 2) (c := .e)
        (rel := 0x15) (by rw [eval_e_cmp, Function.update_self, hcv]; decide) d233
        (by decide)) ?_
      refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 235) (k := 7)
        (pc := 0x40141b) (pc' := 0x401422) (by decide) (fit 235 7) (dst := .rdx) (by decide)
        (disp := 0x1ca6) d235 (by decide) (by rw [hcv]; decide)) ?_
      refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 242) (k := 5)
        (pc := 0x401422) (pc' := 0x401427) (by decide) (fit 242 5) (r := .rax) (by decide)
        d242 (by decide)) ?_
      refine SPEC.mem (M' := blockAny p.toNat 8 ∗ wordPt (headA (cls n)) h ∗ wordPt sp.toNat ret ∗
        (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
          blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
          others s (cls n) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
      exact free_tail _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
        s p h n hi hp (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)

/-- **The loaded image establishes the initial state**: empty lists, an unused arena. -/
theorem init : layout.Init ⊢ₛ iface.mmS s0 := by
  unfold Layout.Init
  dsimp only [layout]
  have hw : Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 0] =
      List.replicate 8 (0 : Byte) := by decide
  have e0 : ∀ a, bytesAt RW a (List.replicate 8 0) = wordPt a 0 := by
    intro a; rw [wordPt, show (0 : Word) = BitVec.ofNat 64 0 from rfl, hw]; rfl
  rw [show arena + 4096 - h128A = 8 + (8 + (8 + (8 + (8 + 4096)))) from rfl, List.replicate_add,
    List.replicate_add, List.replicate_add, List.replicate_add, List.replicate_add, bytesPt,
    bytesAt_append, bytesAt_append, bytesAt_append, bytesAt_append, bytesAt_append]
  simp only [List.length_replicate, e0]
  have hz : ∀ c, wordPt (headA c) 0 ⊢ₛ hd c [] := fun c =>
    sexists_intro 0 (entails_trans (entails_of_eq (sep_emp _).symm)
      (sep_mono_right _ (entails_of_eq (by show emp = ⌜(0 : Word) = 0⌝; rw [eq_self, spure_true_emp]))))
  have e3 : bytesAt RW (h128A + 8 + 8 + 8 + 8 + 8) (List.replicate 4096 0) ⊢ₛ
      blockAny (arena + 0) (4096 - 0) := by
    refine entails_trans (bytesPt_blockAny _ _) (entails_of_eq ?_)
    rw [List.length_replicate]
  refine spure_sep_intro ⟨by decide, by decide⟩ ?_
  show _ ⊢ₛ (((if (0 : Nat) = 16 then emp else hd 16 []) ∗ (if (0 : Nat) = 32 then emp else hd 32 []) ∗
    (if (0 : Nat) = 64 then emp else hd 64 []) ∗ (if (0 : Nat) = 128 then emp else hd 128 [])) ∗
    (wordPt usedA (BitVec.ofNat 64 0) ∗ blockAny (arena + 0) (4096 - 0)) ∗ strue)
  simp only [reduceIte, Nat.reduceEqDiff]
  have e5 : (wordPt h128A 0 ∗ wordPt (h128A + 8) 0 ∗ wordPt (h128A + 8 + 8) 0 ∗
      wordPt (h128A + 8 + 8 + 8) 0 ∗ wordPt (h128A + 8 + 8 + 8 + 8) 0 ∗
      bytesAt RW (h128A + 8 + 8 + 8 + 8 + 8) (List.replicate 4096 0)) =
      ((wordPt (headA 16) 0 ∗ wordPt (headA 32) 0 ∗ wordPt (headA 64) 0 ∗ wordPt (headA 128) 0) ∗
        (wordPt usedA 0 ∗ bytesAt RW (h128A + 8 + 8 + 8 + 8 + 8) (List.replicate 4096 0))) := by
    rw [show h128A + 8 + 8 + 8 + 8 = usedA from rfl, show h128A + 8 + 8 + 8 = h16A from rfl,
      show h128A + 8 + 8 = h32A from rfl, show h128A + 8 = h64A from rfl,
      show headA 16 = h16A from rfl, show headA 32 = h32A from rfl,
      show headA 64 = h64A from rfl, show headA 128 = h128A from rfl]
    ac_rfl
  rw [e5]
  exact sep_mono (sep_mono (hz 16) (sep_mono (hz 32) (sep_mono (hz 64) (hz 128))))
    (entails_trans (entails_of_eq (sep_emp _).symm) (sep_mono (sep_mono_right _ e3)
      (entails_strue _)))

end Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass
