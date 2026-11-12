module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClassTail

/-! # Proofs: rung 07 (size classes) — `malloc` meets the reference model

The request is classified by three or four unsigned comparisons; each class loads its head and
sets `rdx` (class size) and `rcx` (head address), then joins `tail_pick` (classes 16, 64, 128)
or tests the head itself (class 32); a request above 128 bytes fails. -/

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

/-- The class `c` of the state, with its head unpacked. -/
theorem view_head {c : Nat} (hc : IsCls c) (pc : Word) (f : Reg → Word) (fl : Flags) (s : St)
    (A : SProp) :
    Frame.St pc f fl (A ∗ (others s 0 ∗ arenaPt s.u ∗ strue)) = sexists fun h => Frame.St pc f fl
      (wordPt (headA c) h ∗ A ∗ clist c (s.lst c) h ∗ others s c ∗ arenaPt s.u ∗ strue) := by
  rw [others_zero hc]
  unfold hd
  simp only [Frame.St, sexists_sep, sep_sexists]
  congr 1; funext h; ac_rfl

variable {sp ret : Word} {fl : Silmaril.X86.Flags}

/-- Class 32: `test %rax,%rax; jne pop`, else `nop` into the arena. -/
theorem path32 (f : Reg → Word) (hrsp : f .rsp = sp) (s : St) (n : Word) (h : Word)
    (hn : n.toNat ≤ 128) (hi : s.u ≤ 4096 ∧ s.u % 16 = 0)
    (hrax : f .rax = h) (hrdx : f .rdx = BitVec.ofNat 64 (cls n.toNat))
    (hrcx : f .rcx = BitVec.ofNat 64 (headA (cls n.toNat))) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40136f f fl
      (wordPt (headA (cls n.toNat)) h ∗ wordPt sp.toNat ret ∗
        clist (cls n.toNat) (s.lst (cls n.toNat)) h ∗ others s (cls n.toNat) ∗ arenaPt s.u ∗
        strue))
      ((mallocSpecF iface).SysVPost (s, n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 63) (k := 3) (pc := 0x40136f)
    (by decide) (fit 63 3) (r := .rax) (by decide) d63) ?_
  cases hl : s.lst (cls n.toNat) with
  | nil =>
    refine SPEC.mem (M' := wordPt (headA (cls n.toNat)) h ∗ (⌜h = 0⌝ ∗ (wordPt sp.toNat ret ∗
      others s (cls n.toNat) ∗ arenaPt s.u ∗ strue))) (by simp only [clist]; ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun h0 => ?_
    subst h0
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 66) (k := 2)
      (pc := 0x40136f + BitVec.ofNat 64 3) (pc' := 0x401374) (by decide) (fit 66 2) (c := .ne)
      (rel := 0xd8) ?_ d66 (by decide)) ?_
    · rw [eval_ne_test, hrax]; rfl
    refine SPEC.trans (c_nop E (b := 0x401330) (code := code) (o := 68) (k := 4) (pc := 0x401374)
      (by decide) (fit 68 4) d68) ?_
    refine SPEC.mem (M' := wordPt usedA (BitVec.ofNat 64 s.u) ∗ blockAny (arena + s.u) (4096 - s.u) ∗
      wordPt (headA (cls n.toNat)) 0 ∗ wordPt sp.toNat ret ∗ others s (cls n.toNat) ∗ strue)
      (by simp only [arenaPt]; ac_rfl) ?_
    exact tail_bump f hrsp s n hn hl hi (by rw [hrax]) hrdx
  | cons p ps =>
    refine SPEC.mem (M' := wordPt (headA (cls n.toNat)) h ∗
      (⌜h = p ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗ ((wordPt sp.toNat ret ∗
        wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
        others s (cls n.toNat) ∗ arenaPt s.u ∗ strue) ∗
        sexists fun q => wordPt p.toNat q ∗ blockAny (p.toNat + 8) (cls n.toNat - 8) ∗
          clist (cls n.toNat) ps q)))
      (by simp only [clist]; ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun ⟨hhp, hp⟩ => ?_
    subst hhp
    refine SPEC.mem (M' := (wordPt (headA (cls n.toNat)) h ∗ wordPt sp.toNat ret ∗
      wordPt (h.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (h.toNat - 8) 8 ∗
      others s (cls n.toNat) ∗ arenaPt s.u ∗ strue) ∗
      sexists fun q => wordPt h.toNat q ∗ blockAny (h.toNat + 8) (cls n.toNat - 8) ∗
        clist (cls n.toNat) ps q) (by ac_rfl) ?_
    rw [St_ex]
    refine SPEC.sexists fun q => ?_
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 66) (k := 2)
      (pc := 0x40136f + BitVec.ofNat 64 3) (pc' := 0x40134c) (by decide) (fit 66 2) (c := .ne)
      (rel := 0xd8) ?_ d66 (by decide)) ?_
    · rw [eval_ne_test, hrax]; simpa using hp.1
    refine SPEC.mem (M' := wordPt h.toNat q ∗ wordPt (headA (cls n.toNat)) h ∗ wordPt sp.toNat ret ∗
      (wordPt (h.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (h.toNat - 8) 8 ∗
        blockAny (h.toNat + 8) (cls n.toNat - 8) ∗ clist (cls n.toNat) ps q ∗
        others s (cls n.toNat) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
    exact tail_pop f hrsp s n h q ps hn hl hi hp hrax hrcx

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.2) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  obtain ⟨(s : St), n⟩ := x
  change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
    (⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗ (others s 0 ∗ arenaPt s.u ∗ strue)))) _
  rw [St_pure]
  refine SPEC.spure fun hi => ?_
  dsimp only at hdi
  have hc := isCls_cls n.toNat
  refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 0) (k := 4) (pc := 0x401330)
    rfl (fit 0 4) (r := .rdi) (imm := 0x10) (by decide) d0) ?_
  have e16 : (BitVec.signExtend 64 (0x10 : BitVec 8)).toNat = 16 := by decide +kernel
  have e32 : (BitVec.signExtend 64 (0x20 : BitVec 8)).toNat = 32 := by decide +kernel
  have e64 : (BitVec.signExtend 64 (0x40 : BitVec 8)).toNat = 64 := by decide +kernel
  have e128 : (BitVec.signExtend 64 (0x80 : BitVec 32)).toNat = 128 := by decide +kernel
  by_cases h1 : 16 < n.toNat
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 4) (k := 2)
      (pc := 0x401330 + BitVec.ofNat 64 4) (pc' := 0x401358) (by decide) (fit 4 2) (c := .a)
      (rel := 0x22) (by rw [eval_a_cmp, hdi, e16]; simp [h1]) d4 (by decide)) ?_
    refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 40) (k := 4)
      (pc := 0x401358) (by decide) (fit 40 4) (r := .rdi) (imm := 0x20) (by decide) d40) ?_
    by_cases h2 : 32 < n.toNat
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 44) (k := 2)
        (pc := 0x401358 + BitVec.ofNat 64 4) (pc' := 0x4013b0) (by decide) (fit 44 2) (c := .a)
        (rel := 0x52) (by rw [eval_a_cmp, hdi, e32]; simp [h2]) d44 (by decide)) ?_
      refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 128) (k := 4)
        (pc := 0x4013b0) (by decide) (fit 128 4) (r := .rdi) (imm := 0x40) (by decide) d128) ?_
      by_cases h3 : 64 < n.toNat
      · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 132) (k := 2)
          (pc := 0x4013b0 + BitVec.ofNat 64 4) (pc' := 0x4013b6) (by decide) (fit 132 2)
          (c := .be) (rel := 0x22) (by rw [eval_be_cmp, hdi, e64]; simp; omega) d132
          (by decide)) ?_
        refine SPEC.trans (c_cmpI E (b := 0x401330) (code := code) (o := 134) (k := 7)
          (pc := 0x4013b6) (by decide) (fit 134 7) (r := .rdi) (imm := 0x80) (by decide)
          d134) ?_
        by_cases h4 : 128 < n.toNat
        · -- too big
          refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 141) (k := 2)
            (pc := 0x4013b6 + BitVec.ofNat 64 7) (pc' := 0x4013f0) (by decide) (fit 141 2)
            (c := .a) (rel := 0x31) (by rw [eval_a_cmp, hdi, e128]; simp [h4]) d141
            (by decide)) ?_
          refine SPEC.trans (c_xor32 E (b := 0x401330) (code := code) (o := 192) (k := 2)
            (pc := 0x4013f0) (by decide) (fit 192 2) (r := .rax) (by decide) d192) ?_
          refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 194)
            (k := 1) (pc := 0x4013f0 + BitVec.ofNat 64 2) (by decide) (fit 194 1)
            (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) r194) ?_
          refine St_post rfl (by simp only [Function.update_self]) ?_
          refine post_fail s n (by simp only [ref, h4, ite_true]) ?_ _
            (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
          exact spure_sep_intro hi (entails_refl _)
        · -- class 128
          have hcv : cls n.toNat = 128 := by unfold cls; split_ifs <;> omega
          refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 141) (k := 2)
            (pc := 0x4013b6 + BitVec.ofNat 64 7) (pc' := 0x4013bf) (by decide) (fit 141 2)
            (c := .a) (rel := 0x31) (by rw [eval_a_cmp, hdi, e128]; simp [h4]) d141
            (by decide)) ?_
          rw [view_head hc]
          refine SPEC.sexists fun h => ?_
          refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 143) (k := 7)
            (pc := 0x4013bf) (pc' := 0x4013c6) (by decide) (fit 143 7) (dst := .rax) (by decide)
            (disp := 0x1d02) d143 (by decide) (by rw [hcv]; decide)) ?_
          refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 150) (k := 5)
            (pc := 0x4013c6) (pc' := 0x4013cb) (by decide) (fit 150 5) (r := .rdx) (by decide)
            d150 (by decide)) ?_
          refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 155) (k := 5)
            (pc := 0x4013cb) (pc' := 0x4013d0) (by decide) (fit 155 5) (r := .rcx) (by decide)
            d155 (by decide)) ?_
          refine SPEC.trans (c_jmp32 E (b := 0x401330) (code := code) (o := 160) (k := 5)
            (pc := 0x4013d0) (pc' := 0x401347) (by decide) (fit 160 5) d160 (by decide)) ?_
          exact tail_pick _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
            s n h (by omega) hi (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
            (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
            (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
      · -- class 64
        have hcv : cls n.toNat = 64 := by unfold cls; split_ifs <;> omega
        refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 132) (k := 2)
          (pc := 0x4013b0 + BitVec.ofNat 64 4) (pc' := 0x4013d8) (by decide) (fit 132 2)
          (c := .be) (rel := 0x22) (by rw [eval_be_cmp, hdi, e64]; simp; omega) d132
          (by decide)) ?_
        rw [view_head hc]
        refine SPEC.sexists fun h => ?_
        refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 168) (k := 7)
          (pc := 0x4013d8) (pc' := 0x4013df) (by decide) (fit 168 7) (dst := .rax) (by decide)
          (disp := 0x1cf1) d168 (by decide) (by rw [hcv]; decide)) ?_
        refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 175) (k := 5)
          (pc := 0x4013df) (pc' := 0x4013e4) (by decide) (fit 175 5) (r := .rdx) (by decide)
          d175 (by decide)) ?_
        refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 180) (k := 5)
          (pc := 0x4013e4) (pc' := 0x4013e9) (by decide) (fit 180 5) (r := .rcx) (by decide)
          d180 (by decide)) ?_
        refine SPEC.trans (c_jmp32 E (b := 0x401330) (code := code) (o := 185) (k := 5)
          (pc := 0x4013e9) (pc' := 0x401347) (by decide) (fit 185 5) d185 (by decide)) ?_
        exact tail_pick _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
          s n h (by omega) hi (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
          (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
          (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
    · -- class 32
      have hcv : cls n.toNat = 32 := by unfold cls; split_ifs <;> omega
      refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 44) (k := 2)
        (pc := 0x401358 + BitVec.ofNat 64 4) (pc' := 0x40135e) (by decide) (fit 44 2) (c := .a)
        (rel := 0x52) (by rw [eval_a_cmp, hdi, e32]; simp [h2]) d44 (by decide)) ?_
      rw [view_head hc]
      refine SPEC.sexists fun h => ?_
      refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 46) (k := 7)
        (pc := 0x40135e) (pc' := 0x401365) (by decide) (fit 46 7) (dst := .rax) (by decide)
        (disp := 0x1d73) d46 (by decide) (by rw [hcv]; decide)) ?_
      refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 53) (k := 5)
        (pc := 0x401365) (pc' := 0x40136a) (by decide) (fit 53 5) (r := .rdx) (by decide)
        d53 (by decide)) ?_
      refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 58) (k := 5)
        (pc := 0x40136a) (pc' := 0x40136f) (by decide) (fit 58 5) (r := .rcx) (by decide)
        d58 (by decide)) ?_
      exact path32 _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
        s n h (by omega) hi (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
  · -- class 16
    have hcv : cls n.toNat = 16 := by unfold cls; split_ifs <;> omega
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 4) (k := 2)
      (pc := 0x401330 + BitVec.ofNat 64 4) (pc' := 0x401336) (by decide) (fit 4 2) (c := .a)
      (rel := 0x22) (by rw [eval_a_cmp, hdi, e16]; simp [h1]) d4 (by decide)) ?_
    rw [view_head hc]
    refine SPEC.sexists fun h => ?_
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 6) (k := 7)
      (pc := 0x401336) (pc' := 0x40133d) (by decide) (fit 6 7) (dst := .rax) (by decide)
      (disp := 0x1da3) d6 (by decide) (by rw [hcv]; decide)) ?_
    refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 13) (k := 5)
      (pc := 0x40133d) (pc' := 0x401342) (by decide) (fit 13 5) (r := .rdx) (by decide)
      d13 (by decide)) ?_
    refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 18) (k := 5)
      (pc := 0x401342) (pc' := 0x401347) (by decide) (fit 18 5) (r := .rcx) (by decide)
      d18 (by decide)) ?_
    exact tail_pick _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp])
      s n h (by omega) hi (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hcv]; decide)

end Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass
