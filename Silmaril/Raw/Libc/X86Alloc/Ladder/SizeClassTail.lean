module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClassDec
public import Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClassModel

/-! # Proofs: rung 07 (size classes) — the shared tails of `malloc`

`tail_pop` (`0x40134c`) pops the list of the class, `tail_bump` (`0x401378`) carves the arena
or fails, and `tail_pick` (`0x401347`) chooses between them; the four class prefixes of `malloc`
reach one of these with `rdx` the class size and `rcx` the address of its head. -/

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

theorem w_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem toNat_small (a : Nat) (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem headA_le (c : Nat) : headA c ≤ h16A := by
  unfold headA; split_ifs <;> decide

/-- The empty list of class `c` folds back into the state. -/
theorem fold_empty (s : St) (c : Nat) (hc : IsCls c) (hl : s.lst c = [])
    (hi : s.u ≤ 4096 ∧ s.u % 16 = 0) :
    (wordPt usedA (BitVec.ofNat 64 s.u) ∗ blockAny (arena + s.u) (4096 - s.u) ∗
      wordPt (headA c) 0 ∗ others s c ∗ strue) ⊢ₛ iface.mmS s := by
  rw [mm_view hc, hl]
  refine spure_sep_intro hi ?_
  have hhd : wordPt (headA c) 0 ⊢ₛ hd c [] :=
    sexists_intro 0 (entails_trans (entails_of_eq (sep_emp _).symm)
      (sep_mono_right _ (entails_of_eq (by show emp = ⌜(0 : Word) = 0⌝; rw [eq_self, spure_true_emp]))))
  refine entails_trans (entails_of_eq (show _ = (wordPt (headA c) 0 ∗ others s c ∗
    (wordPt usedA (BitVec.ofNat 64 s.u) ∗ blockAny (arena + s.u) (4096 - s.u)) ∗ strue) by ac_rfl))
    (sep_mono_left _ hhd)

variable {sp ret : Word} {fl : Silmaril.X86.Flags}

/-- `mov (%rax),%rdx; mov %rdx,(%rcx); ret`: pop the list of the class. -/
theorem tail_pop (f : Reg → Word) (hrsp : f .rsp = sp) (s : St) (n : Word) (p q : Word)
    (ps : List Word) (hn : n.toNat ≤ 128) (hl : s.lst (cls n.toNat) = p :: ps)
    (hi : s.u ≤ 4096 ∧ s.u % 16 = 0) (hp : p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat)
    (hrax : f .rax = p) (hrcx : f .rcx = BitVec.ofNat 64 (headA (cls n.toNat))) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40134c f fl (wordPt p.toNat q ∗
      wordPt (headA (cls n.toNat)) p ∗ wordPt sp.toNat ret ∗
      (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
        blockAny (p.toNat + 8) (cls n.toNat - 8) ∗ clist (cls n.toNat) ps q ∗
        others s (cls n.toNat) ∗ arenaPt s.u ∗ strue)))
      ((mallocSpecF iface).SysVPost (s, n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hh : headA (cls n.toNat) < 2 ^ 64 := by have := headA_le (cls n.toNat); simp only [h16A] at this; omega
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 28) (k := 3) (pc := 0x40134c)
    (pc' := 0x40134f) (by decide) (fit 28 3) (base := .rax) (dst := .rdx) (by decide) (by decide)
    (by decide) (disp := 0) d28 (by decide) (by simp [hrax])) ?_
  refine SPEC.mem (M' := wordPt (headA (cls n.toNat)) p ∗ wordPt p.toNat q ∗ wordPt sp.toNat ret ∗
    (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
      blockAny (p.toNat + 8) (cls n.toNat - 8) ∗ clist (cls n.toNat) ps q ∗
      others s (cls n.toNat) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 31) (k := 3) (pc := 0x40134f)
    (pc' := 0x401352) (by decide) (fit 31 3) (base := .rcx) (src := .rdx) (by decide) (by decide)
    (by decide) (disp := 0) (wordPt_blockAny _ _) d31 (by decide)
    (by simp [Function.update, hrcx, toNat_small _ hh])) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt (headA (cls n.toNat)) q ∗
    wordPt p.toNat q ∗ wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗
    blockAny (p.toNat - 8) 8 ∗ blockAny (p.toNat + 8) (cls n.toNat - 8) ∗
    clist (cls n.toNat) ps q ∗ others s (cls n.toNat) ∗ arenaPt s.u ∗ strue))
    (by simp only [Function.update_self]; ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 34) (k := 1)
    (pc := 0x401352) (by decide) (fit 34 1)
    (by simp only [Function.update_of_ne (show Reg.rsp ≠ .rdx by decide), hrsp]) r34) ?_
  exact St_post rfl (by simp only [Function.update_self])
    (post_pop s n p q ps hn hl hi hp _ (by
      simp only [Function.update_of_ne (show Reg.rax ≠ .rsp by decide),
        Function.update_of_ne (show Reg.rax ≠ .rdx by decide), hrax]))

theorem arena_split (u : Nat) (hu : u + 16 ≤ 4096) :
    blockAny (arena + u) (4096 - u) = (blockAny (arena + u) 8 ∗ blockAny (arena + u + 8) 8 ∗
      blockAny (arena + u + 16) (4096 - u - 16)) := by
  rw [show arena + u + 16 = arena + u + 8 + 8 by omega, ← blockAny_add, ← blockAny_add]
  congr 1; omega

/-- The arena: `used`, the room check, the header, the new cursor. -/
theorem tail_bump (f : Reg → Word) (hrsp : f .rsp = sp) (s : St) (n : Word)
    (hn : n.toNat ≤ 128) (hl : s.lst (cls n.toNat) = []) (hi : s.u ≤ 4096 ∧ s.u % 16 = 0)
    (hrax : f .rax = 0) (hrdx : f .rdx = BitVec.ofNat 64 (cls n.toNat)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401378 f fl
      (wordPt usedA (BitVec.ofNat 64 s.u) ∗ blockAny (arena + s.u) (4096 - s.u) ∗
        wordPt (headA (cls n.toNat)) 0 ∗ wordPt sp.toNat ret ∗ others s (cls n.toNat) ∗ strue))
      ((mallocSpecF iface).SysVPost (s, n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hcf := (isCls_cls n.toNat).facts
  have hu64 : s.u < 2 ^ 64 := by omega
  -- mov used(%rip),%rsi; mov $0x1000,%ecx; lea 0x10(%rdx),%rdi; sub %rsi,%rcx; cmp %rdi,%rcx
  refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 72) (k := 7)
    (pc := 0x401378) (pc' := 0x40137f) (by decide) (fit 72 7) (dst := .rsi) (by decide)
    (disp := 0x1d69) d72 (by decide) (by decide)) ?_
  refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 79) (k := 5)
    (pc := 0x40137f) (pc' := 0x401384) (by decide) (fit 79 5) (r := .rcx) (by decide) d79
    (by decide)) ?_
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 84) (k := 4) (pc := 0x401384)
    (by decide) (fit 84 4) (dst := .rdi) (by decide) d84
    (a := BitVec.ofNat 64 (cls n.toNat + 16)) (fun st hregs next => by
      rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdx (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = BitVec.ofNat 64 16 by decide +kernel,
        w_add])) ?_
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 88) (k := 3)
    (pc := 0x401384 + BitVec.ofNat 64 4) (by decide) (fit 88 3) (op := .sub) (by decide)
    (r := .rcx) (q := .rsi) (by decide) (by decide) (by decide) d88) ?_
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 91) (k := 3)
    (pc := 0x401384 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3) (by decide) (fit 91 3) (r := .rcx)
    (q := .rdi) (by decide) (by decide) (by decide) d91) ?_
  have hsub : Silmaril.X86.Ext.AluOp.resultN .sub ((0x1000 : BitVec 32).setWidth 64)
      (BitVec.ofNat 64 s.u) = BitVec.ofNat 64 (4096 - s.u) := by
    rw [show ((0x1000 : BitVec 32).setWidth 64) = BitVec.ofNat 64 4096 by decide +kernel]
    show BitVec.ofNat 64 4096 - BitVec.ofNat 64 s.u = _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_small _ hu64, toNat_small 4096 (by decide),
      toNat_small _ (by omega)]
    omega
  have hrcx' : (4096 - s.u : Nat) < 2 ^ 64 := by omega
  have hrdi' : cls n.toNat + 16 < 2 ^ 64 := by omega
  by_cases hroom : cls n.toNat + 16 ≤ 4096 - s.u
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 94) (k := 2)
      (pc := 0x401384 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3 + BitVec.ofNat 64 3)
      (pc' := 0x401390) (by decide) (fit 94 2) (c := .b) (rel := 0x1d) ?_ d94 (by decide)) ?_
    · rw [eval_b_cmp]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsub]
      rw [toNat_small _ hrcx', toNat_small _ hrdi']
      simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt]; exact hroom
    -- lea 0x10(%rsi),%rax; mov %rdx,arena(%rsi); lea (%rdx,%rax),%rcx; lea arena+16(%rsi),%rax
    refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 96) (k := 4) (pc := 0x401390)
      (by decide) (fit 96 4) (dst := .rax) (by decide) d96
      (a := BitVec.ofNat 64 (s.u + 16)) (fun st hregs next => by
        rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rsi (by decide)]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
        rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = BitVec.ofNat 64 16 by decide +kernel,
          w_add])) ?_
    refine SPEC.mem (M' := blockAny (arena + s.u) 8 ∗ (wordPt usedA (BitVec.ofNat 64 s.u) ∗
      blockAny (arena + s.u + 8) 8 ∗ blockAny (arena + s.u + 16) (4096 - s.u - 16) ∗
      wordPt (headA (cls n.toNat)) 0 ∗ wordPt sp.toNat ret ∗ others s (cls n.toNat) ∗ strue))
      (by rw [arena_split s.u (by omega)]; ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 100) (k := 7)
      (pc := 0x401390 + BitVec.ofNat 64 4) (pc' := 0x40139b) (by decide) (fit 100 7)
      (base := .rsi) (src := .rdx) (by decide) (by decide) (by decide) (disp := 0x4030f0)
      (entails_refl _) d100 (by decide) (by
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
        rw [show BitVec.signExtend 64 (0x4030f0 : BitVec 32) = BitVec.ofNat 64 arena by
          decide +kernel, w_add, toNat_small _ (by simp only [arena]; omega), Nat.add_comm])) ?_
    refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 107) (k := 4)
      (pc := 0x40139b) (by decide) (fit 107 4) (dst := .rcx) (by decide) d107
      (a := BitVec.ofNat 64 (s.u + cls n.toNat + 16)) (fun st hregs next => by
        rw [idx_addr, hregs .rdx (by decide), hregs .rax (by decide)]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
        rw [show BitVec.signExtend 64 (0 : BitVec 32) = BitVec.ofNat 64 0 by decide +kernel,
          w_add, w_add]
        congr 1; omega)) ?_
    refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 111) (k := 7)
      (pc := 0x40139b + BitVec.ofNat 64 4) (by decide) (fit 111 7) (dst := .rax) (by decide) d111
      (a := BitVec.ofNat 64 (arena + s.u + 16)) (fun st hregs next => by
        rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rsi (by decide)]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
        rw [show BitVec.signExtend 64 (0x403100 : BitVec 32) = BitVec.ofNat 64 (arena + 16) by
          decide +kernel, w_add]
        congr 1; omega)) ?_
    refine SPEC.mem (M' := wordPt usedA (BitVec.ofNat 64 s.u) ∗ (wordPt (arena + s.u) _ ∗
      blockAny (arena + s.u + 8) 8 ∗ blockAny (arena + s.u + 16) (4096 - s.u - 16) ∗
      wordPt (headA (cls n.toNat)) 0 ∗ wordPt sp.toNat ret ∗ others s (cls n.toNat) ∗ strue))
      (by ac_rfl) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 118) (k := 7)
      (pc := 0x40139b + BitVec.ofNat 64 4 + BitVec.ofNat 64 7) (pc' := 0x4013ad) (by decide)
      (fit 118 7) (src := .rcx) (by decide) (disp := 0x1d3b) (wordPt_blockAny _ _) d118
      (by decide) (by decide)) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt usedA _ ∗ wordPt (arena + s.u) _ ∗
      blockAny (arena + s.u + 8) 8 ∗ blockAny (arena + s.u + 16) (4096 - s.u - 16) ∗
      wordPt (headA (cls n.toNat)) 0 ∗ others s (cls n.toNat) ∗ strue)) (by ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 125)
      (k := 1) (pc := 0x4013ad) (by decide) (fit 125 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r125) ?_
    refine St_post rfl (by simp only [Function.update_self]) ?_
    simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
    exact post_bump s n hn hl hi hroom _ _ rfl rfl
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 94) (k := 2)
      (pc := 0x401384 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3 + BitVec.ofNat 64 3)
      (pc' := 0x4013ad) (by decide) (fit 94 2) (c := .b) (rel := 0x1d) ?_ d94 (by decide)) ?_
    · rw [eval_b_cmp]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsub]
      rw [toNat_small _ hrcx', toNat_small _ hrdi']
      simp only [Option.some.injEq, decide_eq_true_eq]; omega
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt usedA (BitVec.ofNat 64 s.u) ∗
      blockAny (arena + s.u) (4096 - s.u) ∗ wordPt (headA (cls n.toNat)) 0 ∗
      others s (cls n.toNat) ∗ strue)) (by ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 125)
      (k := 1) (pc := 0x4013ad) (by decide) (fit 125 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r125) ?_
    refine St_post rfl (by simp only [Function.update_self]) ?_
    refine post_fail s n ?_ (fold_empty s _ (isCls_cls _) hl hi) _ ?_
    · simp only [ref, show ¬ 128 < n.toNat by omega, ite_false, hl, hroom]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]

/-- `test %rax,%rax; je`: the list of the class is empty (`tail_bump`) or not (`tail_pop`). -/
theorem tail_pick (f : Reg → Word) (hrsp : f .rsp = sp) (s : St) (n : Word) (h : Word)
    (hn : n.toNat ≤ 128) (hi : s.u ≤ 4096 ∧ s.u % 16 = 0)
    (hrax : f .rax = h) (hrdx : f .rdx = BitVec.ofNat 64 (cls n.toNat))
    (hrcx : f .rcx = BitVec.ofNat 64 (headA (cls n.toNat))) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401347 f fl
      (wordPt (headA (cls n.toNat)) h ∗ wordPt sp.toNat ret ∗
        clist (cls n.toNat) (s.lst (cls n.toNat)) h ∗ others s (cls n.toNat) ∗ arenaPt s.u ∗
        strue))
      ((mallocSpecF iface).SysVPost (s, n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 23) (k := 3) (pc := 0x401347)
    (by decide) (fit 23 3) (r := .rax) (by decide) d23) ?_
  cases hl : s.lst (cls n.toNat) with
  | nil =>
    refine SPEC.mem (M' := wordPt (headA (cls n.toNat)) h ∗ (⌜h = 0⌝ ∗ (wordPt sp.toNat ret ∗
      others s (cls n.toNat) ∗ arenaPt s.u ∗ strue))) (by simp only [clist]; ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun h0 => ?_
    subst h0
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 26) (k := 2)
      (pc := 0x401347 + BitVec.ofNat 64 3) (pc' := 0x401378) (by decide) (fit 26 2) (c := .e)
      (rel := 0x2c) ?_ d26 (by decide)) ?_
    · rw [eval_e_test, hrax]; rfl
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
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 26) (k := 2)
      (pc := 0x401347 + BitVec.ofNat 64 3) (pc' := 0x40134c) (by decide) (fit 26 2) (c := .e)
      (rel := 0x2c) ?_ d26 (by decide)) ?_
    · rw [eval_e_test, hrax]; simpa using hp.1
    refine SPEC.mem (M' := wordPt h.toNat q ∗ wordPt (headA (cls n.toNat)) h ∗ wordPt sp.toNat ret ∗
      (wordPt (h.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (h.toNat - 8) 8 ∗
        blockAny (h.toNat + 8) (cls n.toNat - 8) ∗ clist (cls n.toNat) ps q ∗
        others s (cls n.toNat) ∗ arenaPt s.u ∗ strue)) (by ac_rfl) ?_
    exact tail_pop f hrsp s n h q ps hn hl hi hp hrax hrcx

end Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass
