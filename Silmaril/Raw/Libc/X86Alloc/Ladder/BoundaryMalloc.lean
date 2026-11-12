module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM6

/-!
# Proofs: rung 08 (boundary tags) — `malloc` meets the loose interface

`body`: one iteration of the walk at `0x401371`. The size of the block `y` under inspection is
compared with `need n`; a block that is too small is passed (`rax = y.next`; the end of the list
fails, otherwise the walk continues at the next block, with a shorter rest), a block that fits
goes to `found`. Safety of the walk needs only that `rax` is a block of the list; the list and
the memory are unchanged. `malloc_sat` closes the walk with `SPEC.loop`.
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
open Silmaril.Raw.Libc.X86Alloc.Loop

/-- **One iteration of the walk.** -/
theorem body (nw sp ret : Word) (fs : List (Nat × Nat)) (x : Ix) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (LInv nw.toNat sp ret fs x)
      (sor (MQ nw sp ret) (sexists fun x' => ⌜μ x' < μ x⌝ ∗ LInv nw.toNat sp ret fs x')) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  obtain ⟨l1, y, l2⟩ := x
  refine SPEC.sexists fun f => SPEC.sexists fun fl => ?_
  refine SPEC.spure fun ⟨hrax, hrdx, hrsp, hn4, hw, hfs⟩ => ?_
  dsimp only at hrax hfs
  subst hfs
  have hH := heap_eq
  have hg := hw.1
  have hy := (wf_mid hw).1; unfold Good at hy
  obtain ⟨ha16, ha32, han, ha4⟩ := need_facts hn4
  refine SPEC.mem (M' := wordPt y.1 (wd y.2) ∗ (wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗
      wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
      wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
      wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
      tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
    (by rw [mmOf, dll_mid]; unfold blk; ac_rfl) ?_
  refine SPEC.trans (c_cmpM E (b := 0x401330) (code := code) (o := 65) (k := 3) (pc := 0x401371)
    (by decide) (fit 65 3) (src := .rdx) (by decide) d65
    (addr_reg (r := .rax) (by decide) hrax (addr_add (v := y.1) (D := 0) (by decide +kernel)
      (by omega)))) ?_
  by_cases hsm : y.2 < need nw.toNat
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 68) (k := 2)
      (pc := 0x401371 + BitVec.ofNat 64 3) (pc' := 0x401368) (by decide) (fit 68 2) (c := .b)
      (rel := 0xf2) (by rw [hrdx, eval_b_wd (by omega) (by omega)]; simp [hsm]) d68
      (by decide)) ?_
    refine SPEC.mem (M' := wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ (wordPt y.1 (wd y.2) ∗
        wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
        wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0))
      (by ac_rfl) ?_
    refine SPEC.trans (c_loadSelf E (b := 0x401330) (code := code) (o := 56) (k := 4)
      (pc := 0x401368) (pc' := 0x40136c) (by decide) (fit 56 4) (r := .rax) (by decide)
      (disp := 0x8) d56 (by decide)
      (by rw [hrax]; exact addr_add (by decide +kernel) (by omega))) ?_
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 60) (k := 3)
      (pc := 0x40136c) (by decide) (fit 60 3) (r := .rax) (by decide) d60) ?_
    have hfold : (wordPt (y.1 + 8) (wd (hdOr l2 0)) ∗ (wordPt y.1 (wd y.2) ∗
        wordPt (y.1 + 16) (wd (lastOr l1 0)) ∗ blockAny (y.1 + 24) (y.2 - 32) ∗
        wordPt (y.1 + y.2 - 8) (wd y.2) ∗ wordPt sp.toNat ret ∗
        wordPt flistA (wd (hdOr (l1 ++ y :: l2) 0)) ∗
        blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT (l1 ++ y :: l2)) ∗
        tblPt firstA (firstT (l1 ++ y :: l2)) ∗ dll l1 0 y.1 ∗ dll l2 y.1 0)) =
        (wordPt sp.toNat ret ∗ mmOf (l1 ++ y :: l2)) := by
      rw [mmOf, dll_mid]; unfold blk; ac_rfl
    rw [hfold]
    cases l2 with
    | nil =>
      refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 63) (k := 2)
        (pc := 0x40136c + BitVec.ofNat 64 3) (pc' := 0x4013d0) (by decide) (fit 63 2) (c := .e)
        (rel := 0x5f) (by rw [Function.update_self, eval_e_wd (by decide)]; rfl) d63
        (by decide)) ?_
      refine SPEC.conseq (entails_refl _) ?_ (sor_intro_left _ _)
      exact ret_fail (o := 160) (by decide) (fit 160 1) r160 _ _
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
        (by rw [Function.update_self]; rfl) hw
    | cons z l2' =>
      have hz := good_lt hg ⟨z, by simp, rfl⟩
      have hz0 : hdOr (z :: l2') 0 ≠ 0 := by simp only [hdOr]; omega
      have hz64 : hdOr (z :: l2') 0 < 2 ^ 64 := by simp only [hdOr]; omega
      refine SPEC.conseq (entails_refl _) (c_jcc_not E (b := 0x401330) (code := code) (o := 63)
        (k := 2) (pc := 0x40136c + BitVec.ofNat 64 3) (pc' := 0x401371) (by decide) (fit 63 2)
        (c := .e) (rel := 0x5f) (by rw [Function.update_self, eval_e_wd hz64]; simp [hz0]) d63
        (by decide)) ?_
      refine entails_trans ?_ (sor_intro_right _ _)
      refine sexists_intro ⟨l1 ++ [y], z, l2'⟩ (spure_sep_intro (by simp [μ]) ?_)
      refine sexists_intro _ (sexists_intro _ (spure_sep_intro ⟨?_, ?_, ?_, hn4, hw, by simp⟩
        (entails_refl _)))
      · rw [Function.update_self]; rfl
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 68) (k := 2)
      (pc := 0x401371 + BitVec.ofNat 64 3) (pc' := 0x401376) (by decide) (fit 68 2) (c := .b)
      (rel := 0xf2) (by rw [hrdx, eval_b_wd (by omega) (by omega)]; simp [hsm]) d68
      (by decide)) ?_
    refine SPEC.conseq (entails_refl _) ?_ (sor_intro_left _ _)
    refine SPEC.mem ?_ (found f _ l1 l2 y hw hn4 (by omega) hrax hrdx hrsp)
    unfold blk; ac_rfl

/-- **`malloc` meets `mallocSpec iface`.** -/
theorem malloc_sat :
    (mallocSpec iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  refine satWith_of_St rfl (fun x => x) (fun _ => rfl) fun nw sp ret f fl _ hsp hdi => ?_
  change SPEC _ (codePt 0x401330 code) (St 0x401330 f fl (wordPt sp.toNat ret ∗ mm)) _
  unfold mm
  rw [St_ex]
  refine SPEC.sexists fun fs => ?_
  rw [St_pure]
  refine SPEC.spure fun hw => ?_
  exact malloc_entry nw sp ret f fl hsp hdi fs hw fun _ =>
    SPEC.loop μ _ (LInv nw.toNat sp ret fs) _ (body nw sp ret fs)

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
