module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree6
public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitRel
public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit

/-!
# Proofs: rung 06 (coalescing) against `coalRel`

`malloc` returns the first fit of the exact free list (its bytes are rung 05's: `malloc_sat_rel`);
`free` keeps *some* well-formed free list (the coalescing `free_sat`, whose loose state is any
`hdrSeg`); `free(NULL)` keeps the exact list (a direct run, `null_free`).
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
open Silmaril.Libc.X86Alloc.Ladder.FirstFit (iface ifaceR flAddr ffRel)
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole

/-- The exact state is a loose state. -/
theorem mmR_mm (s : List Block) : ifaceR.mmS s ⊢ₛ iface.toIface.mm :=
  sexists_elim fun h => sexists_intro ([] : List Block) (sexists_intro s (sexists_intro h
    (spure_sep_intro (fun _ hb => absurd hb List.not_mem_nil) (entails_refl _))))

/-- A loose state is some exact state. -/
theorem mm_mmR : iface.toIface.mm ⊢ₛ sexists fun (s' : List Block) => ⌜True⌝ ∗ ifaceR.mmS s' :=
  sexists_elim fun _ => sexists_elim fun fl => sexists_elim fun h =>
    spure_sep_elim fun _ => sexists_intro fl (spure_sep_intro trivial (sexists_intro h
      (entails_refl _)))

/-- **`free(NULL)`**, for any leaf one-argument spec whose precondition gives its postcondition. -/
theorem null_free (S : FnSpec) (hS : S.stack = 0) {x : S.Arg} (hargs : S.args x = [0])
    (hM : ∀ v, S.pre x ⊢ₛ S.post x v) (sp ret : Word) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (S.SysVPre x 0x4013b0 sp ret)
      (S.SysVPost x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.conseq (entry_St hS hargs _ sp ret) ?_ (entails_refl _)
  refine SPEC.sexists fun f => SPEC.sexists fun fl => SPEC.spure fun ⟨hsp, hdi⟩ => ?_
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
    (k := 1) (pc := 0x401408) (by decide) (fit 216 1)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) q216) ?_
  exact St_post hS (by simp only [Function.update_self]) (hM _)

theorem free_sat_coal :
    (freeSpecR ifaceC).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  intro x sp ret hA hst
  rcases x with ⟨s, p, _ | n⟩
  · -- free(NULL): the exact list is kept
    have hpre : (freeSpecR ifaceC).SysVPre ⟨s, p, none⟩ layout.freeAt sp ret ⊢ₛ
        (⌜p = 0⌝ ∗ (freeSpecR ifaceC).SysVPre ⟨s, p, none⟩ layout.freeAt sp ret) := by
      intro hf hp
      refine (spure_sep_apply _ _ _).2 ⟨?_, hp⟩
      obtain ⟨_, _, _, _, _, hq⟩ := hp
      obtain ⟨_, _, _, _, _, hq'⟩ := hq
      exact hq'.2
    refine SPEC.conseq hpre (SPEC.spure fun hp => ?_) (entails_refl _)
    subst hp
    exact null_free (freeSpecR ifaceC) rfl (x := ⟨s, 0, none⟩) rfl
      (fun _ => show (ifaceR.mmS s ∗ ⌜(0 : Word) = 0⌝) ⊢ₛ ifaceR.mmS s by
        rw [sep_comm]; exact spure_sep_elim fun _ => entails_refl _) sp ret
  · -- free(p): some well-formed list
    refine SPEC.conseq (sep_mono_right _ (sep_mono_left _ (mmR_mm s)))
      (free_sat (p, some n) sp ret hA hst) ?_
    exact sexists_elim fun v => sexists_intro v (sep_mono_right _ mm_mmR)

theorem malloc_sat_coal :
    (mallocSpecR ifaceC).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  show (mallocSpecR ifaceC).Sat _ (codePt 0x401330 code) _
  rw [Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc.code_prefix _
    Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc.mcode_coalesce]
  exact FnSpec.SatWith.code_frame
    Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc.malloc_sat_rel _

theorem init_coal : layout.Init ⊢ₛ ifaceC.mmS Silmaril.Libc.X86Alloc.Ladder.FirstFit.relS0 :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit.initR

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree
