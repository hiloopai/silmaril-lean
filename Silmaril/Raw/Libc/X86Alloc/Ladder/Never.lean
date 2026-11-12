module

public import Silmaril.Libc.X86Alloc.Ladder.Never.Defs
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 01 (`never`) meets `Iface.never` -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Never

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.Never
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps

theorem malloc_sat :
    (mallocSpec Iface.never).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun n => n) (fun _ => rfl) fun x sp ret f fl _ hsp _ => ?_
  refine SPEC.trans (c_xor32 E (b := 0x401330) (code := code) (o := 0) (k := 2) rfl (by decide)
    (r := .rax) (by decide) (by decide)) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (o := 2) (k := 1) rfl (by decide)
    (by simp [Function.update, hsp]) (by decide)) ?_
  refine St_post rfl (by simp [Function.update]) ?_
  have hv : (Function.update (Function.update f .rax 0) .rsp (sp + 8#64)) .rax = 0 := by
    simp [Function.update]
  show strue ⊢ₛ (strue ∗ sor ⌜_ = 0⌝ _)
  rw [hv]
  exact entails_trans (spure_sep_intro rfl (entails_refl strue))
    (entails_trans (entails_of_eq (sep_comm _ _)) (sep_mono (entails_refl _) (sor_intro_left _ _)))

theorem free_sat :
    (freeSpec Iface.never).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.1) (fun _ => rfl) fun x sp ret f fl _ hsp _ => ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 16) (k := 1)
    rfl (by decide) hsp (by decide)) ?_
  exact St_post rfl (by simp [Function.update]) (entails_strue _)

end Silmaril.Raw.Libc.X86Alloc.Ladder.Never
