module

public import Silmaril.Proofs.X86.Link.FnSpec.Step

/-!
# Proofs: calling an import in the step-indexed logic

* `code_triple`: an instruction triple that owns its own bytes (`codePt pc bytes`) runs
  inside a code region `Code D bs` that holds those bytes.
* `Progress.frame`, `Progress.conseq`: strict progress is preserved by frames and
  consequence.
* `scall_rule`: **the step-indexed call rule.** A `call rel32` whose bytes are in the code
  region and whose target is the address `f` of a function that is `Safe n` for `S` (an
  import, in a `TU.Sat` proof) behaves as one instruction that consumes `S`'s arguments and
  precondition and returns `rax ↦ v` with `S.post`, at index `n + 1`. The call step pays for
  the index. It is the step-indexed counterpart of `call_rule`
  (`Silmaril.X86.Sep.SysV.Thms`), and like it is derived from A's `call_step` and the
  frame rule.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Link.FnSpec


open Silmaril.X86 (MState Word Byte Reg Insn)
open Silmaril.X86.Sep
open Silmaril.X86.Link.FnSpec
open Silmaril.X86.Safe

variable {D : Nat → Prop} {bs : Nat → Byte}

/-- An instruction triple inside a code region. -/
theorem code_triple {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} {pc : Nat} {bytes : List Byte}
    (hD : ∀ i (hi : i < bytes.length), D (pc + i) ∧ bs (pc + i) = bytes[i]) {P Q : SProp}
    (h : Triple I (codePt pc bytes ∗ P) (codePt pc bytes ∗ Q)) :
    Triple I (Code D bs ∗ P) (Code D bs ∗ Q) := by
  rw [code_split bytes pc hD]
  exact Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame h (Code (fun x => D x ∧ ¬ (pc ≤ x ∧ x < pc + bytes.length)) bs))
    (entails_of_eq (by ac_rfl))

theorem toNat_sub_eight' {s : Word} (hs : 8 ≤ s.toNat) : (s - 8#64).toNat = s.toNat - 8 := by
  bv_omega

/-- **The step-indexed call rule**, on every machine that extends the open machine. -/
theorem scall_rule {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} (E : Silmaril.X86.Open.isa.Extends I)
    {S : FnSpec} {ctx : Silmaril.X86.Link.Contract.Image} {n f : Nat}
    {pc s : Word} {rel : BitVec 32} (hc : Covers ctx D bs) (hf : SafeOn I n f S ctx)
    (hD : ∀ i (hi : i < (Insn.encode (.call rel)).length),
      D (pc.toNat + i) ∧ bs (pc.toNat + i) = (Insn.encode (.call rel))[i])
    (htarget : pc + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hA : FnSpec.EntryAligned (s - 8#64)) (hlow : S.stack + 8 ≤ s.toNat) (x : S.Arg) :
    Silmaril.X86.Safe.STriple I (n + 1)
      (Code D bs ∗ ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.pre x)
      (Code D bs ∗ sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) := by
  have esp := toNat_sub_eight' (s := s) (by omega)
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have hne : s ≠ s - 8#64 := by bv_omega
  have hcall := code_triple hD (call_step E pc s rel (by omega))
  rw [htarget] at hcall
  have hprog : Silmaril.X86.Safe.Progress I
      (regPt .rsp s ∗ Code D bs ∗ ripPt pc ∗ blockAny (s.toNat - 8) 8)
      (regPt .rsp (s - 8#64) ∗ Code D bs ∗ ripPt (BitVec.ofNat 64 f) ∗
        wordPt (s.toNat - 8) (pc + 5#64)) :=
    progress_of_rsp hne (Triple.conseq (entails_of_eq (by ac_rfl)) hcall
      (entails_of_eq (by ac_rfl)))
  have hcallee := hf D bs hc x (s - 8#64) (pc + 5#64) hA (by rw [esp]; omega)
  refine STriple.progress_seq
    (Progress.conseq ?_ (Progress.frame hprog
      (SysVRegs (S.args x) ∗ flagsAny ∗ blockAny (s.toNat - 8 - S.stack) S.stack ∗ S.pre x))
      (entails_refl _))
    (STriple.conseq ?_ hcallee ?_)
  · apply entails_of_eq
    rw [show s.toNat - 8 = s.toNat - 8 - S.stack + S.stack by omega, blockAny_add,
      show s.toNat - 8 - S.stack + S.stack - S.stack = s.toNat - 8 - S.stack by omega,
      show s.toNat - 8 - S.stack + S.stack = s.toNat - 8 by omega]
    ac_rfl
  · apply entails_of_eq
    simp only [FnSpec.SysVPre, FnSpec.SysVEntry]
    rw [esp]
    ac_rfl
  · simp only [FnSpec.SysVPost, FnSpec.SysVExit]
    rw [esp, eback, sep_sexists]
    refine sexists_elim fun v => ?_
    rw [sep_sexists]
    refine sexists_intro v (entails_of_eq ?_)
    ac_rfl

end Silmaril.Proofs.X86.Link.FnSpec
