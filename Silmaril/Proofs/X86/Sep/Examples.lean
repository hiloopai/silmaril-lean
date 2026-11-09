module

public import Silmaril.X86.Sep.SysV.Thms

/-!
# Proofs: `push rax; pop rbx` in separation logic

Behind `Silmaril/X86/Sep/Examples.lean`: the two instruction triples `push_step` and
`pop_step`, each framed with what the other instruction owns, composed with `Triple.trans`;
the rearrangements are `ac_rfl`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepExamples

open Silmaril.X86 (Word Byte Reg Insn)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

variable {σ : Type} {I : Isa σ}

theorem encode_push_rax : Insn.encode (.push .rax) = [0x50] := by decide
theorem encode_pop_rbx : Insn.encode (.pop .rbx) = [0x5b] := by decide

theorem push_pop (E : Silmaril.X86.Open.isa.Extends I) (pc s v : Word)
    (hpc : pc.toNat + 1 < 2 ^ 64) (hs : 8 ≤ s.toNat) :
    SPEC I (codePt pc.toNat [0x50, 0x5b])
      (ripPt pc ∗ regPt .rsp s ∗ regPt .rax v ∗ regAny .rbx ∗ blockAny (s.toNat - 8) 8)
      (ripPt (pc + 2#64) ∗ regPt .rsp s ∗ regPt .rax v ∗ regPt .rbx v ∗
        wordPt (s.toNat - 8) v) := by
  have epc : (pc + 1#64).toNat = pc.toNat + 1 := by bv_omega
  have esp : (s - 8#64).toNat = s.toNat - 8 := by bv_omega
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have e2 : pc + 1#64 + 1#64 = pc + 2#64 := by bv_omega
  have hcode : codePt pc.toNat [0x50, 0x5b] =
      (codePt pc.toNat [0x50] ∗ codePt (pc + 1#64).toNat [0x5b]) := by
    rw [epc, show ([0x50, 0x5b] : List Byte) = [0x50] ++ [0x5b] from rfl, codePt,
      bytesAt_append]
    rfl
  have h1 := Triple.frame (push_step E pc s v .rax (by decide) hs)
    (codePt (pc + 1#64).toNat [0x5b] ∗ regAny .rbx)
  have h2 := Triple.frame (pop_step E (pc + 1#64) (s - 8#64) v .rbx (by decide))
    (codePt pc.toNat [0x50] ∗ regPt .rax v)
  rw [encode_push_rax] at h1
  rw [encode_pop_rbx] at h2
  have l1 : BitVec.ofNat 64 (Insn.push .rax).length = 1#64 := by decide
  have l2 : BitVec.ofNat 64 (Insn.pop .rbx).length = 1#64 := by decide
  rw [l1] at h1
  rw [l2, esp, eback, e2] at h2
  unfold SPEC
  rw [hcode]
  refine Triple.trans (Triple.pre (entails_of_eq ?_) h1) (Triple.post (Triple.pre
    (entails_of_eq ?_) h2) (entails_of_eq ?_)) <;> ac_rfl

end Silmaril.Proofs.X86.SepExamples
