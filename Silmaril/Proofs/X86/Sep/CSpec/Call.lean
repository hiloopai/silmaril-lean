module

public import Silmaril.Proofs.X86.Sep.CSpec.Template
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.X86.Sep.Ind.Thms
/-!
# Proofs: the direct and indirect call rules for `CSpec`

Behind `Silmaril/Machine/X86/Sep/CSpec/Thms.lean`. Imports only headers (and the sibling proof
module `Template`).

* `ccall_rule`: `call rel32` to code meeting `S` (`CSpec.Sat`, every index), on any XMM
  machine extending `Open9`. The `call` step is track A's total `call_step`, lifted.
* `cicall_safe`: `call *%r` to code meeting `S` for `n` steps (`CSpec.SatN`) is a triple at
  `n + 1`: the call step pays for the index. The step law is `Sep.Ind.callR_progress` on `Open9.isa`,
  lifted by `xprogress_of_progress`. The register holding the target and the rest `X` of the
  caller's state hand the callee its `ArgsIn` and precondition, leaving `K` (as CP-4b's
  `Handoff`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepCSpec

open Silmaril.X86 (Reg XReg Word Byte MState Insn)
open Silmaril.X86.Sse9 (Xmm XState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.X86.Sep.CSpec
open Silmaril.X86.Sep.Ind (encCallR nextPc)

variable {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M]

theorem blockAny_call {s : Word} {t : Nat} (hlow : t + 8 ≤ s.toNat) :
    blockAny (s.toNat - 8 - t) (t + 8) =
      (blockAny (s.toNat - 8 - t) t ∗ blockAny (s.toNat - 8) 8) := by
  rw [blockAny_add, show s.toNat - 8 - t + t = s.toNat - 8 by omega]

/-- **The direct call rule.** -/
theorem ccall_rule {S : CSpec} {Cf : XSProp} {f pc s : Word} {rel : BitVec 32} (x : S.Arg)
    (hS : S.Sat M Cf f) (hf : pc + 5#64 + rel.signExtend 64 = f)
    (hal : s.toNat % 16 = 0) (hlow : S.stack x + 8 ≤ s.toNat) (n : Nat) :
    XSTriple M n
      (↑ₓ(codePt pc.toNat (Insn.encode (.call rel))) ∗ₓ Cf ∗ₓ
        ↑ₓ(ripPt pc ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        ArgsIn (S.shape x) ⟨s - 8#64, pc + 5#64⟩ ∗ₓ S.pre x ⟨s - 8#64, pc + 5#64⟩)
      (↑ₓ(codePt pc.toNat (Insn.encode (.call rel))) ∗ₓ Cf ∗ₓ xsexists fun rb =>
        ↑ₓ(ripPt (pc + 5#64) ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        RetOut (S.shape x) ⟨s - 8#64, pc + 5#64⟩ rb ∗ₓ S.post x ⟨s - 8#64, pc + 5#64⟩ rb) := by
  have h8 : 8 ≤ s.toNat := by omega
  have esp := toNat_sub_eight h8
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have h1 := (xstriple_of_triple (M := M) (n := n) (call_step (Silmaril.X86.SegVC.Isa.Extends.refl _) pc s rel h8)).frame
    (Cf ∗ₓ ↑ₓ(flagsAny ∗ blockAny (s.toNat - 8 - S.stack x) (S.stack x)) ∗ₓ
      ArgsIn (S.shape x) ⟨s - 8#64, pc + 5#64⟩ ∗ₓ S.pre x ⟨s - 8#64, pc + 5#64⟩)
  have h2 := (hS n x ⟨s - 8#64, pc + 5#64⟩ (entryAligned_of_call hal h8)
    (by simp only [esp]; omega)).frame (↑ₓ(codePt pc.toNat (Insn.encode (.call rel))))
  refine XSTriple.seq (XSTriple.conseq ?_ h1 ?_) (XSTriple.conseq (xentails_refl _) h2 ?_)
  · rw [blockAny_call hlow]
    simp only [lift_sep]
    exact xentails_of_eq (by ac_rfl)
  · simp only [CSpec.Pre, CSpec.Entry, EntryOf, CtlIn, esp, hf, lift_sep]
    exact xentails_of_eq (by ac_rfl)
  · simp only [CSpec.Post, CSpec.Exit, ExitOf, CtlOut, esp, eback]
    rw [xsep_xsexists, xsexists_sep, xsep_xsexists, xsep_xsexists]
    refine xsexists_mono fun rb => xentails_of_eq ?_
    simp only [lift_sep]
    ac_rfl

/-- **The indirect call rule** (`call *%r`), callee-safe form: if the code at `p` meets `S`
for `n` steps, the call meets the caller's triple at `n + 1`. The call instruction is part of
the code `C` (`hC`), which the callee's spec also uses; `hho` hands the target register and
the rest `X` of the caller's state over to the callee, leaving `K`. -/
theorem cicall_safe {S : CSpec} {C Cr X K : XSProp} {r : Reg} {pc s p : Word} {n : Nat}
    (x : S.Arg) (hS : S.SatN M n C p)
    (hC : C = (↑ₓ(codePt pc.toNat (encCallR r)) ∗ₓ Cr))
    (hal : s.toNat % 16 = 0) (hlow : S.stack x + 8 ≤ s.toNat)
    (hho : (↑ₓ(regPt r p) ∗ₓ X) ⊢ₓ
      (ArgsIn (S.shape x) ⟨s - 8#64, nextPc pc (encCallR r)⟩ ∗ₓ
        S.pre x ⟨s - 8#64, nextPc pc (encCallR r)⟩ ∗ₓ K)) :
    XSTriple M (n + 1)
      (C ∗ₓ ↑ₓ(ripPt pc ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ ↑ₓ(regPt r p) ∗ₓ X)
      (C ∗ₓ (xsexists fun rb =>
        ↑ₓ(ripPt (nextPc pc (encCallR r)) ∗ regPt .rsp s ∗ flagsAny ∗
          blockAny (s.toNat - 8 - S.stack x) (S.stack x + 8)) ∗ₓ
        RetOut (S.shape x) ⟨s - 8#64, nextPc pc (encCallR r)⟩ rb ∗ₓ
        S.post x ⟨s - 8#64, nextPc pc (encCallR r)⟩ rb) ∗ₓ K) := by
  have h8 : 8 ≤ s.toNat := by omega
  have esp := toNat_sub_eight h8
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have hP := Silmaril.X86.Sep.Ind.callR_progress
    (Silmaril.X86.SegVC.Isa.Extends.refl Silmaril.X86.Open9.isa) r pc s p h8
  have hX := XProgress.frame (xprogress_of_progress (M := M) hP)
    (Cr ∗ₓ ↑ₓ(flagsAny ∗ blockAny (s.toNat - 8 - S.stack x) (S.stack x)) ∗ₓ X)
  have hT := (hS x ⟨s - 8#64, nextPc pc (encCallR r)⟩ (entryAligned_of_call hal h8)
    (by simp only [esp]; omega)).frame K
  subst hC
  refine XSTriple.progress_seq (XProgress.conseq ?_ hX ?_) (XSTriple.conseq
    (xentails_refl _) hT ?_)
  · rw [blockAny_call hlow]
    simp only [lift_sep]
    exact xentails_of_eq (by ac_rfl)
  · simp only [CSpec.Pre, CSpec.Entry, EntryOf, CtlIn, esp, lift_sep]
    refine xentails_trans (xentails_of_eq ?_) (xentails_trans
      (xsep_mono (xentails_refl ((↑ₓ(codePt pc.toNat (encCallR r)) ∗ₓ Cr) ∗ₓ ↑ₓ(ripPt p) ∗ₓ
        ↑ₓ(regPt .rsp (s - 8#64)) ∗ₓ ↑ₓflagsAny ∗ₓ
        ↑ₓ(wordPt (s.toNat - 8) (nextPc pc (encCallR r))) ∗ₓ
        ↑ₓ(blockAny (s.toNat - 8 - S.stack x) (S.stack x)))) hho) (xentails_of_eq ?_))
    · ac_rfl
    · ac_rfl
  · simp only [CSpec.Post, CSpec.Exit, ExitOf, CtlOut, esp, eback]
    simp only [xsep_xsexists, xsexists_sep]
    refine xsexists_mono fun rb => xentails_of_eq ?_
    simp only [lift_sep]
    ac_rfl

end Silmaril.Proofs.X86.SepCSpec
