module

public import Silmaril.X86.Sep.Demo.Defs
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Proofs.X86.Sep.Algebra
/-!
# Proofs: the addition leaf and its caller, through the call rule

`leaf_sat` turns `Silmaril.X86.Leaf.leaf_returns` (a run of the base machine) into a spec, by
the proved embeddings into `X86.Ext` and the open machine. `caller_sat` then proves the caller
`call leaf; ret` **without** `Leaf.caller_returns`: the `call` is `call_rule` with `leaf_sat`,
the final `ret` is `ret_step`, glued by the frame rule and sequencing.

The leaf's caller calls it with `rsp ≡ 8 (mod 16)` (it has no frame), so the inner call
violates the System V alignment rule: both specs are stated with `SatWith (fun _ => True)`,
which `leaf_returns` supports since the base model has no alignment checks.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepDemo

open Silmaril.X86 (State MState Word Byte Reg Insn sysv64)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Demo
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

theorem le_left {a b s : Frag} (h : Le (union a b) s) : Le a s :=
  Silmaril.Proofs.X86.Sep.Frag.Le.trans
    (Silmaril.Proofs.X86.Sep.Frag.le_union_left a b) h

theorem le_right {a b s : Frag} (hd : Disjoint a b) (h : Le (union a b) s) : Le b s :=
  Silmaril.Proofs.X86.Sep.Frag.Le.trans
    (Silmaril.Proofs.X86.Sep.Frag.le_union_right hd) h

theorem ne_rax_of_calleeSaved {r : Reg} (hr : r ∈ sysv64.calleeSaved) : r ≠ .rax := by
  rintro rfl; exact absurd hr (by decide)

theorem ne_rsp_of_calleeSaved {r : Reg} (hr : r ∈ sysv64.calleeSaved) : r ≠ .rsp := by
  rintro rfl; exact absurd hr (by decide)

/-- **The addition leaf meets `leafSpec`**, from `Leaf.leaf_returns`. -/
theorem leaf_sat (leaf : Word) :
    leafSpec.SatWith Silmaril.X86.Open.isa (fun _ => True)
      (codePt leaf.toNat Silmaril.X86.Leaf.bytes) leaf := by
  apply FnSpec.satWith_of_runs
  intro x sp ret m hc ht hu _ _ _ hcP htP huP hd1 hd2 hl
  have hlc := le_left hl
  have hlt := le_left (le_right hd1 hl)
  have erip := FnSpec.sysVEntry_rip htP hlt
  have ersp := FnSpec.sysVEntry_rsp htP hlt
  have eret := FnSpec.sysVEntry_ret htP hlt
  have ea := FnSpec.sysVEntry_args htP hlt 0 (by decide) (by simp [leafSpec])
  have eb := FnSpec.sysVEntry_args htP hlt 1 (by decide) (by simp [leafSpec])
  simp only [argRegs, leafSpec, List.getElem_cons_zero, List.getElem_cons_succ] at ea eb
  have entry : Silmaril.X86.Leaf.Entry m leaf ret :=
    ⟨erip, fetchBytes_of_codePt (by decide) hcP hlc, by rw [ersp]; exact eret⟩
  obtain ⟨final, hret, hrip, hrax, -, hrsp, -, hother, hmem⟩ :=
    Silmaril.X86.Leaf.leaf_returns entry
  refine ⟨final, (Silmaril.X86.Open.returns_open_ext
      (Silmaril.X86.Ext.returns_of_x86 hret)).1, hrip, by rw [hrsp, ersp],
    fun r hr => hother r (ne_rax_of_calleeSaved hr) (ne_rsp_of_calleeSaved hr), ?_, ?_⟩
  · show m.memory.WritesWithin final.memory _
    rw [hmem]; exact Silmaril.Process.Memory.WritesWithin.refl _ _
  · have hu0 : hu = Frag.empty := huP
    subst hu0
    rw [Silmaril.Proofs.X86.Sep.Frag.reval_empty]
    exact ⟨rfl, by rw [hrax, ea, eb]⟩

theorem callerBytes_split (caller : Nat) (rel : BitVec 32) :
    codePt caller (Silmaril.X86.Leaf.callerBytes rel) =
      (codePt caller (Insn.encode (.call rel)) ∗ codePt (caller + 5) (Insn.encode .ret)) := by
  unfold codePt
  rw [Silmaril.X86.Leaf.callerBytes, bytesAt_append]
  rfl

/-- **The caller meets `callerSpec`**, by the call rule applied to `leaf_sat`. No use of
`Leaf.caller_returns`. -/
theorem caller_sat {caller leaf : Word} {rel : BitVec 32}
    (hf : caller + 5#64 + rel.signExtend 64 = leaf) (hfit : caller.toNat + 6 ≤ 2 ^ 64) :
    callerSpec.SatWith Silmaril.X86.Open.isa (fun _ => True)
      (codePt caller.toNat (Silmaril.X86.Leaf.callerBytes rel) ∗
        codePt leaf.toNat Silmaril.X86.Leaf.bytes) caller := by
  intro x sp ret _ hst
  simp only [callerSpec] at hst
  have hcall := call_rule (Silmaril.X86.SegVC.Isa.Extends.refl _) (A := fun _ => True) (S := leafSpec) (s := sp) x (leaf_sat leaf) hf trivial
    (by simp only [leafSpec]; omega)
  have e5 : (caller + 5#64).toNat = caller.toNat + 5 := by bv_omega
  have hret := ret_step (Silmaril.X86.SegVC.Isa.Extends.refl _) (caller + 5#64) sp ret
  rw [e5] at hret
  unfold SPEC at hcall ⊢
  simp only [FnSpec.SysVPre, FnSpec.SysVPost, FnSpec.SysVEntry, FnSpec.SysVExit, callerSpec,
    leafSpec, Nat.sub_zero, Nat.zero_add] at hcall ⊢
  rw [callerBytes_split]
  have step1 := Triple.frame hcall
    (codePt (caller.toNat + 5) (Insn.encode .ret) ∗ wordPt sp.toNat ret)
  refine Triple.trans (Triple.pre (entails_of_eq ?_) step1) ?_
  · ac_rfl
  rw [sep_sexists, sexists_sep]
  refine Triple.sexists fun v => ?_
  have step2 := Triple.frame hret
    (codePt caller.toNat (Insn.encode (.call rel)) ∗ codePt leaf.toNat Silmaril.X86.Leaf.bytes ∗
      SysVRet v ∗ flagsAny ∗ blockAny (sp.toNat - 8) 8 ∗ ⌜v = x.1 + x.2⌝)
  refine Triple.conseq (entails_of_eq ?_) step2 ?_
  · ac_rfl
  rw [sep_sexists]
  refine sexists_intro v ?_
  have e16 : blockAny (sp.toNat - 8) (8 + 8) =
      (blockAny (sp.toNat - 8) 8 ∗ blockAny sp.toNat 8) := by
    rw [blockAny_add, show sp.toNat - 8 + 8 = sp.toNat by omega]
  rw [e16]
  let Rest : SProp := codePt caller.toNat (Insn.encode (.call rel)) ∗
    codePt (caller.toNat + 5) (Insn.encode .ret) ∗ codePt leaf.toNat Silmaril.X86.Leaf.bytes ∗
    ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ SysVRet v ∗ flagsAny ∗ blockAny (sp.toNat - 8) 8 ∗
    ⌜v = (show Word × Word from x).1 + (show Word × Word from x).2⌝
  refine entails_trans (entails_of_eq (?_ : _ = (wordPt sp.toNat ret ∗ Rest)))
    (entails_trans (sep_mono_left Rest (wordPt_blockAny sp.toNat ret)) (entails_of_eq ?_))
  · simp only [Rest]; ac_rfl
  · simp only [Rest]; ac_rfl

/-- **The caller returns**, re-derived on the open machine from `leaf_sat` and the call rule:
from any state of which the caller's precondition holds, the open machine returns to `ret`
with `rax = a + b`, `rsp` popped, and every location outside the precondition's fragment
(in particular every callee-saved register) unchanged. -/
theorem caller_returns_open {caller leaf : Word} {rel : BitVec 32}
    (hf : caller + 5#64 + rel.signExtend 64 = leaf) (hfit : caller.toNat + 6 ≤ 2 ^ 64)
    {a b sp ret : Word} (hst : 8 ≤ sp.toNat) {m : MState} {h : Frag}
    (hpre : ((codePt caller.toNat (Silmaril.X86.Leaf.callerBytes rel) ∗
        codePt leaf.toNat Silmaril.X86.Leaf.bytes) ∗ callerSpec.SysVPre (a, b) caller sp ret) h)
    (hl : Le h (toFrag m)) :
    ∃ fin, Reaches Silmaril.X86.Open.step m fin ∧ fin.core.rip = ret ∧
      fin.core.read .rax = a + b ∧ fin.core.read .rsp = sp + 8#64 ∧
      ∀ l, h l = none → toFrag fin l = toFrag m l := by
  obtain ⟨fin, h', hrun, hq, hl', hsame⟩ :=
    Triple.run (caller_sat hf hfit (a, b) sp ret trivial hst) trivial hpre hl
  obtain ⟨v, erip, ersp, erax, u, hu, -⟩ := FnSpec.sysVPost_le hq hl'
  have hv : v = a + b := hu.2
  exact ⟨fin, hrun, erip, by rw [erax, hv], ersp, hsame⟩

end Silmaril.Proofs.X86.SepDemo
