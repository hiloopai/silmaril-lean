module

public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs
/-! # Runtime code for an integer expression of the entry argument count -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgcLink

open Silmaril.Machine
open Spec Backend
open IntExpr (Term)

/-- Copy the actual entry argc to the expression's variable register, then compute it. -/
def ops (t : Term) : List (Lir.Op Mir.Reg) :=
  [.move 3 1] ++ t.ops 4 ++ [.move 0 4]

def link (t : Term) : Mir.Linked := OpsLink.link (ops t) 0

theorem ops_exec {n : Int} {t : Term} (ok : t.Ok n) (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory)
    (h1 : fr.get 1 = some (BitVec.ofInt 64 n)) :
    ∃ fr', Lir.execOps (ops t) fr mem = some (fr', mem) ∧
      fr'.get 0 = some (BitVec.ofInt 64 (t.val n)) := by
  obtain ⟨fr₁, w, hx, hg, hv, -⟩ := Term.ops_exec (n := n) t 4 (by decide) (fr.set 3 (BitVec.ofInt 64 n))
    mem (by simp)
  rw [hv ok] at hg
  refine ⟨fr₁.set 0 (BitVec.ofInt 64 (t.val n)), ?_, by simp⟩
  simp [ops, Lir.execOps_append, Lir.execOps, Lir.Op.exec, h1, hx, hg]

/-- Every observation is exhaustion or the computed argc expression's exit status. -/
theorem link_sound {t : Term} {args : List String} (ok : t.Ok args.length)
    {a : Artifact} (h : artifactOf (link t) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit ((BitVec.ofInt 64 (t.val args.length)).toNat % 256) [] := by
  have himg : a.image = .empty := by
    rw [(ConstLink.artifact_layout h).2.2]; rfl
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link, OpsLink.link_funcs] at hstart
  cases hstart
  obtain ⟨fr, hx, hr⟩ := ops_exec ok
    ((Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2 (BitVec.ofNat 64 a.argBase))
    (a.lmem args) (by simp)
  rcases ho with ho | hstuck | ⟨b, hb, hobs⟩
  · exact .inl ho
  · cases OpsLink.link_beh hx hr hs hstuck
  · right
    cases OpsLink.link_beh hx hr hs hb
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) :
        memWord (a.lmem args) addr = 0 := by
      apply ConstLink.memWord_zero
      intro i
      apply ConstLink.lmem_bytes_empty himg
      rw [(ConstLink.artifact_layout h).1]
      have := i.isLt
      omega
    rw [hk _ rfl, ConstLink.stdoutOf_zero (hzero (ctlAddr + 24) (by decide))
      (hzero (ctlAddr + 48) (by decide)) hout]

end Silmaril.Compile.Core.Verified.ArgcLink
