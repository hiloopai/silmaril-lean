module

public import Silmaril.Machine.X86.Ladder.LibMini.Defs
public import Silmaril.Machine.X86.FnContract.SystemV.Thms
public import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Memcpy
public import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Memset
public import Silmaril.Proofs.Machine.X86.Ladder.LibMini.Strlen

/-!
# libmini contracts as integer System V `Realizes` certificates

Each state-level stencil contract goes through `FnContract.toRealizes` with the C signature
(`sigCopy`, `sigFill`, `sigScan`); the domain is the contract's entry condition. The argument
words are read off `SysV.Entry` (`argWord`); `memset`'s `int` argument is only its low 32 bits,
of which the fill byte is the low 8. `strlen`'s result is not a function of its argument, so its
certificate is indexed by the string length `k`, which the domain fixes.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Ladder.LibMini

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86 Silmaril.Machine.X86.Stencils.ByteLoop Silmaril.Machine.X86.Ladder.LibMini

/-- The word of a register argument. -/
theorem argWord {m : MState} {i : Nat} {r : Reg} {word : Word}
    (hr : Silmaril.X86.sysv64.intArgRegs[i]? = some r)
    (h : Silmaril.C.Api.SysV.ArgumentWord m i word) : m.core.read r = word := by
  simpa only [Silmaril.C.Api.SysV.ArgumentWord, hr] using h

theorem memcpy_realizes (entry : Word) :
    Silmaril.Machine.SystemV.Realizes sigCopy firstResult blockWrites
      (fun _ call => (copyContract memcpyCode entry).entry call.initial)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨copyContract memcpyCode entry, memcpy_total entry⟩ sigCopy
    firstResult blockWrites _ (fun _ _ _ d => d) ?_ ?_
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons d (.cons _ (.cons _ .nil)), admitted, hpost =>
      obtain ⟨w, hw, he⟩ := admitted.arguments.1
      show final.core.read .rax = d
      rw [hpost.1, argWord rfl hw]; exact he
  · intro arguments call a admitted _ ha
    match arguments, admitted, ha with
    | .cons d (.cons _ (.cons n .nil)), admitted, ha =>
      obtain ⟨w, hw, he⟩ := admitted.arguments.1
      obtain ⟨w2, hw2, he2⟩ := admitted.arguments.2.2.1
      have e0 : arg0 call.initial = d.toNat := by
        simp only [arg0]; rw [argWord rfl hw]; exact congrArg BitVec.toNat he
      have e2 : arg2 call.initial = n.toNat := by
        simp only [arg2]; rw [argWord rfl hw2]; exact congrArg BitVec.toNat he2
      show d.toNat ≤ a ∧ a < d.toNat + n.toNat
      rw [← e0, ← e2]; exact ha

theorem memset_realizes (entry : Word) :
    Silmaril.Machine.SystemV.Realizes sigFill firstResult blockWrites
      (fun _ call => (fillContract memsetCode entry).entry call.initial)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨fillContract memsetCode entry, memset_total entry⟩ sigFill
    firstResult blockWrites _ (fun _ _ _ d => d) ?_ ?_
  · intro arguments call final admitted _ hpost
    match arguments, admitted, hpost with
    | .cons d (.cons _ (.cons _ .nil)), admitted, hpost =>
      obtain ⟨w, hw, he⟩ := admitted.arguments.1
      show final.core.read .rax = d
      rw [hpost.1, argWord rfl hw]; exact he
  · intro arguments call a admitted _ ha
    match arguments, admitted, ha with
    | .cons d (.cons _ (.cons n .nil)), admitted, ha =>
      obtain ⟨w, hw, he⟩ := admitted.arguments.1
      obtain ⟨w2, hw2, he2⟩ := admitted.arguments.2.2.1
      have e0 : arg0 call.initial = d.toNat := by
        simp only [arg0]; rw [argWord rfl hw]; exact congrArg BitVec.toNat he
      have e2 : arg2 call.initial = n.toNat := by
        simp only [arg2]; rw [argWord rfl hw2]; exact congrArg BitVec.toNat he2
      show d.toNat ≤ a ∧ a < d.toNat + n.toNat
      rw [← e0, ← e2]; exact ha

/-- `strlen`, for strings of length `k`. -/
theorem strlen_realizes (entry : Word) (k : Nat) :
    Silmaril.Machine.SystemV.Realizes sigScan (fun _ => BitVec.ofNat 64 k) (fun _ _ => False)
      (fun _ call => (scanContract strlenCode entry).entry call.initial ∧
        CStr call.initial.memory (arg0 call.initial) k)
      (fun call final => Reaches Open.step call.initial final) := by
  refine FnContract.toRealizes ⟨scanContract strlenCode entry, strlen_total entry⟩ sigScan
    _ _ _ (fun _ _ _ d => d.1) ?_ ?_
  · intro arguments call final _ d hpost
    exact hpost.1 k d.2
  · intro _ _ _ _ _ ha; exact ha.elim

end Silmaril.Proofs.Machine.X86.Ladder.LibMini
