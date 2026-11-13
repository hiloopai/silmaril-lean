module

public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Open.Thms
/-!
# Function contracts on the open machine from returning runs

`ofReturns`: a callee proved with an `Ext8.Returns` (or `X86.Ext.Returns`) run to the
return address its entry state holds is a `FnContract Open.isa` (`Open.returns_open`).
(`ofDecompiled` moved to `FnContract/SystemV`; `retOf_of_readBytes` and `abiEntry_of` are
`Silmaril.X86.FnContract`'s.)
-/

@[expose] public section

namespace Silmaril.Proofs.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86
open Silmaril.X86.FnContract

theorem total_of_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext8.Returns (FnContract.retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    S.Total Open.isa := by
  intro m _ ha he
  obtain ⟨fin, hret, hp⟩ := h m ha he
  obtain ⟨hr, hrip⟩ := Open.returns_open hret
  exact ⟨fin, hr, rfl, ⟨hrip, hp.stack, hp.calleeSaved⟩, hp.frame, hp.post⟩

theorem total_of_ext_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext.Returns (FnContract.retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    S.Total Open.isa :=
  total_of_returns S fun m ha he => by
    obtain ⟨fin, hret, hp⟩ := h m ha he
    exact ⟨fin, Silmaril.X86.Ext8.returns_of_ext hret, hp⟩

end Silmaril.Proofs.X86.FnContract
