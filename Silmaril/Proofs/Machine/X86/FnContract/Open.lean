module

public import Silmaril.Machine.X86.FnContract.Defs

/-!
# Function contracts on the open machine from returning runs

`ofReturns`: a callee proved with an `Ext8.Returns` (or `X86.Ext.Returns`) run to the
return address its entry state holds is a `FnContract Open.isa` (`Open.returns_open`).
`retOf_of_readBytes`, `abiEntry_of`: the return address and the ABI entry obligations from an
encoded stack slot. (`ofDecompiled` moved to `FnContract/SystemV`.)
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.FnContract

theorem total_of_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext8.Returns (Open.retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    S.Total Open.isa := by
  intro m _ ha he
  obtain ⟨fin, hret, hp⟩ := h m ha he
  obtain ⟨hr, hrip⟩ := Open.returns_open hret
  exact ⟨fin, hr, rfl, ⟨hrip, hp.stack, hp.calleeSaved⟩, hp.frame, hp.post⟩

theorem total_of_ext_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Silmaril.X86.Ext.Returns (Open.retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    S.Total Open.isa :=
  total_of_returns S fun m ha he => by
    obtain ⟨fin, hret, hp⟩ := h m ha he
    exact ⟨fin, Silmaril.X86.Ext8.returns_of_ext hret, hp⟩

/-- The return address read from a stack slot holding its encoding. -/
theorem retOf_of_readBytes {core : State} {memory : Memory} {x : Word}
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) :
    Open.retOf core memory = x := by
  simp [Open.retOf, h, Silmaril.X86.wordOfBytes?_encodeWords]

/-- The ABI entry obligations from an aligned stack and an encoded return address. -/
theorem abiEntry_of {core : State} {memory : Memory} {x : Word}
    (aligned : (core.read .rsp).toNat % 16 = 8)
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) :
    AbiEntry core memory :=
  ⟨aligned, by rw [retOf_of_readBytes h]; exact h⟩

end Silmaril.Proofs.Machine.X86.FnContract
