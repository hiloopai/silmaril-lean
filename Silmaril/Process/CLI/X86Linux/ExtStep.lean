module

public import Silmaril.Process.CLI.X86Linux

/-! # Adapting successful extended x86 steps

The Linux wrapper recognizes `syscall` before the extended decoder. These
results show that recognition cannot intercept an actual extended-machine
retirement or return. A function's final `RET` remains a silent retirement of
the process ISA; it does not exit the process.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.X86 (MState Word Byte maxInstrLength)
open Silmaril.Process (Memory)

/-- No suffix makes the Linux syscall opcode an extended-model instruction. -/
theorem ext_decode_syscall_prefix (more : List Byte) :
    X86.Ext.decode (syscallBytes ++ more) = none := by
  rfl

/-- A successfully decoded extended instruction cannot be intercepted by the
Linux wrapper's earlier recognition of the two syscall bytes. -/
theorem not_syscall_of_ext_fetch {memory : Memory} {address : Nat}
    {instr : X86.Ext.Instr} {length : Nat}
    (fetched : X86.Ext.fetch memory address = .decoded instr length) :
    memory.fetchBytes address 2 ≠ some syscallBytes := by
  intro syscall
  obtain ⟨more, window⟩ := X86.fetchBytes_prefix_fetchWindow syscall
    (limit := maxInstrLength) (by decide)
  unfold X86.Ext.fetch at fetched
  rw [← window, ext_decode_syscall_prefix] at fetched
  change X86.Ext.Fetch.undecodable = .decoded instr length at fetched
  cases fetched

/-- Successful extended-machine steps are Linux ISA retirements with the same
core and memory. This includes the final `RET` of an extended-machine call.
The decoded byte length is retained exactly. -/
theorem step_retired_of_ext_success {exit : Word} {initial final : MState}
    (success : X86.Ext.step exit initial = .retired final ∨
      X86.Ext.step exit initial = .returned final) :
    step initial.core initial.memory = .retired final.core final.memory := by
  cases fetched : X86.Ext.fetch initial.memory initial.core.rip.toNat with
  | undecodable => simp [X86.Ext.step, fetched] at success
  | truncated => simp [X86.Ext.step, fetched] at success
  | decoded instr length =>
    have noSyscall := not_syscall_of_ext_fetch fetched
    have exactLength := X86.Ext.fetch_length fetched
    simp only [step, noSyscall, ite_false, fetched, exactLength]
    cases executed : X86.Ext.exec instr initial.core initial.memory with
    | ok core memory =>
      simp only [X86.Ext.step, fetched, executed] at success
      split at success <;> rcases success with success | success <;>
        cases success <;> rfl
    | dataFault => simp [X86.Ext.step, fetched, executed] at success
    | divideError => simp [X86.Ext.step, fetched, executed] at success
    | undefinedCondition c => simp [X86.Ext.step, fetched, executed] at success
    | trap => simp [X86.Ext.step, fetched, executed] at success

/-- An actual extended retirement is a silent Linux ISA retirement. -/
theorem step_of_ext_retired {exit : Word} {initial final : MState}
    (retired : X86.Ext.step exit initial = .retired final) :
    step initial.core initial.memory = .retired final.core final.memory :=
  step_retired_of_ext_success (.inl retired)

/-- An actual extended return executes its `RET` as a Linux ISA retirement. -/
theorem step_of_ext_returned {exit : Word} {initial final : MState}
    (returned : X86.Ext.step exit initial = .returned final) :
    step initial.core initial.memory = .retired final.core final.memory :=
  step_retired_of_ext_success (.inr returned)

end Silmaril.Process.CLI.X86Linux
