module

public import Silmaril.Apps.Sha256sum.X86Sys.Silent
public import Silmaril.Process.CLI.X86Linux.Silent

/-! # Concrete return-to-exit controls for the silent execution adapter

The program returns through a one-byte `RET` at address 0 to an exit syscall
at address 32. The return itself is one internal step; the continuation exits
with status 7. Replacing the return by `syscall`, or marking the state faulted,
prevents that internal step. All proofs are checked in the instruction model.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys.SilentControls

open Silmaril.X86 (MState Word)
open Silmaril.Process (Byte Memory)
open Silmaril.Apps.Sha256sum.Sys

/-- Separate mappings for the callee, its return slot, and its continuation. -/
def memory (code : List Byte) : Memory where
  regions := [⟨0, code.length, ⟨true, false, true⟩⟩,
    ⟨16, 8, ⟨true, true, false⟩⟩, ⟨32, 2, ⟨true, false, true⟩⟩]
  bytes := Memory.install
    (Memory.install (Memory.install ∅ 0 code) 16 [32, 0, 0, 0, 0, 0, 0, 0])
    32 Process.CLI.X86Linux.syscallBytes

def core : Core where
  regs := fun reg => if reg = .rsp then 16 else if reg = .rax then 60
    else if reg = .rdi then 7 else 0
  rip := 0
  flags := ⟨none, none, none, none, none, none⟩

def afterRet : Core := { core.write .rsp 24 with rip := 32 }

def initial : XState := ⟨core, memory [0xC3], 64, 64, false⟩
def final : MState := ⟨afterRet, initial.memory⟩

private theorem code_installed (code : List Byte) (short : code.length ≤ 16)
    (index : Nat) (bound : index < code.length) :
    (memory code).bytes.get? (0 + index) = some code[index] := by
  change (Memory.install
    (Memory.install (Memory.install ∅ 0 code) 16 [32, 0, 0, 0, 0, 0, 0, 0])
    32 Process.CLI.X86Linux.syscallBytes).get? (0 + index) = some code[index]
  rw [Memory.install_outside _ _ _ _ (Or.inl (by omega)),
    Memory.install_outside _ _ _ _ (Or.inl (by omega))]
  exact Memory.install_get _ 0 code index bound

theorem ret_fetch : initial.memory.fetchBytes 0 1 = some [0xC3] := by
  apply Memory.readWith_eq initial.memory .execute 0 [0xC3] (by decide)
  exact code_installed [0xC3] (by decide)

theorem continuation_fetch : initial.memory.fetchBytes 32 2 =
    some Process.CLI.X86Linux.syscallBytes := by
  apply Memory.readWith_eq initial.memory .execute 32
    Process.CLI.X86Linux.syscallBytes (by decide)
  exact Memory.install_get _ 32 Process.CLI.X86Linux.syscallBytes

/-- An actual fetched RET reads the stack slot and advances RSP by eight. -/
theorem ext_return : X86.Ext.step 32 (toExtState initial) = .returned final := by
  rw [X86.Ext.step_of_fetch ret_fetch
    (by decide : X86.Ext.decode [0xC3] = some (.ret, 1))]
  have popped := X86.popWord_of_readBytes
    (s := initial.core) (memory := initial.memory) (value := 32)
    (by
      have encoded : Machine.LittleEndian.encodeWords [32] =
          [32, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
      rw [encoded]
      apply Memory.readWith_eq initial.memory .read 16 [32, 0, 0, 0, 0, 0, 0, 0]
        (by decide)
      intro index bound
      change (Memory.install
        (Memory.install (Memory.install ∅ 0 [0xC3]) 16 [32, 0, 0, 0, 0, 0, 0, 0])
        32 Process.CLI.X86Linux.syscallBytes).get? (16 + index) = _
      have bound' : index < 8 := by simpa using bound
      rw [Memory.install_outside _ _ _ _ (Or.inl (by omega))]
      exact Memory.install_get _ 16 [32, 0, 0, 0, 0, 0, 0, 0] index bound)
  simp only [toExtState, X86.Ext.exec, popped]
  rfl

theorem ext_returns : X86.Ext.Returns 32 (toExtState initial) final :=
  ⟨0, toExtState initial, rfl, ext_return⟩

/-- The completed zero-retirement callee still executes its final RET. -/
theorem one_tau (r11Of : Core → Word) :
    TauRun r11Of 1 initial (withExtState initial final) :=
  .single (step_of_ext_returned rfl ext_return)

theorem return_target : final.core.rip = 32 := rfl
theorem return_stack_pointer : final.core.read .rsp = 24 := rfl

private theorem linux_exit : Process.CLI.X86Linux.step afterRet initial.memory =
    .syscall { afterRet with rip := 34 } := by
  simp only [Process.CLI.X86Linux.step, show afterRet.rip.toNat = 32 from rfl,
    continuation_fetch, ite_true]
  rfl

theorem exit_step (r11Of : Core → Word) :
    (x86Machine r11Of).step (withExtState initial final) = .exit 7 := by
  have trapped : Process.CLI.X86Linux.step (withExtState initial final).core
      (withExtState initial final).memory = .syscall { afterRet with rip := 34 } := linux_exit
  have decoded : decode { afterRet with rip := 34 } initial.memory = some (.exit 7) := by
    rfl
  change step r11Of (withExtState initial final) = .exit 7
  unfold step
  rw [show (withExtState initial final).faulted = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [trapped]
  simp only [show (withExtState initial final).memory = initial.memory from rfl, decoded]

/-- The silent segment composes with an actual exit for any syscall policy,
environment and kernel state, without introducing an event. -/
theorem completed (r11Of : Core → Word) (E : Env) (k : KState) :
    Exec (x86Machine r11Of) E initial k [] 7 := by
  apply (one_tau r11Of).exec_iff.mpr
  exact .exit (exit_step r11Of)

def syscallInitial : XState := { initial with memory := memory [0x0F, 0x05] }

theorem mutation_syscall_fetch : syscallInitial.memory.fetchBytes 0 2 =
    some Process.CLI.X86Linux.syscallBytes := by
  apply Memory.readWith_eq syscallInitial.memory .execute 0
    Process.CLI.X86Linux.syscallBytes (by decide)
  exact code_installed [0x0F, 0x05] (by decide)

/-- The opcode mutation exits immediately instead of silently returning. -/
theorem mutation_exit (r11Of : Core → Word) :
    (x86Machine r11Of).step syscallInitial = .exit 7 := by
  have trapped : Process.CLI.X86Linux.step syscallInitial.core syscallInitial.memory =
      .syscall { core with rip := 2 } := by
    simp only [Process.CLI.X86Linux.step,
      show syscallInitial.core.rip.toNat = 0 from rfl, mutation_syscall_fetch, ite_true]
    rfl
  have decoded : decode { core with rip := 2 } syscallInitial.memory = some (.exit 7) := by
    rfl
  change step r11Of syscallInitial = .exit 7
  unfold step
  rw [show syscallInitial.faulted = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [trapped]
  simp only [decoded]

theorem mutation_not_tau (r11Of : Core → Word) (next : XState) :
    (x86Machine r11Of).step syscallInitial ≠ .tau next := by
  rw [mutation_exit]
  intro impossible
  cases impossible

theorem mutation_no_one_tau (r11Of : Core → Word) (next : XState) :
    ¬TauRun r11Of 1 syscallInitial next := by
  intro run
  cases run with
  | cons head _ => exact mutation_not_tau r11Of _ head

def faultedInitial : XState := { initial with faulted := true }

theorem faulted_stuck (r11Of : Core → Word) :
    (x86Machine r11Of).step faultedInitial = .stuck := rfl

theorem faulted_not_tau (r11Of : Core → Word) (next : XState) :
    (x86Machine r11Of).step faultedInitial ≠ .tau next := by
  rw [faulted_stuck]
  intro impossible
  cases impossible

theorem faulted_no_one_tau (r11Of : Core → Word) (next : XState) :
    ¬TauRun r11Of 1 faultedInitial next := by
  intro run
  cases run with
  | cons head _ => exact faulted_not_tau r11Of _ head

/-- The generic CLI adapter also gives an empty trace and preserves the entire
Linux environment, including every descriptor and its exit flag. -/
theorem cli_silent (s : Process.Syscall.State) (running : s.exited = none)
    (memory_eq : s.memory = initial.memory) :
    Process.CLI.Proc.Runs Process.CLI.X86Linux.isa Process.CLI.Env.linux
      ⟨initial.core, s⟩ [] ⟨final.core, s⟩ := by
  have run := Process.CLI.X86Linux.runs_of_ext_returns Process.CLI.Env.linux_memoryLens
    (initial := toExtState initial) (final := final) running memory_eq ext_returns
  have unchanged : Process.CLI.Env.linux.withMemory s final.memory = s := by
    rw [show final.memory = Process.CLI.Env.linux.memory s from memory_eq.symm]
    exact Process.CLI.Env.linux_memoryLens.withMemory_self s
  rwa [unchanged] at run

end Silmaril.Apps.Sha256sum.X86Sys.SilentControls
