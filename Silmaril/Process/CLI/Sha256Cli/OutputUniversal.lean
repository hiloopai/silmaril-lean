module

public import Silmaril.Process.CLI.Sha256Cli.OutputAdvance
public import Silmaril.Process.CLI.X86Linux.SyscallInversion
public import Silmaril.Process.CLI.X86Linux.SilentTransport

/-! # Universal completed-result correctness of the actual output loop

The theorem covers every finite execution that exits0 from the canonical
output cutpoint. Short/zero/error replies and arbitrary R11 remain admitted.
There is no assertion that a syscall returns or that a run terminates.

`SilentTransport` is the explicit external PR#3052 dependency, pinned to
f69056ce06858f0e72bc8c6ae53c51603fd11282; no dependency source is vendored.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.OutputUniversal

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open OutputTransfer OutputLoop

set_option maxRecDepth 10000

theorem instruction (c : Core) (off : Fin 65) (memory : Memory)
    (ready : Ready c off) (intact : Output.Intact memory) :
    X86Linux.step c memory = .syscall (trapped c) := by
  have actual : X86Linux.step c memory = Binary.i_4002a9.denote c memory :=
    step_of_entry Binary.ok_4002a9.1 (by simp [ready.pc, Binary.i_4002a9])
    (intact Binary.i_4002a9 (by simp [Binary.transcript]))
  simpa [Entry.denote, Binary.i_4002a9, trapped, ready.pc] using actual

theorem requested (c : Core) (off : Fin 65) (ready : Ready c off) :
    X86Linux.request (trapped c) = some (writeRequest off) := by
  have ax : c.regs .rax = 1 := ready.number
  have di : c.regs .rdi = 1 := ready.fd
  have si : c.regs .rsi = BitVec.ofNat 64 (address off) := ready.pointer
  have dx : c.regs .rdx = BitVec.ofNat 64 (remaining off) := ready.size
  have a : address off < 2 ^ 64 := by have := off.isLt; dsimp [address]; omega
  have n : remaining off < 2 ^ 64 := by dsimp [remaining]; omega
  simp [trapped, X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber,
    X86.State.read, ax, di, si, dx, writeRequest, BitVec.toNat_ofNat]
  exact ⟨a, n⟩

theorem write_running {before after : Syscall.State} {off : Fin 65} {event : Event}
    {result : Result}
    (effect : Syscall.Step before (writeRequest off) event (.returned result) after) :
    after.exited = none := by
  change Syscall.Step before (.write 1 (address off) (remaining off)) event (.returned result) after at effect
  cases effect <;> assumption

theorem output_exit {message : List Byte} {events : List Event} {off : Nat}
    (h : Driver.OutputInv message events off) (status : Nat) :
    Driver.OutputInv message (events ++ [.exit status]) off := by
  refine ⟨?_, List.mem_append_left _ h.eof, ?_, ?_, h.bound⟩
  · simpa [stdinRead, readOn_append, readOn] using h.input
  · intro fd bytes member
    exact h.only fd bytes (by simpa using member)
  · simpa [stdout, writtenOn_append, writtenOn] using h.output

theorem failed_exit (c : Core) (off : Fin 65) (result : Result) (flags : Word)
    (s : Syscall.State) (ready : Ready c off) (intact : Output.Intact s.memory)
    (running : s.exited = none) {events : List Event} {final : Output.PS}
    (run : Proc.Runs X86Linux.isa Env.linux ⟨failure c result flags, s⟩ events final)
    (stop : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) : False := by
  have actual : X86Linux.step (failure c result flags) s.memory =
      Binary.i_4002b5.denote (failure c result flags) s.memory :=
    step_of_entry Binary.ok_4002b5.1 rfl
    (intact Binary.i_4002b5 (by simp [Binary.transcript]))
  have trap : X86Linux.step (failure c result flags) s.memory =
      .syscall { failure c result flags with rip := 0x4002b7 } := by
    simpa [Entry.denote, Binary.i_4002b5, OutputLoop.failure] using actual
  have fd : c.regs .rdi = 1 := ready.fd
  have requestExit : X86Linux.request { failure c result flags with rip := 0x4002b7 } =
      some (.exit 1) := by
    simp [X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber, X86Linux.exitNumber,
      OutputLoop.failure, rejected, tested, returned, trapped,
      X86.State.read, X86.State.write, Machine.RegisterFile.write, fd]
  have contradiction := (X86Linux.completed_exit running trap requestExit run stop).2
  contradiction

theorem successful_exit (c : Core) (off : Fin 65) (count : Nat) (flags : Word)
    (s : Syscall.State) (intact : Output.Intact s.memory) (running : s.exited = none)
    {events : List Event} {final : Output.PS}
    (run : Proc.Runs X86Linux.isa Env.linux ⟨success c off count flags, s⟩ events final)
    (stop : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) : events = [.exit 0] := by
  have actual : X86Linux.step (success c off count flags) s.memory =
      Binary.i_4002d1.denote (success c off count flags) s.memory :=
    step_of_entry Binary.ok_4002d1.1 rfl
    (intact Binary.i_4002d1 (by simp [Binary.transcript]))
  have trap : X86Linux.step (success c off count flags) s.memory =
      .syscall { success c off count flags with rip := 0x4002d3 } := by
    simpa [Entry.denote, Binary.i_4002d1, success] using actual
  have requestExit : X86Linux.request { success c off count flags with rip := 0x4002d3 } =
      some (.exit 0) := by
    simp [X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber, X86Linux.exitNumber,
      success, successNumber, X86.State.read, X86.State.write, Machine.RegisterFile.write]
  exact (X86Linux.completed_exit running trap requestExit run stop).1

/-- Every actual finite exit0 execution from any unfinished canonical write
cutpoint has consumed complete input and emitted exactly digest/newline.
The well-founded proof follows strictly increasing positive-write offsets;
zero/error replies are rejected by the actual exit1 continuation. -/
theorem completed {input : ProcInput} {message : List Byte} {prior events : List Event}
    {final : Output.PS} (c : Core) (s : Syscall.State) (off : Fin 65)
    (ready : Ready c off) (intact : Output.Intact s.memory) (running : s.exited = none)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message prior off.val) (finite : input.stdin = .ofList message)
    (run : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final)
    (stop : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) :
    Sha256.Success input (prior ++ events) := by
  generalize fuelEq : remaining off = fuel
  induction fuel using Nat.strong_induction_on generalizing c s off prior events final with
  | h fuel ih =>
    have actual := instruction c off s.memory ready intact
    have request := requested c off ready
    cases run with
    | refl => exact False.elim (not_stop_of_syscall running actual request stop)
    | @cons _ next _ head tail first rest =>
      obtain ⟨nextCore, after⟩ := next
      obtain ⟨_, returning | exiting⟩ := (step_iff_of_syscall actual request).mp first
      · obtain ⟨event, result, rfl, effect, resume⟩ := returning
        change Syscall.Step s (writeRequest off) event (.returned result) after at effect
        obtain ⟨flags, coreEq⟩ := resume
        change nextCore = returned c result flags at coreEq
        subst nextCore
        have kept := effect.write_memory_preserved
        have intactAfter : Output.Intact after.memory := by rw [kept]; exact intact
        have answerAfter : after.memory.readBytes 0x4015c0 65 = some (Sha256.expected message) := by
          rw [kept]; exact answer
        have runningAfter := write_running effect
        cases result with
        | error errno =>
          have silent := rejection c (.error errno) flags after intactAfter runningAfter (jg_error errno)
          have continuation := (X86Linux.completed_iff_of_silent silent).mp ⟨rest, stop⟩
          exact False.elim (failed_exit c off (.error errno) flags after ready intactAfter runningAfter
            continuation.1 continuation.2)
        | ok count =>
          obtain ⟨_, _, _, fits⟩ := effect.write_success
          have ledger := (successful_ledger answer accounted effect).1
          by_cases nonzero : 0 < count
          · have prefixRun := advance c off count flags after ready intactAfter runningAfter nonzero fits
            by_cases unfinished : off.val + count < 65
            · have silent := prefixRun.append
                (retry_path c off count flags after ready intactAfter runningAfter unfinished)
              have continuation := (X86Linux.completed_iff_of_silent silent).mp ⟨rest, stop⟩
              let nextOff : Fin 65 := ⟨off.val + count, unfinished⟩
              have decreased : remaining nextOff < fuel := by
                have := off.isLt
                dsimp [remaining, nextOff] at *
                omega
              have result := ih (remaining nextOff) decreased
                (c := nextRequest c off count flags) (s := after) (off := nextOff)
                (prior := prior ++ [event])
                (retry_ready c off count flags ready unfinished) intactAfter runningAfter answerAfter
                ledger continuation.1 continuation.2 rfl
              simpa only [List.append_assoc] using result
            · have complete : off.val + count = 65 := by
                have := off.isLt
                dsimp [remaining] at fits
                omega
              have silent := prefixRun.append
                (success_path c off count flags after intactAfter runningAfter complete)
              have continuation := (X86Linux.completed_iff_of_silent silent).mp ⟨rest, stop⟩
              have tailEq := successful_exit c off count flags after intactAfter runningAfter
                continuation.1 continuation.2
              rw [complete] at ledger
              have result := (output_exit ledger 0).success finite
              simpa only [tailEq, List.append_assoc] using result
          · have zero : count = 0 := by omega
            rw [zero] at rest
            have condition : X86.Ext.Cond.g.eval (X86.Ext.logicFlagsN (resultWord (.ok 0))) =
                some false := jg_ok 0 (by decide)
            have silent := rejection c (.ok 0) flags after intactAfter runningAfter condition
            have continuation := (X86Linux.completed_iff_of_silent silent).mp ⟨rest, stop⟩
            exact False.elim (failed_exit c off (.ok 0) flags after ready intactAfter runningAfter
              continuation.1 continuation.2)
      · obtain ⟨event, status, _, effect, _⟩ := exiting
        change Syscall.Step s (writeRequest off) event (.exited status) after at effect
        change Syscall.Step s (.write 1 (address off) (remaining off)) event (.exited status) after at effect
        cases effect

theorem completed_request {input : ProcInput} {message : List Byte} {prior events : List Event}
    {final : Output.PS} (c : Core) (s : Syscall.State) (off : Fin 65)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message prior off.val) (finite : input.stdin = .ofList message)
    (run : Proc.Runs X86Linux.isa Env.linux ⟨requestCore c off, s⟩ events final)
    (stop : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) :
    Sha256.Success input (prior ++ events) :=
  completed (requestCore c off) s off (request_ready c off) intact running answer accounted finite run stop

end Silmaril.Process.CLI.Sha256Cli.OutputUniversal
