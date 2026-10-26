module

public import Silmaril.Process.CLI.Sha256Cli.OutputUniversal
public import Silmaril.Process.CLI.X86Linux.ExitTrace

/-! # Every finite observation of the actual SHA output loop

This strengthens the independent completed-result theorem with prefix safety,
including finite runs that stop inside an instruction segment, at a blocked
write, after a zero/error return, or after an accepted short write. The actual
machine branches reject zero/error returns; no progress assumption is added.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.OutputPrefix

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open OutputTransfer OutputLoop

set_option maxRecDepth 10000

/-- Appending observations that accept no output preserves the prefix policy. -/
theorem append_no_output {input : ProcInput} {prior added : List Event}
    (priorOk : Sha256.PrefixOk input prior) (only : WritesOnlyTo [1] added)
    (silent : stdout added = []) : Sha256.PrefixOk input (prior ++ added) := by
  refine ⟨?_, ?_⟩
  · intro fd bytes member
    rcases List.mem_append.mp member with old | new
    · exact priorOk.1 fd bytes old
    · exact only fd bytes new
  · have written : writtenOn 1 added = [] := silent
    simpa only [stdout, writtenOn_append, written, List.append_nil] using priorOk.2

theorem exit_safe {input : ProcInput} {prior events : List Event}
    {c trapped : Core} {s : Syscall.State} {status : Nat} {final : Output.PS}
    (priorOk : Sha256.PrefixOk input prior)
    (trappedStep : X86Linux.step c s.memory = .syscall trapped)
    (requested : X86Linux.request trapped = some (.exit status))
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  rcases X86Linux.runs_exit trappedStep requested execution with rfl | rfl
  · simpa only [List.append_nil] using priorOk
  · exact append_no_output priorOk (by intro fd bytes member; simp at member) rfl

/-- Prefix policies survive early endpoints inside a supplied silent segment.
The prior trace is retained, so this interface composes across syscall replies. -/
theorem of_silent {initial middle final : Output.PS} {prior events : List Event}
    {input : ProcInput} (silent : Proc.Runs X86Linux.isa Env.linux initial [] middle)
    (priorOk : Sha256.PrefixOk input prior)
    (after : ∀ events final, Proc.Runs X86Linux.isa Env.linux middle events final →
      Sha256.PrefixOk input (prior ++ events))
    (execution : Proc.Runs X86Linux.isa Env.linux initial events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  rcases Proc.runs_empty_or_after_silent X86Linux.instruction_deterministic silent execution with
      rfl | continuation
  · simpa only [List.append_nil] using priorOk
  · exact after _ _ continuation

theorem at_exit {input : ProcInput} {message : List Byte} {prior events : List Event}
    {off : Nat} {c trapped : Core} {s : Syscall.State} {status : Nat} {final : Output.PS}
    (accounted : Driver.OutputInv message prior off) (finite : input.stdin = .ofList message)
    (trappedStep : X86Linux.step c s.memory = .syscall trapped)
    (requested : X86Linux.request trapped = some (.exit status))
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  rcases X86Linux.runs_exit trappedStep requested execution with rfl | rfl
  · simpa only [List.append_nil] using accounted.prefix finite
  · exact (OutputUniversal.output_exit accounted _).prefix finite

theorem failed (c : Core) (off : Fin 65) (result : Result) (flags : Word)
    (s : Syscall.State) (ready : Ready c off) (intact : Output.Intact s.memory)
    {input : ProcInput} {message : List Byte} {prior events : List Event} {n : Nat}
    {final : Output.PS} (accounted : Driver.OutputInv message prior n)
    (finite : input.stdin = .ofList message)
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨failure c result flags, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  have actual : X86Linux.step (failure c result flags) s.memory =
      Binary.i_4002b5.denote (failure c result flags) s.memory :=
    step_of_entry Binary.ok_4002b5.1 rfl (intact _ (by simp [Binary.transcript]))
  have trap : X86Linux.step (failure c result flags) s.memory =
      .syscall { failure c result flags with rip := 0x4002b7 } := by
    simpa [Entry.denote, Binary.i_4002b5, OutputLoop.failure] using actual
  have fd : c.regs .rdi = 1 := ready.fd
  have requestExit : X86Linux.request { failure c result flags with rip := 0x4002b7 } =
      some (.exit 1) := by
    simp [X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber, X86Linux.exitNumber,
      OutputLoop.failure, rejected, tested, returned, trapped,
      X86.State.read, X86.State.write, Machine.RegisterFile.write, fd]
  exact at_exit accounted finite trap requestExit execution

theorem successful (c : Core) (off : Fin 65) (count : Nat) (flags : Word)
    (s : Syscall.State) (intact : Output.Intact s.memory)
    {input : ProcInput} {message : List Byte} {prior events : List Event} {n : Nat}
    {final : Output.PS} (accounted : Driver.OutputInv message prior n)
    (finite : input.stdin = .ofList message)
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨success c off count flags, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  have actual : X86Linux.step (success c off count flags) s.memory =
      Binary.i_4002d1.denote (success c off count flags) s.memory :=
    step_of_entry Binary.ok_4002d1.1 rfl (intact _ (by simp [Binary.transcript]))
  have trap : X86Linux.step (success c off count flags) s.memory =
      .syscall { success c off count flags with rip := 0x4002d3 } := by
    simpa [Entry.denote, Binary.i_4002d1, success] using actual
  have requestExit : X86Linux.request { success c off count flags with rip := 0x4002d3 } =
      some (.exit 0) := by
    simp [X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber, X86Linux.exitNumber,
      success, successNumber, X86.State.read, X86.State.write, Machine.RegisterFile.write]
  exact at_exit accounted finite trap requestExit execution

/-- Every finite execution from any unfinished canonical write cutpoint emits
only a prefix of the correct digest/newline, on stdout alone. All admitted
write lengths, error profiles and resumed R11 values remain quantified. -/
theorem safe {input : ProcInput} {message : List Byte} {prior events : List Event}
    {final : Output.PS} (c : Core) (s : Syscall.State) (off : Fin 65)
    (ready : Ready c off) (intact : Output.Intact s.memory) (running : s.exited = none)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message prior off.val) (finite : input.stdin = .ofList message)
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  generalize fuelEq : remaining off = fuel
  induction fuel using Nat.strong_induction_on generalizing c s off prior events final with
  | h fuel ih =>
    have actual := OutputUniversal.instruction c off s.memory ready intact
    have request := OutputUniversal.requested c off ready
    cases execution with
    | refl => simpa only [List.append_nil] using accounted.prefix finite
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
        have runningAfter := OutputUniversal.write_running effect
        have result : Sha256.PrefixOk input ((prior ++ [event]) ++ tail) := by
          cases result with
          | error errno =>
            have ledger := (error_ledger accounted effect).1
            exact of_silent
              (rejection c (.error errno) flags after intactAfter runningAfter (jg_error errno))
              (ledger.prefix finite)
              (fun _ _ continuation => failed c off (.error errno) flags after ready intactAfter
                ledger finite continuation) rest
          | ok count =>
            obtain ⟨_, _, _, fits⟩ := effect.write_success
            have ledger := (successful_ledger answer accounted effect).1
            by_cases nonzero : 0 < count
            · have prefixRun := advance c off count flags after ready intactAfter runningAfter nonzero fits
              by_cases unfinished : off.val + count < 65
              · have silent := prefixRun.append
                  (retry_path c off count flags after ready intactAfter runningAfter unfinished)
                let nextOff : Fin 65 := ⟨off.val + count, unfinished⟩
                have decreased : remaining nextOff < fuel := by
                  have := off.isLt
                  dsimp [remaining, nextOff] at *
                  omega
                exact of_silent silent (ledger.prefix finite) (fun _ _ continuation =>
                  ih (remaining nextOff) decreased (c := nextRequest c off count flags)
                    (s := after) (off := nextOff) (prior := prior ++ [event])
                    (retry_ready c off count flags ready unfinished) intactAfter runningAfter
                    answerAfter ledger continuation rfl) rest
              · have complete : off.val + count = 65 := by
                  have := off.isLt
                  dsimp [remaining] at fits
                  omega
                have silent := prefixRun.append
                  (success_path c off count flags after intactAfter runningAfter complete)
                exact of_silent silent (ledger.prefix finite) (fun _ _ continuation =>
                  successful c off count flags after intactAfter ledger finite continuation) rest
            · have zero : count = 0 := by omega
              rw [zero] at rest
              have condition : X86.Ext.Cond.g.eval (X86.Ext.logicFlagsN (resultWord (.ok 0))) =
                  some false := jg_ok 0 (by decide)
              exact of_silent
                (rejection c (.ok 0) flags after intactAfter runningAfter condition)
                (ledger.prefix finite) (fun _ _ continuation =>
                  failed c off (.ok 0) flags after ready intactAfter ledger finite continuation) rest
        simpa only [List.append_assoc] using result
      · obtain ⟨_, _, _, effect, _⟩ := exiting
        change Syscall.Step s (.write 1 (address off) (remaining off)) _ (.exited _) after at effect
        cases effect

theorem prefix_request {input : ProcInput} {message : List Byte} {prior events : List Event}
    {final : Output.PS} (c : Core) (s : Syscall.State) (off : Fin 65)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message prior off.val) (finite : input.stdin = .ofList message)
    (execution : Proc.Runs X86Linux.isa Env.linux ⟨requestCore c off, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) :=
  safe (requestCore c off) s off (request_ready c off) intact running answer accounted finite execution

end Silmaril.Process.CLI.Sha256Cli.OutputPrefix
