module

public import Silmaril.Process.CLI.Sha256Cli.ShortReadFrame
public import Silmaril.Process.CLI.Sha256Cli.ShortReadFailure
public import Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame

/-! # Genuine EOF with independent buffer fill, stream cursor and total

The current H32 bytes survive actual EOF and final-short-tail padding. The
input cursor need not equal buffer fill after completed compression blocks.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.TailReadEofFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

set_option maxRecDepth 10000

/-- Every admitted zero from this positive-capacity read is genuine EOF.
The original stream, accumulated state, source frame and stack remain explicit;
the total word's relation to the input length is not silently inferred. -/
theorem to_call {initial : Memory} {stack : Word} {c : Core}
    {before after : Syscall.State} {message tail stateBytes : List Byte}
    {cursor : Nat} {total : Word} {event : Event}
    (ready : ShortRead.Ready c tail.length total) (short : tail.length < 56)
    (cursorBound : cursor ≤ message.length)
    (input : ShortReadTransfer.InputAt before message cursor)
    (running : before.exited = none)
    (copied : before.memory.readBytes Padding.blockAddress tail.length = some tail)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (rsp : c.read .rsp = stack) (frame : DriverMemory.Frame initial before.memory)
    (flags : Word)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok 0)) after) :
    cursor = message.length ∧ event = .read 0 [] ∧ after = before ∧
      ∃ (prepared : Core) (memory : Memory),
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨prepared, { before with memory := memory }⟩ ∧
        Memory.WritesWithin before.memory memory (TailPaddingFrame.Footprint tail) ∧
        TailPaddingFrame.CallReady initial stack prepared
          { before with memory := memory } tail stateBytes total := by
  have request := ready.request short
  obtain ⟨atEnd, eventEq, environment⟩ := ShortReadTransfer.zero_is_eof
    cursorBound input request.2 effect
  subst event
  subst after
  have trapped : X86Linux.step c before.memory = .syscall { c with rip := 0x400177 } := by
    have actual := step_of_entry (core := c) (memory := before.memory) Binary.ok_400175.1
      (by simp [ready.pc, Binary.i_400175]) (frame.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400175, ready.pc] using actual
  let returned := ShortReadFrame.returnedCore c (.ok 0) flags
  have read : Proc.Step X86Linux.isa Env.linux (⟨c, before⟩ : Output.PS) [.read 0 []]
      ⟨returned, before⟩ := .call running trapped.symm request.1 effect ⟨flags, rfl⟩
  have eof := ShortReadFailure.eof_prefix returned before running frame.code rfl rfl
  let padding := ShortReadFailure.paddingCore returned
  have filled : padding.read .r8 = BitVec.ofNat 64 tail.length := ready.filled
  have count : padding.read .rbx = total := ready.total
  obtain ⟨memory, body, writes, padded⟩ := TailPaddingFrame.prepare padding before
    tail stateBytes total short running rfl filled count copied stateRead frame
  have stackEq : padding.read .rsp = stack := rsp
  refine ⟨atEnd, rfl, rfl, TailPaddingFrame.callCore padding total, memory, ?_, writes, ?_⟩
  · simpa only [List.nil_append, List.append_nil] using
      (Machine.Trace.Runs.single read).append (eof.append body)
  · simpa only [stackEq] using padded

end Silmaril.Process.CLI.Sha256Cli.TailReadEofFrame
