module

public import Silmaril.Process.CLI.Sha256Cli.BufferedTailFrame
public import Silmaril.Process.CLI.Sha256Cli.LongTailOutputFrame
public import Silmaril.Process.CLI.Sha256Cli.ShortReadFailure

/-! # Genuine long-tail EOF through both actual compression calls

The stream cursor and whole-input modular total remain independent of buffer
fill. A positive-capacity returned zero proves genuine EOF. Canonical output
additionally requires the caller's accumulated prefix fold and whole count.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.LongTailReadEofFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

set_option maxRecDepth 100000

/-- Actual zero read, TEST/JE and marker/first-block stores, preserving the
original observed H32, total, source frame and symbolic stack. -/
theorem to_call {initial : Memory} {stack : Word} {c : Core}
    {before after : Syscall.State} {message tail stateBytes : List Byte}
    {cursor : Nat} {total : Word} {event : Event}
    (ready : ShortRead.Ready c tail.length total) (long : 56 ≤ tail.length) (room : tail.length < 64)
    (cursorBound : cursor ≤ message.length) (input : ShortReadTransfer.InputAt before message cursor)
    (running : before.exited = none)
    (copied : before.memory.readBytes Padding.blockAddress tail.length = some tail)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (rsp : c.read .rsp = stack) (frame : DriverMemory.Frame initial before.memory) (flags : Word)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok 0)) after) :
    cursor = message.length ∧ event = .read 0 [] ∧ after = before ∧
      ∃ (prepared : Core) (memory : Memory),
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨prepared, { before with memory := memory }⟩ ∧
        ExtraPaddingFrame.CallReady initial stack prepared { before with memory := memory }
          tail stateBytes total := by
  have request := ready.request_below64 room
  obtain ⟨atEnd, eventEq, environment⟩ := ShortReadTransfer.zero_is_eof cursorBound input request.2 effect
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
  obtain ⟨memory, body, _, padded⟩ := ExtraPaddingFrame.prepare padding before tail stateBytes total
    room long running rfl filled count copied stateRead frame
  have stackEq : padding.read .rsp = stack := rsp
  exact ⟨atEnd, rfl, rfl, PaddingExtra.callCore padding tail.length, memory, by
    simpa only [List.nil_append, List.append_nil] using (Machine.Trace.Runs.single read).append (eof.append body),
    by simpa only [stackEq] using padded⟩

end Silmaril.Process.CLI.Sha256Cli.LongTailReadEofFrame

namespace Silmaril.Process.CLI.Sha256Cli.BufferedTailFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-- Genuine EOF executes both actual CALL/body/RET paths on the accumulated
H32. The modular total is retained as a ghost after destructive serialization. -/
theorem Ready.long_return {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {message tail : List Byte} {total : Word}
    {state : Silmaril.Crypto.SHA256.State} {cursor : Nat} {event : Event}
    (ready : Ready initial (BitVec.ofNat 64 (top - 32)) c before tail total state)
    (long : 56 ≤ tail.length) (cursorBound : cursor ≤ message.length)
    (input : ShortReadTransfer.InputAt before message cursor)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top)
    (flags : Word)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok 0)) after) :
    cursor = message.length ∧ event = .read 0 [] ∧ after = before ∧
      ∃ (priorH : List Byte) (next : Core) (memory : Memory),
        (stateOf priorH).toState = state ∧
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨next, { before with memory := memory }⟩ ∧
        LongTailOutputFrame.Returned initial (BitVec.ofNat 64 (top - 32)) next
          { before with memory := memory } tail priorH total := by
  obtain ⟨priorH, observed, value⟩ := ready.hash
  obtain ⟨atEnd, eventEq, unchanged, _, _, padded, callReady⟩ :=
    LongTailReadEofFrame.to_call ready.registers long ready.room cursorBound input ready.running
      ready.copied observed ready.rsp ready.frame flags effect
  obtain ⟨_, _, first, _, loopReady⟩ := ExtraPaddingContinuation.advance callReady geometry stack
  obtain ⟨_, stores, _, finalReady⟩ := SecondPaddingFrame.prepare loopReady
  obtain ⟨next, memory, second, _, returned⟩ := LongTailOutputFrame.advance finalReady geometry stack
  exact ⟨atEnd, eventEq, unchanged, priorH, next, memory, value, by
    simpa only [List.append_nil] using ((padded.append first).append stores).append second, returned⟩

/-- Canonical output follows genuine EOF only with the actual accumulated
prefix fold and the whole-message modular byte count supplied by the caller. -/
theorem Ready.long_output {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {tail : List Byte} {prefixBlocks : List (List Byte)}
    {state : Silmaril.Crypto.SHA256.State} {cursor : Nat} {event : Event}
    (ready : Ready initial (BitVec.ofNat 64 (top - 32)) c before tail
      (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length) state)
    (long : 56 ≤ tail.length) (full : ∀ block ∈ prefixBlocks, block.length = 64)
    (hash : state = prefixBlocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0)
    (cursorBound : cursor ≤ (prefixBlocks.flatten ++ tail).length)
    (input : ShortReadTransfer.InputAt before (prefixBlocks.flatten ++ tail) cursor)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top)
    (flags : Word)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok 0)) after) :
    cursor = (prefixBlocks.flatten ++ tail).length ∧ event = .read 0 [] ∧ after = before ∧
      ∃ (outCore : Core) (memory : Memory),
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨outCore, { before with memory := memory }⟩ ∧
        HexOutputFrame.Ready initial outCore { before with memory := memory }
          (prefixBlocks.flatten ++ tail) := by
  obtain ⟨atEnd, eventEq, unchanged, priorH, _, _, value, compressed, returned⟩ :=
    ready.long_return long cursorBound input geometry stack flags effect
  obtain ⟨outCore, memory, formatted, answer⟩ :=
    returned.canonical_output prefixBlocks full (value.trans hash) rfl
  exact ⟨atEnd, eventEq, unchanged, outCore, memory, by
    simpa only [List.append_nil] using compressed.append formatted, answer⟩

end Silmaril.Process.CLI.Sha256Cli.BufferedTailFrame
