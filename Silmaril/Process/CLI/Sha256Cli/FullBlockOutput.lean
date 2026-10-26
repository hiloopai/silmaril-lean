module

public import Silmaril.Process.CLI.Sha256Cli.FullBlockEof
public import Silmaril.Process.CLI.Sha256Cli.HexOutputFrame

/-! # Genuine full-block EOF through canonical output preparation

The accumulated-state/length proof establishes the hash; the existing generic
hex/newline/setup proof then establishes actual output bytes and request state.
Successful writes, universal output safety and progress remain separate.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullBlockEof

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2

/-- Compose the actual EOF, final padding and second compression with all
hex/newline stores and the first write request. No output is assumed at entry. -/
theorem output_read {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {message stateBytes : List Byte} {event : Event}
    (full : message.length = 64) (ready : ShortRead.Ready c 0 64)
    (input : ShortReadTransfer.InputAt before message 64) (running : before.exited = none)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (hash : (stateOf stateBytes).toState = Driver.compressBlock Silmaril.Crypto.SHA256.H0 message)
    (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (frame : DriverMemory.Frame initial before.memory)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top)
    (flags : Word)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok 0)) after) :
    event = .read 0 [] ∧ after = before ∧
      ∃ (outCore : Core) (memory : Memory),
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨outCore, { before with memory := memory }⟩ ∧
        HexOutputFrame.Ready initial outCore { before with memory := memory } message := by
  obtain ⟨eventEq, unchanged, final, compressed, pc, _, finalFrame, bytes, digest, value⟩ :=
    complete_read full ready input running stateRead hash rsp frame geometry stack flags effect
  obtain ⟨outCore, memory, formatted, answer⟩ := HexOutputFrame.prepare final.core
    { before with memory := final.memory } bytes message running finalFrame pc digest value
  exact ⟨eventEq, unchanged, outCore, memory, by
    simpa only [List.append_nil] using compressed.append formatted, answer⟩

end Silmaril.Process.CLI.Sha256Cli.FullBlockEof
