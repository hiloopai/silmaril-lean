module

public import Silmaril.Process.CLI.Sha256Cli.TailPaddingReference
public import Silmaril.Process.CLI.Sha256Cli.BlockSequenceOutput

/-! # Actual accumulated-state short-tail EOF through canonical output

The tail and accumulated hash are read from the original process memory.
Genuine EOF, retained padding instructions, checked CALL/body/RET and formatting
establish the reference answer. No per-message padding certificate, installed
compressor entry, initial-state reset or progress premise is used.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.TailReadEofFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-- The actual repeated read at any established short-tail cut executes the
canonical final hash and output setup, retaining the source frame and stack.
The preceding read schedule and long-tail machine path remain separate. -/
theorem canonical_output {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {prefixBlocks : List (List Byte)} {tail stateBytes : List Byte}
    {cursor : Nat} {event : Event}
    (ready : ShortRead.Ready c tail.length (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length))
    (short : tail.length < 56) (full : ∀ block ∈ prefixBlocks, block.length = 64)
    (cursorBound : cursor ≤ (prefixBlocks.flatten ++ tail).length)
    (input : ShortReadTransfer.InputAt before (prefixBlocks.flatten ++ tail) cursor)
    (running : before.exited = none)
    (copied : before.memory.readBytes Padding.blockAddress tail.length = some tail)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (hash : (stateOf stateBytes).toState =
      prefixBlocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0)
    (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (frame : DriverMemory.Frame initial before.memory)
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
  obtain ⟨atEnd, eventEq, unchanged, _, _, padded, _, callReady⟩ :=
    to_call ready short cursorBound input running copied stateRead rsp frame flags effect
  obtain ⟨final, compressed, pc, _, finalFrame, bytes, digest, compression⟩ :=
    callReady.compress geometry stack
  rw [hash] at compression
  have value := compression.trans (TailPaddingReference.fold_short prefixBlocks tail full short)
  obtain ⟨outCore, memory, formatted, answer⟩ := HexOutputFrame.prepare final.core
    { before with memory := final.memory } bytes (prefixBlocks.flatten ++ tail)
      running finalFrame pc digest value
  exact ⟨atEnd, eventEq, unchanged, outCore, memory, by
    simpa only [List.append_nil] using (padded.append compressed).append formatted, answer⟩

end Silmaril.Process.CLI.Sha256Cli.TailReadEofFrame
