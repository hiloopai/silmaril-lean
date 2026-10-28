module

public import Silmaril.Process.CLI.Sha256Cli.TailReadEofFrame
public import Silmaril.Process.CLI.Sha256Cli.TailCompressionFrame
public import Silmaril.Process.CLI.Sha256Cli.FullBlockReference

/-! # Actual EOF and final compression after one full input block

This composition starts at a real read cutpoint with accumulated hash/length
established by the prior block. It classifies any admitted successful zero;
it does not assume EOF availability, a preinstalled padded block or an answer.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullBlockEof

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word MState)
open Silmaril.Crypto.X86.Sha256O2

/-- A genuine EOF after an actually established first compression executes the
final empty-tail/total64 padding block and returns the complete reference hash.
Source READ352/write mapping and stack/global geometry remain explicit. -/
theorem complete_read {initial : Memory} {top : Nat} {c : Core}
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
      ∃ final : MState,
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨final.core, { before with memory := final.memory }⟩ ∧
        final.core.rip = CompressionCallFrame.returnAddress ∧
        final.core.read .rsp = BitVec.ofNat 64 (top - 32) ∧
        DriverMemory.Frame initial final.memory ∧
        ∃ bytes, final.memory.readBytes 0x401660 32 = some bytes ∧
          (stateOf bytes).toState = Silmaril.Crypto.SHA256.hash (message.map UInt8.ofBitVec) := by
  have emptyRead : before.memory.readBytes Padding.blockAddress 0 = some [] := by
    exact Memory.readWith_eq _ _ _ []
      (frame.bss_permitted .read rfl _ _ (by decide) (by decide))
      (by intro index bound; simp at bound)
  obtain ⟨_, eventEq, unchanged, prepared, memory, padding, _, callReady⟩ :=
    TailReadEofFrame.to_call (tail := []) ready (by decide) (by omega) input running
      emptyRead stateRead rsp frame flags effect
  obtain ⟨final, compression, pc, restored, finalFrame, bytes, digest, reference⟩ :=
    callReady.compress geometry stack
  rw [hash] at reference
  exact ⟨eventEq, unchanged, final, by
    simpa only [List.append_nil] using padding.append compression,
    pc, restored, finalFrame, bytes, digest,
    reference.trans (FullBlockReference.compress_eq_hash message full)⟩

end Silmaril.Process.CLI.Sha256Cli.FullBlockEof
