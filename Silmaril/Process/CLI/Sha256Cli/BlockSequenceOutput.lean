module

public import Silmaril.Process.CLI.Sha256Cli.FullBlockList
public import Silmaril.Process.CLI.Sha256Cli.FullBlockOutput

/-! # Finishing a certified sequence of actual compression blocks

The modular total is never interpreted as an unbounded natural byte count.
The caller proves the exact canonical padded-block decomposition, including
the actual modular length field. No SHA compression rounds are recomputed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-- A checked padded-block decomposition bridges the accumulated fold and
actual final padding block to the existing SHA specification. -/
theorem FullBlockReference.fold_eq_hash (message : List Byte) (blocks : List (List Byte))
    (total : Word)
    (reference : Driver.paddedBlocks message = blocks ++ [TailPaddingFrame.block [] total]) :
    Driver.compressBlock (blocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0)
      (TailPaddingFrame.block [] total) = Silmaril.Crypto.SHA256.hash (message.map UInt8.ofBitVec) := by
  have folded := Driver.fold_paddedBlocks message
  rw [reference, List.foldl_append] at folded
  simpa only [List.foldl_cons, List.foldl_nil] using folded

namespace FullBlockIteration

/-- Genuine EOF after a supplied sequence of full input blocks executes the
actual final padding/compression and hexadecimal/newline/write setup. The
reference certificate checks the accumulated fold and modular length field. -/
theorem Ready.eof_output {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {total : Word} {message : List Byte}
    {blocks : List (List Byte)} {state : Silmaril.Crypto.SHA256.State} {event : Event}
    (ready : Ready initial top c before total state)
    (input : ShortReadTransfer.InputAt before message message.length)
    (hash : state = blocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0)
    (reference : Driver.paddedBlocks message = blocks ++ [TailPaddingFrame.block [] total])
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top)
    (flags : Word)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok 0)) after) :
    event = .read 0 [] ∧ after = before ∧
      ∃ (outCore : Core) (memory : Memory),
        Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [.read 0 []]
          ⟨outCore, { before with memory := memory }⟩ ∧
        HexOutputFrame.Ready initial outCore { before with memory := memory } message := by
  obtain ⟨stateBytes, stateRead, hashRead⟩ := ready.hash
  have emptyRead : before.memory.readBytes Padding.blockAddress 0 = some [] :=
    Memory.readWith_eq _ _ _ []
      (ready.frame.bss_permitted .read rfl _ _ (by decide) (by decide))
      (by intro index bound; simp at bound)
  obtain ⟨_, eventEq, unchanged, _, _, padding, _, callReady⟩ :=
    TailReadEofFrame.to_call (tail := []) ready.registers (by decide) (Nat.le_refl _)
      input ready.running emptyRead stateRead ready.rsp ready.frame flags effect
  obtain ⟨final, compressed, pc, _, finalFrame, bytes, digest, compression⟩ :=
    callReady.compress geometry stack
  rw [hashRead, hash] at compression
  have value := compression.trans (FullBlockReference.fold_eq_hash message blocks total reference)
  obtain ⟨outCore, memory, formatted, answer⟩ := HexOutputFrame.prepare final.core
    { before with memory := final.memory } bytes message ready.running finalFrame pc digest value
  exact ⟨eventEq, unchanged, outCore, memory, by
    simpa only [List.append_nil] using (padding.append compressed).append formatted, answer⟩

end FullBlockIteration

end Silmaril.Process.CLI.Sha256Cli
