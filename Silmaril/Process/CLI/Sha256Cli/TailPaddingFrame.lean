module

public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.LengthStore

/-! # Actual short-tail padding with accumulated state and total

Buffer fill and total consumed length are distinct after full input blocks.
This segment retains arbitrary H32 bytes and serializes the caller's modular
total word, rather than resetting either to the short-message special case.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

/-- Actual final-block bytes. The total is a modular machine word; its
correspondence with a natural input length remains the caller's obligation. -/
def block (tail : List Byte) (total : Word) : List Byte :=
  (tail ++ (0x80 :: List.replicate (55 - tail.length) 0)) ++ LengthStore.encoded total

theorem block_length (tail : List Byte) (short : tail.length < 56) (total : Word) :
    (block tail total).length = 64 := by
  simp only [block, List.length_append, List.length_cons, List.length_replicate,
    LengthStore.encoded_length]
  omega

theorem block_short (tail : List Byte) (short : tail.length < 56) :
    block tail (BitVec.ofNat 64 tail.length) = SingleBlockReference.block tail := by
  rw [block, LengthStore.encoded_short ⟨tail.length, short⟩]
  exact (SingleBlockReference.block_expansion tail short).symm

structure CallReady (initial : Memory) (stack : Word)
    (c : Core) (s : Syscall.State) (tail stateBytes : List Byte) (total : Word) : Prop where
  short : tail.length < 56
  running : s.exited = none
  pc : c.rip = 0x400229
  stateArg : c.read .rdi = 0x401660
  blockArg : c.read .rsi = 0x401620
  state : s.memory.readBytes 0x401660 32 = some stateBytes
  block : s.memory.readBytes 0x401620 64 = some (block tail total)
  rsp : c.read .rsp = stack
  frame : DriverMemory.Frame initial s.memory

def callCore (c : Core) (total : Word) : Core :=
  LengthStore.callCore (Padding.zeroFinished c) total

def Footprint (tail : List Byte) (address : Nat) : Prop :=
  Padding.blockAddress + tail.length ≤ address ∧ address < Padding.blockAddress + 64

/-- Reuse the actual marker/zero and length stores, preserving accumulated H32.
No compressor frame, successful syscall, hash or final answer is assumed. -/
theorem prepare {initial : Memory} (c : Core) (s : Syscall.State)
    (tail stateBytes : List Byte) (total : Word)
    (short : tail.length < 56) (running : s.exited = none)
    (pc : c.rip = 0x4001bc) (fill : c.read .r8 = BitVec.ofNat 64 tail.length)
    (count : c.read .rbx = total)
    (copied : s.memory.readBytes Padding.blockAddress tail.length = some tail)
    (stateRead : s.memory.readBytes 0x401660 32 = some stateBytes)
    (frame : DriverMemory.Frame initial s.memory) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨callCore c total, { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after (Footprint tail) ∧
      CallReady initial (c.read .rsp) (callCore c total)
        { s with memory := after } tail stateBytes total := by
  have permission (access : Access) (allowed : Binary.seg1.permissions.allows access = true) :
      s.memory.Permitted access Padding.blockAddress 64 :=
    frame.bss_permitted access allowed _ _ (by decide) (by decide)
  obtain ⟨paddedMemory, padRun, padded, padFrame, padCode⟩ := PaddingShort.single_block_prefix
    c s tail short running frame.code pc fill copied (permission .write rfl) (permission .read rfl)
  obtain ⟨blockMemory, lengthRun, fullBlock, lengthFrame, _⟩ := LengthStore.store
    (Padding.zeroFinished c) { s with memory := paddedMemory } total _ running padCode rfl
      count padded ((padFrame.permitted_iff _ _ _).mpr (permission .write rfl))
      ((padFrame.permitted_iff _ _ _).mpr (permission .read rfl))
  have state : blockMemory.readBytes 0x401660 32 = some stateBytes := by
    rw [lengthFrame.readBytes (by intro offset bound; dsimp [Padding.blockAddress]; omega),
      padFrame.readBytes (by intro offset bound; dsimp [Padding.blockAddress]; omega)]
    exact stateRead
  have writes : Memory.WritesWithin s.memory blockMemory (Footprint tail) :=
    (padFrame.mono (by intro address inside; dsimp [Footprint]; omega)).trans
      (lengthFrame.mono (by intro address inside; dsimp [Footprint]; omega))
  have finalFrame : DriverMemory.Frame initial blockMemory := frame.trans (writes.mono (by
    intro address inside
    dsimp [Footprint, Padding.blockAddress] at inside
    dsimp [DriverMemory.Above]
    omega))
  refine ⟨blockMemory, by simpa only [List.nil_append, callCore] using padRun.append lengthRun,
    writes, short, running, rfl, (LengthStore.arguments _ _).2.1,
    (LengthStore.arguments _ _).1, state, fullBlock, ?_, finalFrame⟩
  simp [callCore, LengthStore.callCore, Padding.zeroFinished, X86.State.read,
    X86.State.write, Machine.RegisterFile.write]

end Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame
