module

public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.PaddingExtra
public import Silmaril.Process.CLI.Sha256Cli.CompressionSite

/-! # Original long-tail first-padding-block CALL cut point

The copied tail, accumulated H32, modular total, source descriptor state and
symbolic stack are retained. The theorem executes the actual marker, branches,
zero loop and argument instructions; it does not install a padding block,
compression result or digest. The second length-bearing block remains separate.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ExtraPaddingFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

structure CallReady (initial : Memory) (stack : Word)
    (c : Core) (s : Syscall.State) (tail stateBytes : List Byte) (total : Word) : Prop where
  long : 56 ≤ tail.length
  room : tail.length < 64
  running : s.exited = none
  pc : c.rip = CompressionSite.extraPadding.address
  stateArg : c.read .rdi = 0x401660
  blockArg : c.read .rsi = 0x401620
  totalRetained : c.read .rbx = total
  state : s.memory.readBytes 0x401660 32 = some stateBytes
  block : s.memory.readBytes 0x401620 64 = some (PaddingExtra.block tail)
  rsp : c.read .rsp = stack
  frame : DriverMemory.Frame initial s.memory

def Footprint (tail : List Byte) (address : Nat) : Prop :=
  Padding.blockAddress + tail.length ≤ address ∧ address < Padding.blockAddress + 64

/-- Prepare the actual extra-padding CALL while preserving arbitrary observed
state bytes and modular total. Only the tail's unused buffer suffix is written;
all descriptor fields and every other byte remain the caller's actual values. -/
theorem prepare {initial : Memory} (c : Core) (s : Syscall.State)
    (tail stateBytes : List Byte) (total : Word)
    (room : tail.length < 64) (long : 56 ≤ tail.length) (running : s.exited = none)
    (pc : c.rip = 0x4001bc) (fill : c.read .r8 = BitVec.ofNat 64 tail.length)
    (count : c.read .rbx = total)
    (copied : s.memory.readBytes Padding.blockAddress tail.length = some tail)
    (stateRead : s.memory.readBytes 0x401660 32 = some stateBytes)
    (frame : DriverMemory.Frame initial s.memory) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨PaddingExtra.callCore c tail.length, { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after (Footprint tail) ∧
      CallReady initial (c.read .rsp) (PaddingExtra.callCore c tail.length)
        { s with memory := after } tail stateBytes total := by
  have permission (access : Access) (allowed : Binary.seg1.permissions.allows access = true) :
      s.memory.Permitted access Padding.blockAddress 64 :=
    frame.bss_permitted access allowed _ _ (by decide) (by decide)
  obtain ⟨after, padding, block, changes, code⟩ := PaddingExtra.first_block c s tail room long
    running frame.code pc fill copied (permission .write rfl) (permission .read rfl)
  have state : after.readBytes 0x401660 32 = some stateBytes := by
    rw [changes.readBytes (by intro offset bound; dsimp [Padding.blockAddress]; omega)]
    exact stateRead
  have writes : Memory.WritesWithin s.memory after (Footprint tail) := changes
  have finalFrame : DriverMemory.Frame initial after := frame.trans (writes.mono (by
    intro address inside
    dsimp [Footprint, Padding.blockAddress] at inside
    dsimp [DriverMemory.Above]
    omega))
  have args := PaddingExtra.callCore_registers c tail.length
  refine ⟨after, ?_, writes, long, room, running, rfl,
    args.1, args.2.1, args.2.2.1.trans count, state, block, args.2.2.2, finalFrame⟩
  simpa only [List.nil_append] using padding.append
    (PaddingExtra.arguments c { s with memory := after } tail.length running code)

end Silmaril.Process.CLI.Sha256Cli.ExtraPaddingFrame
