module

public import Silmaril.Process.CLI.Sha256Cli.FullBlockIteration
public import Silmaril.Process.CLI.Sha256Cli.ShortReadInit
public import Silmaril.Process.CLI.Sha256Cli.TailBlockOutput

/-! # Actual short tails after accumulated full-block compression

Buffer fill, natural input cursor and modular total are independent. The tail
cut retains observed H32 bytes and the original memory frame; it does not reset
the accumulated hash to H0. Only the existing below-56 machine path is covered.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullBlockIteration

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

structure TailReady (initial : Memory) (top : Nat) (c : Core) (s : Syscall.State)
    (tail : List Byte) (total : Word) (state : Silmaril.Crypto.SHA256.State) : Prop where
  short : tail.length < 56
  registers : ShortRead.Ready c tail.length total
  running : s.exited = none
  rsp : c.read .rsp = BitVec.ofNat 64 (top - 32)
  frame : DriverMemory.Frame initial s.memory
  copied : s.memory.readBytes 0x401620 tail.length = some tail
  hash : ∃ bytes, s.memory.readBytes 0x401660 32 = some bytes ∧ (stateOf bytes).toState = state

set_option maxRecDepth 100000

/-- The actual first full read, optimized first-return path and checked
compression/restart. The pre-read H32 bytes come from the supplied memory. -/
theorem first_full_read {initial : Memory} {top : Nat} {before after : Syscall.State}
    {stateBytes : List Byte} {event : Event} (c : Core) (flags : Word)
    (running : before.exited = none) (pc : c.rip = 0x400159)
    (request : X86Linux.request { c with rip := 0x40015b } = some (.read 0 0x401620 64))
    (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (frame : DriverMemory.Frame initial before.memory)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok 64)) after)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (block : List Byte) (next : Core) (memory : Memory),
      block.length = 64 ∧ event = .read 0 block ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [event]
        ⟨next, { after with memory := memory }⟩ ∧
      Ready initial top next { after with memory := memory } 64
        (Driver.compressBlock (stateOf stateBytes).toState block) := by
  obtain ⟨block, length, eventEq, afterRunning, stored⟩ := full_read_stored effect
  have nextFrame : DriverMemory.Frame initial after.memory := frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have stateRead' : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  have blockRead : after.memory.readBytes 0x401620 64 = some block := by
    simpa only [Memory.readBytes, length] using stored.readWith_self
      (by rw [length]; exact frame.bss_permitted .read rfl _ _ (by decide) (by decide))
  let returned := ShortReadInit.returnedCore c 64 flags
  have trapped : X86Linux.step c before.memory = .syscall { c with rip := 0x40015b } := by
    have actual := step_of_entry (core := c) (memory := before.memory) Binary.ok_400159.1
      (by simp [pc, Binary.i_400159]) (frame.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400159, pc] using actual
  have read : Proc.Step X86Linux.isa Env.linux (⟨c, before⟩ : Output.PS) [event]
      ⟨returned, after⟩ := .call running trapped.symm request effect ⟨flags, rfl⟩
  have toCall := FullRead.first_to_call returned after afterRunning nextFrame.code rfl rfl
  have callRsp : (FullRead.firstCallCore returned).read .rsp = BitVec.ofNat 64 (top - 32) := by
    simpa [FullRead.firstCallCore, FullRead.callCore, ReadAdvance.countCore,
      ShortReadBranches.initialCore, returned, ShortReadInit.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using rsp
  obtain ⟨next, memory, compressed, fresh⟩ := compress_restart
    (FullRead.firstCallCore returned) after stateBytes block 64 afterRunning rfl callRsp
      rfl rfl rfl rfl stateRead' blockRead nextFrame geometry stack
  exact ⟨block, next, memory, length, eventEq, by
    simpa only [List.append_nil] using ((Machine.Trace.Runs.single read).append toCall).append compressed,
    fresh⟩

/-- Classify any admitted positive return at a fresh full-capacity read. -/
theorem short_read_stored {before after : Syscall.State} {event : Event} {amount : Nat}
    (positive : 0 < amount)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok amount)) after) :
    ∃ tail, tail.length = amount ∧ event = .read 0 tail ∧ after.exited = none ∧
      X86.Ext.Stored before.memory after.memory 0x401620 tail := by
  generalize resultEq : Result.ok amount = result at effect
  cases effect with
  | @readSome _ _ _ descriptor bytes memory running opened mode matched nonempty bounded transfer accessible copied =>
    exact ⟨bytes, (Result.ok.inj resultEq).symm, rfl, running, X86.Ext.Stored.of_writeBytes copied⟩
  | readEof => have zero := Result.ok.inj resultEq; omega
  | readError => cases resultEq
  | readBadDescriptor => cases resultEq
  | readBadAddress => cases resultEq

/-- A real short repeated read retains accumulated H32 and advances the modular
total. The actual copied tail is classified from the syscall, not installed as
a premise, and the natural descriptor cursor remains in the original state. -/
theorem Ready.read_short {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {total : Word} {state : Silmaril.Crypto.SHA256.State}
    {event : Event} {amount : Nat} (ready : Ready initial top c before total state)
    (positive : 0 < amount) (short : amount < 56) (flags : Word)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok amount)) after) :
    ∃ (tail : List Byte) (next : Core),
      tail.length = amount ∧ event = .read 0 tail ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [event] ⟨next, after⟩ ∧
      TailReady initial top next after tail (total + BitVec.ofNat 64 amount) state := by
  obtain ⟨tail, length, eventEq, running, stored⟩ := short_read_stored positive effect
  have nextFrame : DriverMemory.Frame initial after.memory := ready.frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have tailRead : after.memory.readBytes 0x401620 tail.length = some tail :=
    stored.readWith_self (by rw [length]; exact ready.frame.bss_permitted .read rfl _ _ (by decide) (by omega))
  obtain ⟨stateBytes, stateRead, hash⟩ := ready.hash
  have stateRead' : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  let returned := ShortReadFrame.returnedCore c (.ok amount) flags
  have trapped : X86Linux.step c before.memory = .syscall { c with rip := 0x400177 } := by
    have actual := step_of_entry (core := c) (memory := before.memory) Binary.ok_400175.1
      (by simp [ready.registers.pc, Binary.i_400175]) (ready.frame.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400175, ready.registers.pc] using actual
  have read : Proc.Step X86Linux.isa Env.linux (⟨c, before⟩ : Output.PS) [event]
      ⟨returned, after⟩ :=
    .call ready.running trapped.symm (ready.registers.request (by decide)).1 effect ⟨flags, rfl⟩
  have rax : returned.read .rax = BitVec.ofNat 64 amount := by
    simp [returned, ShortReadFrame.returnedCore, resultWord, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have r8 : returned.read .r8 = 0 := ready.registers.filled
  have rbp : returned.read .rbp = 64 := ready.registers.blockSize
  have body := ShortReadBranches.positive_loop returned after 0 amount positive (by omega)
    running nextFrame.code rfl rax r8 rbp
  have registers := ShortRead.next_ready returned 0 amount rbp
  have count : returned.read .rbx = total := ready.registers.total
  rw [count] at registers
  refine ⟨tail, ShortRead.nextCore returned 0 amount, length, eventEq, ?_, ?_⟩
  · simpa only [List.append_nil] using (Machine.Trace.Runs.single read).append body
  · exact ⟨by omega, by simpa only [Nat.zero_add, length] using registers, running,
      (ShortRead.next_rsp _ _ _).trans ready.rsp, nextFrame, tailRead, stateBytes, stateRead', hash⟩

/-- Finish a retained short-tail cut using canonical whole-message padding.
The finite input cursor is supplied independently of the tail buffer fill. -/
theorem TailReady.eof_output {initial : Memory} {top : Nat} {c : Core}
    {before after : Syscall.State} {tail : List Byte} {prefixBlocks : List (List Byte)}
    {state : Silmaril.Crypto.SHA256.State} {cursor : Nat} {event : Event}
    (ready : TailReady initial top c before tail
      (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length) state)
    (full : ∀ block ∈ prefixBlocks, block.length = 64)
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
  obtain ⟨bytes, observed, value⟩ := ready.hash
  exact TailReadEofFrame.canonical_output ready.registers ready.short full cursorBound input
    ready.running ready.copied observed (value.trans hash) ready.rsp ready.frame geometry stack flags effect

end Silmaril.Process.CLI.Sha256Cli.FullBlockIteration
