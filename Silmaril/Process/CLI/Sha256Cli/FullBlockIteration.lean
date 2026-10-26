module

public import Silmaril.Process.CLI.Sha256Cli.FullReadRepeat
public import Silmaril.Process.CLI.Sha256Cli.ShortReadFrame
public import Silmaril.Process.CLI.Sha256Cli.Driver

/-! # Reusable actual full-block iterations

A fresh read cut point carries arbitrary accumulated SHA state and a modular
total. The real full-block CALL/body/RET and restart preserve the source frame
and descriptor state. An admitted 64-byte read supplies the next actual block.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullBlockIteration

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

structure Ready (initial : Memory) (top : Nat) (c : Core) (s : Syscall.State)
    (total : Word) (state : Silmaril.Crypto.SHA256.State) : Prop where
  registers : ShortRead.Ready c 0 total
  running : s.exited = none
  rsp : c.read .rsp = BitVec.ofNat 64 (top - 32)
  frame : DriverMemory.Frame initial s.memory
  hash : ∃ bytes, s.memory.readBytes 0x401660 32 = some bytes ∧ (stateOf bytes).toState = state

set_option maxRecDepth 100000 in
/-- One actual full-block compression/restart for arbitrary accumulated state,
total and input bytes. The caller's descriptor fields are retained exactly. -/
theorem compress_restart {initial : Memory} {top : Nat} (c : Core) (s : Syscall.State)
    (stateBytes block : List Byte) (total : Word)
    (running : s.exited = none) (pc : c.rip = CompressionSite.fullBlock.address)
    (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (argState : c.read .rdi = 0x401660) (argBlock : c.read .rsi = 0x401620)
    (counter : c.read .rbx = total) (size : c.read .rbp = 64)
    (stateRead : s.memory.readBytes 0x401660 32 = some stateBytes)
    (blockRead : s.memory.readBytes 0x401620 64 = some block)
    (frame : DriverMemory.Frame initial s.memory)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (next : Core) (memory : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := memory }⟩ ∧
      Ready initial top next { s with memory := memory } total
        (Driver.compressBlock (stateOf stateBytes).toState block) := by
  obtain ⟨_, final, compressed, _, _, post, returned, _, _, restored, finalFrame,
      bytes, digest, reference⟩ := CompressionCallFrame.invoke_site .fullBlock c s
    stateBytes block running frame.code pc rsp argState argBlock stateRead blockRead frame geometry stack
  have savedTotal : final.core.read .rbx = total := by
    simpa [CompressionSite.entryCore, directCallCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write] using (post.saved .rbx (by decide)).trans counter
  have savedSize : final.core.read .rbp = 64 := by
    simpa [CompressionSite.entryCore, directCallCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write] using (post.saved .rbp (by decide)).trans size
  have fresh := FullRead.restart_ready final.core savedSize
  rw [savedTotal] at fresh
  refine ⟨FullRead.restartCore final.core, final.memory, ?_, fresh, running,
    (FullRead.restart_rsp _).trans restored, finalFrame, bytes, digest, reference⟩
  simpa only [List.append_nil] using compressed.append
    (FullRead.restart final.core { s with memory := final.memory } running finalFrame.code returned)

/-- Classify the actual positive full read, including the concrete bytes copied
by its admitted syscall constructor. No favorable input stream is assumed. -/
theorem full_read_stored {before after : Syscall.State} {event : Event}
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok 64)) after) :
    ∃ block, block.length = 64 ∧ event = .read 0 block ∧ after.exited = none ∧
      X86.Ext.Stored before.memory after.memory 0x401620 block := by
  generalize resultEq : Result.ok 64 = result at effect
  cases effect with
  | @readSome _ _ _ descriptor bytes memory running opened mode matched nonempty bounded transfer accessible copied =>
    exact ⟨bytes, (Result.ok.inj resultEq).symm, rfl, running, X86.Ext.Stored.of_writeBytes copied⟩
  | readEof => have zero := Result.ok.inj resultEq; omega
  | readError => cases resultEq
  | readBadDescriptor => cases resultEq
  | readBadAddress => cases resultEq

set_option maxRecDepth 100000 in
/-- Every admitted 64-byte repeated read executes the real full-buffer path,
compresses that exact block, and reaches the next read with total increased by
64. The previous accumulated hash is read from actual H32 memory. -/
theorem Ready.read_full {initial : Memory} {top : Nat} {c : Core} {s after : Syscall.State}
    {total : Word} {state : Silmaril.Crypto.SHA256.State} {event : Event}
    (ready : Ready initial top c s total state) (flags : Word)
    (effect : Syscall.Step s (.read 0 0x401620 64) event (.returned (.ok 64)) after)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (block : List Byte) (next : Core) (memory : Memory),
      block.length = 64 ∧ event = .read 0 block ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [event]
        ⟨next, { after with memory := memory }⟩ ∧
      Ready initial top next { after with memory := memory } (total + 64)
        (Driver.compressBlock state block) := by
  obtain ⟨block, length, eventEq, running, stored⟩ := full_read_stored effect
  obtain ⟨stateBytes, stateRead, hash⟩ := ready.hash
  have nextFrame : DriverMemory.Frame initial after.memory := ready.frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have stateRead' : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  have blockRead : after.memory.readBytes 0x401620 64 = some block := by
    simpa only [Memory.readBytes, length] using stored.readWith_self
      (by rw [length]; exact ready.frame.bss_permitted .read rfl _ _ (by decide) (by decide))
  let returned := ShortReadFrame.returnedCore c (.ok 64) flags
  have trapped : X86Linux.step c s.memory = .syscall { c with rip := 0x400177 } := by
    have actual := step_of_entry (core := c) (memory := s.memory) Binary.ok_400175.1
      (by simp [ready.registers.pc, Binary.i_400175]) (ready.frame.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400175, ready.registers.pc] using actual
  have request := ready.registers.request (by decide)
  have read : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [event] ⟨returned, after⟩ :=
    .call ready.running trapped.symm request.1 effect ⟨flags, rfl⟩
  have rax : returned.read .rax = 64 := by
    simp [returned, ShortReadFrame.returnedCore, resultWord, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have r8 : returned.read .r8 = 0 := ready.registers.filled
  have rbp : returned.read .rbp = 64 := ready.registers.blockSize
  have toCall := FullReadRepeat.to_call returned after running nextFrame.code rfl rax r8 rbp
  have callRsp : (FullRead.callCore returned 0 64).read .rsp = BitVec.ofNat 64 (top - 32) := by
    simpa [FullRead.callCore, ReadAdvance.countCore, returned, ShortReadFrame.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using ready.rsp
  have callTotal : (FullRead.callCore returned 0 64).read .rbx = total + 64 := by
    simpa [FullRead.callCore, ReadAdvance.countCore, returned, ShortReadFrame.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using
        congrArg (· + (64 : Word)) ready.registers.total
  have callSize : (FullRead.callCore returned 0 64).read .rbp = 64 := rbp
  obtain ⟨next, memory, compressed, fresh⟩ := compress_restart
    (FullRead.callCore returned 0 64) after stateBytes block (total + 64) running rfl callRsp
      rfl rfl callTotal callSize stateRead' blockRead nextFrame geometry stack
  rw [hash] at fresh
  exact ⟨block, next, memory, length, eventEq, by
    simpa only [List.append_nil] using ((Machine.Trace.Runs.single read).append toCall).append compressed,
    fresh⟩

end Silmaril.Process.CLI.Sha256Cli.FullBlockIteration
