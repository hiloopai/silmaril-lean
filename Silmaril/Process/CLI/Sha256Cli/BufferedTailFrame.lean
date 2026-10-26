module

public import Silmaril.Process.CLI.Sha256Cli.FullBlockIteration
public import Silmaril.Process.CLI.Sha256Cli.ShortReadInit

/-! # Actual positive reads leaving a buffer below64

Buffer fill, descriptor cursor, modular whole-input counter and accumulated
H32 are independent. The copied bytes come from actual read constructors.
This interface includes tails56..63 without changing the existing short API.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.BufferedTailFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

structure Ready (initial : Memory) (stack : Word) (c : Core) (s : Syscall.State)
    (tail : List Byte) (total : Word) (state : Silmaril.Crypto.SHA256.State) : Prop where
  room : tail.length < 64
  registers : ShortRead.Ready c tail.length total
  running : s.exited = none
  rsp : c.read .rsp = stack
  frame : DriverMemory.Frame initial s.memory
  copied : s.memory.readBytes 0x401620 tail.length = some tail
  hash : ∃ bytes, s.memory.readBytes 0x401660 32 = some bytes ∧ (stateOf bytes).toState = state

/-- Exact bytes and stores from any admitted positive read, independently of
the natural stream cursor or previous completed compression blocks. -/
theorem read_stored {before after : Syscall.State} {event : Event} {fill amount : Nat}
    (positive : 0 < amount)
    (effect : Syscall.Step before (.read 0 (0x401620 + fill) (64 - fill))
      event (.returned (.ok amount)) after) :
    ∃ chunk, chunk.length = amount ∧ event = .read 0 chunk ∧ after.exited = none ∧
      X86.Ext.Stored before.memory after.memory (0x401620 + fill) chunk := by
  generalize requestCount : 64 - fill = requested at effect
  generalize resultEq : Result.ok amount = result at effect
  cases effect with
  | @readSome _ _ _ descriptor bytes memory running opened mode matched nonempty bounded transfer accessible copied =>
    exact ⟨bytes, (Result.ok.inj resultEq).symm, rfl, running, X86.Ext.Stored.of_writeBytes copied⟩
  | readEof => have zero := Result.ok.inj resultEq; omega
  | readZero => have zero := Result.ok.inj resultEq; omega
  | readError => cases resultEq
  | readBadDescriptor => cases resultEq
  | readBadAddress => cases resultEq

set_option maxRecDepth 100000

/-- Actual repeated syscall and counter/branch instructions append the bytes
actually copied. The bound is on buffer fill, not the whole message length. -/
theorem Ready.read {initial : Memory} {stack : Word} {c : Core} {before after : Syscall.State}
    {tail : List Byte} {total : Word} {state : Silmaril.Crypto.SHA256.State}
    {event : Event} {amount : Nat}
    (ready : Ready initial stack c before tail total state)
    (positive : 0 < amount) (room : tail.length + amount < 64) (flags : Word)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok amount)) after) :
    ∃ (chunk : List Byte) (next : Core),
      chunk.length = amount ∧ event = .read 0 chunk ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [event] ⟨next, after⟩ ∧
      Ready initial stack next after (tail ++ chunk) (total + BitVec.ofNat 64 amount) state := by
  obtain ⟨chunk, length, eventEq, running, stored⟩ := read_stored positive effect
  have nextFrame := ready.frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have headRead := (stored.readWith_disjoint .read 0x401620 tail.length (Or.inl (by omega))).trans ready.copied
  have tailRead : after.memory.readBytes (0x401620 + tail.length) chunk.length = some chunk :=
    stored.readWith_self (ready.frame.bss_permitted .read rfl _ _ (by omega) (by omega))
  have copied : after.memory.readBytes 0x401620 (tail ++ chunk).length = some (tail ++ chunk) := by
    simpa only [List.length_append] using Memory.readBytes_append headRead tailRead
  obtain ⟨bytes, observed, value⟩ := ready.hash
  have observed' : after.memory.readBytes 0x401660 32 = some bytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans observed
  let returned := ShortReadFrame.returnedCore c (.ok amount) flags
  have trapped : X86Linux.step c before.memory = .syscall { c with rip := 0x400177 } := by
    have actual := step_of_entry (core := c) (memory := before.memory) Binary.ok_400175.1
      (by simp [ready.registers.pc, Binary.i_400175]) (ready.frame.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400175, ready.registers.pc] using actual
  have read : Proc.Step X86Linux.isa Env.linux (⟨c, before⟩ : Output.PS) [event] ⟨returned, after⟩ :=
    .call ready.running trapped.symm (ready.registers.request_below64 ready.room).1 effect ⟨flags, rfl⟩
  have rax : returned.read .rax = BitVec.ofNat 64 amount := by
    simp [returned, ShortReadFrame.returnedCore, resultWord, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have r8 : returned.read .r8 = BitVec.ofNat 64 tail.length := ready.registers.filled
  have rbp : returned.read .rbp = 64 := ready.registers.blockSize
  have body := ShortReadBranches.positive_loop_below64 returned after tail.length amount
    positive room running nextFrame.code rfl rax r8 rbp
  have registers := ShortRead.next_ready returned tail.length amount rbp
  have count : returned.read .rbx = total := ready.registers.total
  rw [count] at registers
  refine ⟨chunk, ShortRead.nextCore returned tail.length amount, length, eventEq, ?_, ?_⟩
  · simpa only [List.append_nil] using (Machine.Trace.Runs.single read).append body
  · exact ⟨by simpa only [List.length_append, length] using room,
      by simpa only [List.length_append, length] using registers, running,
      (ShortRead.next_rsp _ _ _).trans ready.rsp, nextFrame, copied, bytes, observed', value⟩

/-- The optimized first syscall/setup also admits every positive count below64.
Its real setup resets the total to zero; subsequent buffered reads retain the
accumulated modular total instead. No input bytes are preinstalled. -/
theorem first_read {initial : Memory} {before after : Syscall.State}
    {stateBytes : List Byte} {amount : Nat} {event : Event}
    (c : Core) (flags : Word) (positive : 0 < amount) (room : amount < 64)
    (frame : DriverMemory.Frame initial before.memory)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (running : before.exited = none) (pc : c.rip = 0x400159)
    (request : X86Linux.request { c with rip := 0x40015b } = some (.read 0 0x401620 64))
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok amount)) after) :
    ∃ (tail : List Byte) (next : Core),
      tail.length = amount ∧ event = .read 0 tail ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [event] ⟨next, after⟩ ∧
      Ready initial (c.read .rsp) next after tail (BitVec.ofNat 64 amount) (stateOf stateBytes).toState := by
  obtain ⟨tail, length, eventEq, afterRunning, stored⟩ := read_stored (fill := 0) positive effect
  have nextFrame := frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have copied : after.memory.readBytes 0x401620 tail.length = some tail :=
    stored.readWith_self (frame.bss_permitted .read rfl _ _ (by decide) (by omega))
  have observed : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  let returned := ShortReadInit.returnedCore c amount flags
  have trapped : X86Linux.step c before.memory = .syscall { c with rip := 0x40015b } := by
    have actual := step_of_entry (core := c) (memory := before.memory) Binary.ok_400159.1
      (by simp [pc, Binary.i_400159]) (frame.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400159, pc] using actual
  have read : Proc.Step X86Linux.isa Env.linux (⟨c, before⟩ : Output.PS) [event] ⟨returned, after⟩ :=
    .call running trapped.symm request effect ⟨flags, rfl⟩
  have rax : returned.read .rax = BitVec.ofNat 64 amount := by
    simp [returned, ShortReadInit.returnedCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have body := ShortReadBranches.first_positive_below64 returned after amount positive room
    afterRunning nextFrame.code rfl rax
  have registers : ShortRead.Ready (ShortReadBranches.firstNextCore returned amount) tail.length
      (BitVec.ofNat 64 amount) := by
    simpa [ShortReadBranches.firstNextCore, ShortReadBranches.initialCore, length,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using
        ShortRead.next_ready (ShortReadBranches.initialCore returned) 0 amount (by rfl)
  exact ⟨tail, ShortReadBranches.firstNextCore returned amount, length, eventEq,
    by simpa only [List.append_nil] using (Machine.Trace.Runs.single read).append body,
    by omega, registers, afterRunning, by
      simp [ShortReadBranches.firstNextCore, ShortReadBranches.initialCore, returned,
        ShortReadInit.returnedCore, ShortRead.nextCore, X86.State.read, X86.State.write,
        Machine.RegisterFile.write], nextFrame, copied, stateBytes, observed, rfl⟩

/-- A completed full-block iteration is already a fresh empty-buffer cut.
The accumulated state and whole-input total are retained without resetting H0. -/
theorem of_full {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {total : Word} {state : Silmaril.Crypto.SHA256.State}
    (ready : FullBlockIteration.Ready initial top c s total state) :
    Ready initial (BitVec.ofNat 64 (top - 32)) c s [] total state := by
  refine ⟨by decide, ready.registers, ready.running, ready.rsp, ready.frame, ?_, ready.hash⟩
  exact Memory.readWith_eq s.memory .read 0x401620 []
    (ready.frame.bss_permitted .read rfl _ _ (by decide) (by decide)) (by simp)

end Silmaril.Process.CLI.Sha256Cli.BufferedTailFrame
