module

public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.ShortReadBranches
public import Silmaril.Process.CLI.Sha256Cli.ShortReadTransfer

/-! # The short-read invariant with symbolic source memory and stack pointer

Positive read/counter steps are parameterized independently of the eventual
compressor frame. No fixed memory₀/sp, desired output or completion premise
occurs here; deeper readable-stack and separation obligations remain open.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ShortReadFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

set_option maxRecDepth 10000

structure Invariant (initial : Memory) (stack : Word)
    (c : Core) (s : Syscall.State) (message : List Byte) (fill : Nat) : Prop where
  short : message.length < 56
  cursor : fill ≤ message.length
  ready : ShortRead.Ready c fill (BitVec.ofNat 64 fill)
  input : ShortReadTransfer.InputAt s message fill
  running : s.exited = none
  copied : s.memory.readBytes 0x401620 fill = some (message.take fill)
  initialH : s.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes
  rsp : c.read .rsp = stack
  frame : DriverMemory.Frame initial s.memory

theorem Invariant.code {initial : Memory} {stack : Word} {c : Core} {s : Syscall.State}
    {message : List Byte} {fill : Nat} (invariant : Invariant initial stack c s message fill) :
    Output.Intact s.memory := invariant.frame.code

theorem Invariant.readable {initial : Memory} {stack : Word} {c : Core} {s : Syscall.State}
    {message : List Byte} {fill : Nat} (invariant : Invariant initial stack c s message fill) :
    s.memory.Permitted .read 0x401620 64 :=
  invariant.frame.bss_permitted .read rfl _ _ (by decide) (by decide)

def returnedCore (c : Core) (result : Result) (flags : Word) : Core :=
  ((({ c with rip := 0x400177 }).write .rax (resultWord result)).write .rcx 0x400177).write .r11 flags

theorem read_code {before after : Syscall.State} {fill count : Nat} {event : Event} {result : Result}
    (code : Output.Intact before.memory)
    (effect : Syscall.Step before (.read 0 (0x401620 + fill) count) event (.returned result) after) :
    Output.Intact after.memory := by
  intro entry member
  have bound := Output.code_end entry member
  exact (X86.Memory.readWith_writesOnly effect.read_memory_frame .execute entry.address
    entry.bytes.length (Or.inl (by omega))).trans (code entry member)

theorem Invariant.after_success {initial : Memory} {stack : Word} {c : Core} {s after : Syscall.State} {message : List Byte}
    {fill amount : Nat} {event : Event} (invariant : Invariant initial stack c s message fill)
    (positive : 0 < amount) (flags : Word)
    (effect : Syscall.Step s (.read 0 (0x401620 + fill) (64 - fill)) event
      (.returned (.ok amount)) after) :
    amount ≤ message.length - fill ∧ event = .read 0 ((message.drop fill).take amount) ∧
      Proc.Runs X86Linux.isa Env.linux ⟨returnedCore c (.ok amount) flags, after⟩ []
        ⟨ShortRead.nextCore (returnedCore c (.ok amount) flags) fill amount, after⟩ ∧
      Invariant initial stack (ShortRead.nextCore (returnedCore c (.ok amount) flags) fill amount)
        after message (fill + amount) := by
  obtain ⟨fits, eventEq, input, running, copied, stored⟩ := ShortReadTransfer.successful_chunk
    invariant.short invariant.cursor invariant.input invariant.copied invariant.readable positive effect
  have nextBound : fill + amount < 56 := by have := invariant.short; have := invariant.cursor; omega
  have code := read_code invariant.code effect
  have rax : (returnedCore c (.ok amount) flags).read .rax = BitVec.ofNat 64 amount := by
    simp [returnedCore, X86.State.read, X86.State.write, Machine.RegisterFile.write, resultWord]
  have r8 : (returnedCore c (.ok amount) flags).read .r8 = BitVec.ofNat 64 fill := by
    change c.read .r8 = _
    exact invariant.ready.filled
  have rbp : (returnedCore c (.ok amount) flags).read .rbp = 64 := by
    change c.read .rbp = _
    exact invariant.ready.blockSize
  have total : (returnedCore c (.ok amount) flags).read .rbx = BitVec.ofNat 64 fill := by
    change c.read .rbx = _
    exact invariant.ready.total
  have ready : ShortRead.Ready (ShortRead.nextCore (returnedCore c (.ok amount) flags) fill amount)
      (fill + amount) (BitVec.ofNat 64 (fill + amount)) := by
    have ready := ShortRead.next_ready (returnedCore c (.ok amount) flags) fill amount rbp
    simpa only [total, BitVec.ofNat_add_ofNat] using ready
  have chunkLength : ((message.drop fill).take amount).length = amount := by
    simp only [List.length_take, List.length_drop, Nat.min_eq_left fits]
  have state : after.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes := by
    exact (stored.readWith_disjoint .read 0x401660 32
      (Or.inr (by rw [chunkLength]; have := invariant.short; have := invariant.cursor; omega))).trans
        invariant.initialH
  have stepFrame : Memory.WritesWithin s.memory after.memory DriverMemory.Above := stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega)
  refine ⟨fits, eventEq, ShortReadBranches.positive_loop _ _ _ _ positive nextBound running code
    rfl rax r8 rbp, ?_⟩
  exact ⟨invariant.short, by omega, ready, input, running, copied, state,
    by rw [ShortRead.next_rsp]; change c.read .rsp = _; exact invariant.rsp,
    invariant.frame.trans stepFrame⟩


/-- The actual repeated syscall plus its thirteen counter/branch retirements
preserves the symbolic invariant for every admitted positive read and R11. -/
theorem Invariant.successful_read {initial : Memory} {stack : Word} {c : Core}
    {s after : Syscall.State} {message : List Byte} {fill amount : Nat} {event : Event}
    (invariant : Invariant initial stack c s message fill) (positive : 0 < amount) (flags : Word)
    (effect : Syscall.Step s (.read 0 (0x401620 + fill) (64 - fill)) event
      (.returned (.ok amount)) after) :
    amount ≤ message.length - fill ∧ event = .read 0 ((message.drop fill).take amount) ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [event]
        ⟨ShortRead.nextCore (returnedCore c (.ok amount) flags) fill amount, after⟩ ∧
      Invariant initial stack (ShortRead.nextCore (returnedCore c (.ok amount) flags) fill amount)
        after message (fill + amount) := by
  have trapped : X86Linux.step c s.memory = .syscall { c with rip := 0x400177 } := by
    have actual := step_of_entry (core := c) (memory := s.memory) Binary.ok_400175.1
      (by simp [invariant.ready.pc, Binary.i_400175]) (invariant.code _ (by simp [Binary.transcript]))
    simpa [Entry.denote, Binary.i_400175, invariant.ready.pc] using actual
  have request := invariant.ready.request (by have := invariant.short; have := invariant.cursor; omega)
  have called : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [event]
      ⟨returnedCore c (.ok amount) flags, after⟩ :=
    .call invariant.running trapped.symm request.1 effect ⟨flags, rfl⟩
  obtain ⟨fits, eventEq, body, next⟩ := invariant.after_success positive flags effect
  exact ⟨fits, eventEq, by simpa using (Machine.Trace.Runs.single called).append body, next⟩

end Silmaril.Process.CLI.Sha256Cli.ShortReadFrame
