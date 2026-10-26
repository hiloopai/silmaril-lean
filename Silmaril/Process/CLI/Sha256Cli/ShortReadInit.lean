module

public import Silmaril.Process.CLI.Sha256Cli.ShortReadFrame

/-! # Actual first-read initialization of the dynamic loop invariant

Every admitted positive first read is classified against the supplied finite
stream, then the seventeen real setup/counter instructions initialize the
loop invariant. The source memory and caller stack word remain parameters.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ShortReadInit

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

set_option maxRecDepth 10000

def returnedCore (c : Core) (amount : Nat) (flags : Word) : Core :=
  ((({ c with rip := 0x40015b }).write .rax (BitVec.ofNat 64 amount)).write
    .rcx 0x40015b).write .r11 flags

/-- Initialize the invariant from an actual successful read effect and the
actual returned register cut point. No input bytes are preinstalled. -/
theorem after_first_success {initial : Memory} {stack : Word}
    {before after : Syscall.State} {message : List Byte} {amount : Nat} {event : Event}
    (c : Core) (short : message.length < 56)
    (frame : DriverMemory.Frame initial before.memory)
    (input : ShortReadTransfer.InputAt before message 0)
    (initialH : before.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes)
    (positive : 0 < amount) (pc : c.rip = 0x40015b)
    (rax : c.read .rax = BitVec.ofNat 64 amount) (rsp : c.read .rsp = stack)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok amount)) after) :
    amount ≤ message.length ∧ event = .read 0 (message.take amount) ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, after⟩ []
        ⟨ShortReadBranches.firstNextCore c amount, after⟩ ∧
      ShortReadFrame.Invariant initial stack (ShortReadBranches.firstNextCore c amount)
        after message amount := by
  have emptyRead : before.memory.readBytes 0x401620 0 = some (message.take 0) := by
    apply Memory.readWith_eq before.memory .read 0x401620 []
      (frame.bss_permitted .read rfl _ _ (by decide) (by decide))
    intro index bound
    simp at bound
  obtain ⟨fits, eventEq, inputAfter, running, copied, stored⟩ :=
    ShortReadTransfer.successful_chunk short (by omega) input emptyRead
      (frame.bss_permitted .read rfl _ _ (by decide) (by decide)) positive effect
  have nextFrame : DriverMemory.Frame initial after.memory := frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have ready : ShortRead.Ready (ShortReadBranches.firstNextCore c amount) amount
      (BitVec.ofNat 64 amount) := by
    simpa [ShortReadBranches.firstNextCore, ShortReadBranches.initialCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using
      ShortRead.next_ready (ShortReadBranches.initialCore c) 0 amount (by rfl)
  have state : after.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes := by
    have disjoint : 0x401620 + ((message.drop 0).take amount).length ≤ 0x401660 := by
      simp only [List.drop_zero, List.length_take]
      omega
    exact (stored.readWith_disjoint .read _ _ (Or.inr disjoint)).trans initialH
  refine ⟨by simpa using fits, by simpa using eventEq,
    ShortReadBranches.first_positive c after amount positive (by omega)
      running nextFrame.code pc rax, ?_⟩
  exact ⟨short, by omega, ready, by simpa using inputAfter, running,
    by simpa using copied, state,
    by simpa [ShortReadBranches.firstNextCore, ShortReadBranches.initialCore,
      ShortRead.nextCore, X86.State.read, X86.State.write, Machine.RegisterFile.write] using rsp,
    nextFrame⟩

/-- The real first syscall plus its seventeen retired instructions initialize
the dynamic invariant for every positive admitted transfer and resumed R11. -/
theorem first_read {initial : Memory} {before after : Syscall.State}
    {message : List Byte} {amount : Nat} {event : Event}
    (c : Core) (flags : Word) (short : message.length < 56)
    (frame : DriverMemory.Frame initial before.memory)
    (input : ShortReadTransfer.InputAt before message 0)
    (initialH : before.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes)
    (running : before.exited = none) (positive : 0 < amount)
    (pc : c.rip = 0x400159)
    (request : X86Linux.request { c with rip := 0x40015b } = some (.read 0 0x401620 64))
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok amount)) after) :
    amount ≤ message.length ∧ event = .read 0 (message.take amount) ∧
      Proc.Runs X86Linux.isa Env.linux ⟨c, before⟩ [event]
        ⟨ShortReadBranches.firstNextCore (returnedCore c amount flags) amount, after⟩ ∧
      ShortReadFrame.Invariant initial (c.read .rsp)
        (ShortReadBranches.firstNextCore (returnedCore c amount flags) amount) after message amount := by
  have actual := step_of_entry (core := c) (memory := before.memory) Binary.ok_400159.1
    (by simp [pc, Binary.i_400159]) (frame.code _ (by simp [Binary.transcript]))
  have trapped : X86Linux.step c before.memory = .syscall { c with rip := 0x40015b } := by
    simpa [Entry.denote, Binary.i_400159, pc] using actual
  have called : Proc.Step X86Linux.isa Env.linux (⟨c, before⟩ : Output.PS) [event]
      ⟨returnedCore c amount flags, after⟩ :=
    .call running trapped.symm request effect ⟨flags, rfl⟩
  obtain ⟨fits, eventEq, body, invariant⟩ := after_first_success (initial := initial) (stack := c.read .rsp)
    (returnedCore c amount flags) short frame input initialH positive rfl
    (by simp [returnedCore, X86.State.read, X86.State.write, Machine.RegisterFile.write])
    (by simp [returnedCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]) effect
  exact ⟨fits, eventEq, by simpa using (Machine.Trace.Runs.single called).append body, invariant⟩


/-- A real arbitrary Loaded launch reaches a cut point from which every
admitted positive first read initializes the symbolic loop invariant. The
choice/existence of a positive transfer is not assumed by the launch claim. -/
theorem from_loaded (input : ProcInput) (initial : Core) (s : Syscall.State)
    (message : List Byte) (short : message.length < 56)
    (loaded : Loaded image input initial s.memory)
    (stdin : ShortReadTransfer.InputAt s message 0)
    (apart : 0x4005c0 ≤ (initial.read .rsp).toNat - 24)
    (running : s.exited = none) :
    ∃ before : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨initial, s⟩ []
        ⟨LoadedStartup.readCore initial (initial.read .rsp).toNat, { s with memory := before }⟩ ∧
      ∀ (after : Syscall.State) (amount : Nat) (event : Event) (flags : Word),
        0 < amount →
        Syscall.Step { s with memory := before } (.read 0 0x401620 64)
          event (.returned (.ok amount)) after →
        amount ≤ message.length ∧ event = .read 0 (message.take amount) ∧
        Proc.Runs X86Linux.isa Env.linux ⟨initial, s⟩ [event]
          ⟨ShortReadBranches.firstNextCore
            (returnedCore (LoadedStartup.readCore initial (initial.read .rsp).toNat) amount flags)
            amount, after⟩ ∧
        ShortReadFrame.Invariant s.memory (BitVec.ofNat 64 ((initial.read .rsp).toNat - 32))
          (ShortReadBranches.firstNextCore
            (returnedCore (LoadedStartup.readCore initial (initial.read .rsp).toNat) amount flags)
            amount) after message amount := by
  obtain ⟨before, launch, bytes, frame⟩ := DriverMemory.launch_read input initial s loaded apart running
  refine ⟨before, launch, ?_⟩
  intro after amount event flags positive effect
  obtain ⟨fits, eventEq, body, invariant⟩ := first_read (initial := s.memory) (before := { s with memory := before })
    (LoadedStartup.readCore initial (initial.read .rsp).toNat) flags short frame stdin bytes
    running positive rfl (LoadedStartup.read_request initial (initial.read .rsp).toNat) effect
  have stack := (LoadedStartup.read_arguments initial (initial.read .rsp).toNat).2.2.2.2
  exact ⟨fits, eventEq, by simpa using launch.append body, by simpa only [stack] using invariant⟩

end Silmaril.Process.CLI.Sha256Cli.ShortReadInit
