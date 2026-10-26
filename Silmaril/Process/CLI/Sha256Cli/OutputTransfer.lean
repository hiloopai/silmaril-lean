module

public import Silmaril.Process.CLI.Sha256Cli.Output

/-! # The actual write syscall at every unfinished output offset

The checked syscall consumes the canonical buffer's remaining suffix. Zero
and short writes, and errors, preserve the existing output ledger. These are
single-syscall results; retry instructions, loop termination and a universal
whole-driver contract remain separate obligations.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.OutputTransfer

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def address (off : Fin 65) : Nat := 0x4015c0 + off.val

def remaining (off : Fin 65) : Nat := 65 - off.val

def writeRequest (off : Fin 65) : Request := .write 1 (address off) (remaining off)

def accepted (message : List Byte) (off : Fin 65) (count : Nat) : List Byte :=
  ((Sha256.expected message).drop off.val).take count

/-- The real write-site registers, including the source's offset and size. -/
def requestCore (c : Core) (off : Fin 65) : Core :=
  { ((((((c.write .rax 1).write .rdi 1).write .rsi (BitVec.ofNat 64 (address off))).write
      .rdx (BitVec.ofNat 64 (remaining off))).write .r8 (BitVec.ofNat 64 off.val)).write .r9 65)
      with rip := 0x4002a9 }

def trappedCore (c : Core) (off : Fin 65) : Core :=
  { requestCore c off with rip := 0x4002ab }

def replyCore (c : Core) (off : Fin 65) (result : Result) (flags : Word) : Core :=
  (((trappedCore c off).write .rax (resultWord result)).write .rcx
    (trappedCore c off).rip).write .r11 flags

def writtenState (before : Syscall.State) (descriptor : Descriptor)
    (message : List Byte) (off : Fin 65) (count : Nat) : Syscall.State :=
  before.setDescriptor 1
    { descriptor with output := descriptor.output ++ accepted message off count }

theorem remaining_positive (off : Fin 65) : 0 < remaining off := by
  have := off.isLt
  dsimp [remaining]
  omega

theorem request_at (c : Core) (off : Fin 65) :
    X86Linux.request (trappedCore c off) = some (writeRequest off) := by
  have a : address off < 2 ^ 64 := by have := off.isLt; dsimp [address]; omega
  have n : remaining off < 2 ^ 64 := by dsimp [remaining]; omega
  simp [trappedCore, requestCore, X86Linux.request, X86Linux.readNumber,
    X86Linux.writeNumber, X86.State.read, X86.State.write, Machine.RegisterFile.write,
    BitVec.toNat_ofNat, writeRequest]
  exact ⟨a, n⟩

/-- A read of the canonical buffer supplies exactly the requested suffix. -/
theorem tail_read {memory : Memory} {message : List Byte}
    (answer : memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (off : Fin 65) :
    memory.readBytes (address off) (remaining off) = some ((Sha256.expected message).drop off.val) := by
  have take : ((Sha256.expected message).drop off.val).take (remaining off) =
      (Sha256.expected message).drop off.val :=
    List.take_of_length_le (by simp [remaining])
  have sub := Memory.readBytes_sub_range answer (offset := off.val) (len := remaining off)
    off.isLt (by have := off.isLt; dsimp [remaining]; omega)
  simpa only [address, take] using sub

theorem accepted_length {message : List Byte} {off : Fin 65} {count : Nat}
    (fits : count ≤ remaining off) : (accepted message off count).length = count := by
  simp only [accepted, List.length_take, List.length_drop, Sha256.expected_length]
  exact Nat.min_eq_left fits

/-- Every admitted successful return, including zero, accepts these exact
bytes. The result does not rely on a favorable choice of write chunking. -/
theorem successful_event {before after : Syscall.State} {message : List Byte}
    {off : Fin 65} {count : Nat} {event : Event}
    (answer : before.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (step : Syscall.Step before (writeRequest off) event (.returned (.ok count)) after) :
    event = .write 1 (accepted message off count) := by
  have tail := tail_read answer off
  change Syscall.Step before (.write 1 (address off) (remaining off)) event
    (.returned (.ok count)) after at step
  cases step with
  | writeSome _ _ _ loaded _ _ =>
    have same := Option.some.inj (loaded.symm.trans tail)
    exact congrArg (fun bytes => Event.write 1 (bytes.take count)) same

/-- Successful syscall observations discharge the abstract ledger's accepted
byte premise; write memory is retained by the shared syscall contract. -/
theorem successful_ledger {before after : Syscall.State} {message : List Byte}
    {off : Fin 65} {count : Nat} {event : Event} {events : List Event}
    (answer : before.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message events off.val)
    (step : Syscall.Step before (writeRequest off) event (.returned (.ok count)) after) :
    Driver.OutputInv message (events ++ [event]) (off.val + count) ∧
      after.memory = before.memory := by
  obtain ⟨_, _, _, fits⟩ := step.write_success
  refine ⟨?_, step.write_memory_preserved⟩
  rw [successful_event answer step]
  exact accounted.write count fits

/-- Per-syscall refinement to the shared prefix contract. This gives no
retry-loop or successful-exit theorem. -/
theorem prefix_after_success {before after : Syscall.State} {input : ProcInput}
    {message : List Byte} {off : Fin 65} {count : Nat} {event : Event} {events : List Event}
    (answer : before.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message events off.val)
    (finite : input.stdin = .ofList message)
    (step : Syscall.Step before (writeRequest off) event (.returned (.ok count)) after) :
    Sha256.PrefixOk input (events ++ [event]) :=
  (successful_ledger answer accounted step).1.prefix finite

/-- Once accepted output reaches65, this ledger has the complete answer.
The statement concerns observations, without claiming the machine exits. -/
theorem answer_if_complete {before after : Syscall.State} {input : ProcInput}
    {message : List Byte} {off : Fin 65} {count : Nat} {event : Event} {events : List Event}
    (answer : before.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message events off.val)
    (finite : input.stdin = .ofList message) (complete : off.val + count = 65)
    (step : Syscall.Step before (writeRequest off) event (.returned (.ok count)) after) :
    Sha256.Success input (events ++ [event]) := by
  have ledger := (successful_ledger answer accounted step).1
  rw [complete] at ledger
  exact ledger.success finite

theorem error_event {before after : Syscall.State} {off : Fin 65}
    {event : Event} {errno : Errno}
    (step : Syscall.Step before (writeRequest off) event (.returned (.error errno)) after) :
    event = .error (writeRequest off) errno := by
  change Syscall.Step before (.write 1 (address off) (remaining off)) event
    (.returned (.error errno)) after at step
  cases step <;> rfl

/-- All write-error profiles preserve the accepted-byte ledger and memory.
This includes descriptor and address failures, not just an I/O error. -/
theorem error_ledger {before after : Syscall.State} {message : List Byte}
    {off : Fin 65} {event : Event} {errno : Errno} {events : List Event}
    (accounted : Driver.OutputInv message events off.val)
    (step : Syscall.Step before (writeRequest off) event (.returned (.error errno)) after) :
    Driver.OutputInv message (events ++ [event]) off.val ∧ after.memory = before.memory := by
  refine ⟨?_, step.write_memory_preserved⟩
  rw [error_event step]
  exact accounted.error (writeRequest off) errno

set_option maxRecDepth 10000 in
/-- The real checked syscall instruction binds any admitted write transition
to the process model. R11's permitted return value remains arbitrary. -/
theorem call_of_step (c : Core) (off : Fin 65) (flags : Word)
    {before after : Syscall.State} {result : Result} {event : Event}
    (running : before.exited = none) (intact : Output.Intact before.memory)
    (effect : Syscall.Step before (writeRequest off) event (.returned result) after) :
    Proc.Step X86Linux.isa Env.linux (⟨requestCore c off, before⟩ : Output.PS) [event]
      ⟨replyCore c off result flags, after⟩ := by
  apply Proc.Step.call (q := writeRequest off) (r := result) running
  · exact (step_of_entry Binary.ok_4002a9.1 rfl
      (intact _ (by simp [Binary.transcript]))).symm
  · exact request_at c off
  · exact effect
  · exact ⟨flags, rfl⟩

/-- Every permitted transfer length, including zero and the full remaining
suffix, has a real process step with its exact accepted-byte accounting. -/
theorem write_some (c : Core) (off : Fin 65) (flags : Word) (before : Syscall.State)
    {message : List Byte} {events : List Event} (count : Nat)
    (running : before.exited = none) (intact : Output.Intact before.memory)
    {descriptor : Descriptor} (stdoutOpen : before.descriptors 1 = some descriptor)
    (writable : descriptor.writable = true)
    (answer : before.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message events off.val) (fits : count ≤ remaining off) :
    Proc.Step X86Linux.isa Env.linux (⟨requestCore c off, before⟩ : Output.PS)
        [.write 1 (accepted message off count)]
        ⟨replyCore c off (.ok count) flags, writtenState before descriptor message off count⟩ ∧
      Driver.OutputInv message (events ++ [.write 1 (accepted message off count)])
        (off.val + count) ∧
      (writtenState before descriptor message off count).memory = before.memory := by
  have transfer : count ≤ maxTransfer :=
    (fits.trans (Nat.sub_le 65 off.val)).trans (by decide)
  have effect : Syscall.Step before (writeRequest off) (.write 1 (accepted message off count))
      (.returned (.ok count)) (writtenState before descriptor message off count) := by
    simpa only [writeRequest, writtenState, accepted] using
      (Syscall.Step.writeSome (written := count) running stdoutOpen writable
        (tail_read answer off) fits transfer)
  have ledger := successful_ledger answer accounted effect
  exact ⟨call_of_step c off flags running intact effect, ledger⟩

/-- An admitted I/O error at this actual write site changes neither the
accepted offset nor memory. There is no promise to retry or make progress. -/
theorem write_error (c : Core) (off : Fin 65) (flags : Word) (before : Syscall.State)
    {message : List Byte} {events : List Event} (errno : Errno)
    (running : before.exited = none) (intact : Output.Intact before.memory)
    {descriptor : Descriptor} (stdoutOpen : before.descriptors 1 = some descriptor)
    (writable : descriptor.writable = true)
    (answer : before.memory.readBytes 0x4015c0 65 = some (Sha256.expected message))
    (accounted : Driver.OutputInv message events off.val) :
    Proc.Step X86Linux.isa Env.linux (⟨requestCore c off, before⟩ : Output.PS)
        [.error (writeRequest off) errno] ⟨replyCore c off (.error errno) flags, before⟩ ∧
      Driver.OutputInv message (events ++ [.error (writeRequest off) errno]) off.val := by
  have accessible : before.memory.Permitted .read (address off) (remaining off) :=
    Memory.readWith_permitted (tail_read answer off)
  have effect : Syscall.Step before (writeRequest off) (.error (writeRequest off) errno)
      (.returned (.error errno)) before :=
    Syscall.Step.writeError errno running stdoutOpen writable accessible
  exact ⟨call_of_step c off flags running intact effect, (error_ledger accounted effect).1⟩

end Silmaril.Process.CLI.Sha256Cli.OutputTransfer
