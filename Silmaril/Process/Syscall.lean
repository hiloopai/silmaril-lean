module

public import Silmaril.Process.Memory

/-! # Explicit byte-stream syscall contracts

These nondeterministic returning transitions are an OS interface contract, not
a proof of a kernel implementation. Descriptors represent private byte streams:
no O_DIRECT, device-specific effects, shared offsets, or external descriptor
mutation. Successful writes record OS-accepted bytes, without a durability claim.
Signals are excluded; in particular a Linux realization that admits EPIPE must
inherit SIGPIPE ignored or blocked. No constructor promises an OS call returns.

Linux references: v6.12 `include/uapi/asm-generic/unistd.h`; Linux man-pages
`read(2)`, `write(2)`, and `_exit(2)`. Errors may clobber the entire requested
read buffer and consume a bounded input prefix. Neither is subsequently usable.
-/

@[expose] public section

namespace Silmaril.Process.Syscall

/-- Raw Linux errors are the negative integers -4095 through -1. -/
structure Errno where
  value : Nat
  positive : 0 < value
  bounded : value ≤ 4095
  deriving DecidableEq

def Errno.badDescriptor : Errno := ⟨9, by decide, by decide⟩
def Errno.badAddress : Errno := ⟨14, by decide, by decide⟩

inductive Request where
  | read (fd address count : Nat)
  | write (fd address count : Nat)
  | exit (status : Nat)
  deriving DecidableEq, Repr

inductive Result where
  | ok (count : Nat)
  | error (errno : Errno)
  deriving DecidableEq

inductive Reply where
  | returned (result : Result)
  | exited (status : Nat)
  deriving DecidableEq

inductive Event where
  | read (fd : Nat) (bytes : List Byte)
  | write (fd : Nat) (bytes : List Byte)
  | error (request : Request) (errno : Errno)
  | exit (status : Nat)
  deriving DecidableEq

/-- Only successful write bytes contribute to the observable output stream. -/
def Event.output : Event → List Byte
  | .write _ bytes => bytes
  | _ => []

/-- An immutable finite or infinite stream. Once EOF is observed it stays EOF.
Temporary blocking is not represented by `none`; it is absence of a completed
syscall transition in the enclosing process semantics. -/
structure InputStream where
  byteAt : Nat → Option Byte
  eof_stable : ∀ first later, first ≤ later → byteAt first = none → byteAt later = none

def InputStream.ofList (bytes : List Byte) : InputStream where
  byteAt index := bytes[index]?
  eof_stable := by
    intro first later ordered eof
    have bound : bytes.length ≤ first := List.getElem?_eq_none_iff.mp eof
    exact List.getElem?_eq_none_iff.mpr (by omega)

@[simp] theorem InputStream.ofList_byteAt (bytes : List Byte) (index : Nat) :
    (InputStream.ofList bytes).byteAt index = bytes[index]? := rfl

theorem InputStream.ofList_injective : Function.Injective InputStream.ofList := by
  intro first second equal
  apply List.ext_getElem?
  intro index
  exact congrArg (fun stream : InputStream => stream.byteAt index) equal

/-- The exact bytes of a successful read, starting at the descriptor cursor. -/
def InputStream.Matches (stream : InputStream) (cursor : Nat) (bytes : List Byte) : Prop :=
  ∀ index (bound : index < bytes.length),
    stream.byteAt (cursor + index) = some bytes[index]

theorem InputStream.Matches.append {stream : InputStream} {cursor : Nat}
    {first second : List Byte} (head : stream.Matches cursor first)
    (tail : stream.Matches (cursor + first.length) second) :
    stream.Matches cursor (first ++ second) := by
  intro index bound
  by_cases left : index < first.length
  · simpa only [List.getElem_append_left left] using head index left
  · have right : index - first.length < second.length := by
      simp only [List.length_append] at bound
      omega
    have offset : cursor + first.length + (index - first.length) = cursor + index := by omega
    rw [List.getElem_append_right (by omega : first.length ≤ index)]
    simpa only [offset] using tail (index - first.length) right

theorem InputStream.Matches.left {stream : InputStream} {cursor : Nat}
    {first second : List Byte} (contents : stream.Matches cursor (first ++ second)) :
    stream.Matches cursor first := by
  intro index bound
  have byte := contents index (by simp; omega)
  rw [List.getElem_append_left bound] at byte
  exact byte

theorem InputStream.Matches.unique {stream : InputStream} {cursor : Nat}
    {first second : List Byte} (head : stream.Matches cursor first)
    (tail : stream.Matches cursor second) (length : first.length = second.length) :
    first = second := by
  apply List.ext_getElem length
  intro index firstBound secondBound
  exact Option.some.inj ((head index firstBound).symm.trans (tail index secondBound))

/-- Matching bytes and stable EOF determine the complete input, rather than
assuming that the stream was finite before the reads began. -/
theorem InputStream.eq_ofList {stream : InputStream} {bytes : List Byte}
    (contents : stream.Matches 0 bytes) (eof : stream.byteAt bytes.length = none) :
    stream = InputStream.ofList bytes := by
  have same : stream.byteAt = (InputStream.ofList bytes).byteAt := by
    funext index
    by_cases inside : index < bytes.length
    · simpa [InputStream.ofList, inside] using contents index inside
    · have endOfStream := stream.eof_stable bytes.length index (by omega) eof
      simpa [InputStream.ofList, List.getElem?_eq_none_iff.mpr (by omega : bytes.length ≤ index)]
        using endOfStream
  cases stream with
  | mk byteAt stable =>
    simp only [InputStream.ofList] at same ⊢
    cases same
    rfl

theorem InputStream.ofList_matches (bytes : List Byte) :
    (InputStream.ofList bytes).Matches 0 bytes := by
  intro index bound
  simp [InputStream.ofList, bound]

/-- Stream permissions and input stay fixed; only the cursor and output change. -/
structure Descriptor where
  readable : Bool
  writable : Bool
  input : InputStream
  cursor : Nat
  output : List Byte

structure State where
  memory : Memory
  descriptors : Nat → Option Descriptor
  exited : Option Nat

def State.setDescriptor (state : State) (fd : Nat) (descriptor : Descriptor) : State :=
  { state with descriptors := Function.update state.descriptors fd (some descriptor) }

/-- Backing storage cannot disappear when the kernel modifies a user buffer. -/
def SameBacking (before after : Memory) : Prop :=
  ∀ address, (before.bytes.get? address).isSome = (after.bytes.get? address).isSome

/-- Linux caps each read/write transfer independently of the requested count. -/
def maxTransfer : Nat := 0x7ffff000

/-- One completed call. Short positive returns, EOF, zero writes and errors are
all explicit. Waiting for a call to complete belongs to the enclosing process
semantics; this relation asserts no fairness or progress assumption. -/
inductive Step : State → Request → Event → Reply → State → Prop where
  | readSome {state : State} {fd address count : Nat} {descriptor : Descriptor}
      {bytes : List Byte} {memory : Memory}
      (running : state.exited = none) (openFd : state.descriptors fd = some descriptor)
      (readable : descriptor.readable = true)
      (input : descriptor.input.Matches descriptor.cursor bytes)
      (positive : 0 < bytes.length) (bounded : bytes.length ≤ count)
      (transferBound : bytes.length ≤ maxTransfer)
      (accessible : state.memory.Permitted .write address count)
      (copied : state.memory.writeBytes address bytes = some memory) :
      Step state (.read fd address count) (.read fd bytes) (.returned (.ok bytes.length))
        { state.setDescriptor fd { descriptor with cursor := descriptor.cursor + bytes.length }
          with memory := memory }
  | readEof {state : State} {fd address count : Nat} {descriptor : Descriptor}
      (running : state.exited = none) (openFd : state.descriptors fd = some descriptor)
      (readable : descriptor.readable = true) (eof : descriptor.input.byteAt descriptor.cursor = none)
      (accessible : state.memory.Permitted .write address count) :
      Step state (.read fd address count) (.read fd []) (.returned (.ok 0)) state
  | readZero {state : State} {fd address : Nat} {descriptor : Descriptor}
      (running : state.exited = none) (openFd : state.descriptors fd = some descriptor)
      (readable : descriptor.readable = true)
      (accessible : state.memory.Permitted .write address 0) :
      Step state (.read fd address 0) (.read fd []) (.returned (.ok 0)) state
  | readError {state : State} {fd address count consumed : Nat} {descriptor : Descriptor}
      {memory : Memory} (errno : Errno)
      (running : state.exited = none) (openFd : state.descriptors fd = some descriptor)
      (readable : descriptor.readable = true)
      (accessible : state.memory.Permitted .write address count)
      (bounded : consumed ≤ count)
      (available : ∀ index < consumed,
        (descriptor.input.byteAt (descriptor.cursor + index)).isSome = true)
      (frame : Memory.WritesOnly state.memory memory address count)
      (backed : SameBacking state.memory memory) :
      Step state (.read fd address count) (.error (.read fd address count) errno)
        (.returned (.error errno))
        { state.setDescriptor fd { descriptor with cursor := descriptor.cursor + consumed }
          with memory := memory }
  | writeSome {state : State} {fd address count written : Nat} {descriptor : Descriptor}
      {bytes : List Byte}
      (running : state.exited = none) (openFd : state.descriptors fd = some descriptor)
      (writable : descriptor.writable = true)
      (loaded : state.memory.readBytes address count = some bytes)
      (bounded : written ≤ count) (transferBound : written ≤ maxTransfer) :
      Step state (.write fd address count) (.write fd (bytes.take written))
        (.returned (.ok written))
        (state.setDescriptor fd
          { descriptor with output := descriptor.output ++ bytes.take written })
  | writeError {state : State} {fd address count : Nat} {descriptor : Descriptor}
      (errno : Errno) (running : state.exited = none)
      (openFd : state.descriptors fd = some descriptor)
      (writable : descriptor.writable = true)
      (accessible : state.memory.Permitted .read address count) :
      Step state (.write fd address count) (.error (.write fd address count) errno)
        (.returned (.error errno)) state
  | readBadDescriptor {state : State} {fd address count : Nat}
      (running : state.exited = none)
      (invalid : (state.descriptors fd).map Descriptor.readable ≠ some true) :
      Step state (.read fd address count)
        (.error (.read fd address count) Errno.badDescriptor)
        (.returned (.error Errno.badDescriptor)) state
  | writeBadDescriptor {state : State} {fd address count : Nat}
      (running : state.exited = none)
      (invalid : (state.descriptors fd).map Descriptor.writable ≠ some true) :
      Step state (.write fd address count)
        (.error (.write fd address count) Errno.badDescriptor)
        (.returned (.error Errno.badDescriptor)) state
  | readBadAddress {state : State} {fd address count : Nat}
      (running : state.exited = none)
      (invalid : ¬ state.memory.Permitted .write address count) :
      Step state (.read fd address count)
        (.error (.read fd address count) Errno.badAddress)
        (.returned (.error Errno.badAddress)) state
  | writeBadAddress {state : State} {fd address count : Nat}
      (running : state.exited = none)
      (invalid : ¬ state.memory.Permitted .read address count) :
      Step state (.write fd address count)
        (.error (.write fd address count) Errno.badAddress)
        (.returned (.error Errno.badAddress)) state
  | exit {state : State} (status : Nat) (running : state.exited = none) :
      Step state (.exit status) (.exit (status % 256)) (.exited (status % 256))
        { state with exited := some (status % 256) }

theorem Step.was_running {before after : State} {request : Request} {event : Event}
    {reply : Reply} (step : Step before request event reply after) : before.exited = none := by
  cases step <;> assumption

theorem no_step_after_exit {state : State} {status : Nat}
    (exited : state.exited = some status) {request : Request} {event : Event}
    {reply : Reply} {after : State} : ¬ Step state request event reply after := by
  intro step
  have running := step.was_running
  rw [exited] at running
  contradiction

/-- Reads cannot add externally accepted output, including their error paths. -/
theorem Step.read_output_preserved {before after : State} {fd address count : Nat}
    {event : Event} {reply : Reply}
    (step : Step before (.read fd address count) event reply after) (other : Nat) :
    (after.descriptors other).map Descriptor.output =
      (before.descriptors other).map Descriptor.output := by
  cases step <;> try rfl
  all_goals
    simp only [State.setDescriptor, Function.update_apply]
    split
    · subst other
      simp_all
    · rfl

/-- Write requests never modify user memory, even on zero or failed returns. -/
theorem Step.write_memory_preserved {before after : State} {fd address count : Nat}
    {event : Event} {reply : Reply}
    (step : Step before (.write fd address count) event reply after) :
    after.memory = before.memory := by cases step <;> rfl

/-- Even a failed read preserves every byte outside its requested buffer. -/
theorem Step.read_memory_frame {before after : State} {fd address count : Nat}
    {event : Event} {reply : Reply}
    (step : Step before (.read fd address count) event reply after) :
    Memory.WritesOnly before.memory after.memory address count := by
  cases step with
  | readSome _ _ _ _ _ bounded _ _ copied =>
    have frame := Memory.writeBytes_writesOnly copied
    refine ⟨frame.1, fun location outside => frame.2 location ?_⟩
    omega
  | readError _ _ _ _ _ _ _ frame _ => exact frame
  | _ => exact ⟨rfl, fun _ _ => rfl⟩

/-- File modes and membership are invariant; stream contents are the only
descriptor fields affected by read/write. -/
theorem Step.descriptor_modes {before after : State} {request : Request} {event : Event}
    {reply : Reply} (step : Step before request event reply after) (fd : Nat) :
    (after.descriptors fd).map (fun descriptor => (descriptor.readable, descriptor.writable)) =
      (before.descriptors fd).map (fun descriptor => (descriptor.readable, descriptor.writable)) := by
  cases step <;> try rfl
  all_goals
    simp only [State.setDescriptor, Function.update_apply]
    split
    · subst fd
      simp_all
    · rfl

/-- Completed calls never replace the immutable source stream. -/
theorem Step.input_streams {before after : State} {request : Request} {event : Event}
    {reply : Reply} (step : Step before request event reply after) (fd : Nat) :
    (after.descriptors fd).map Descriptor.input = (before.descriptors fd).map Descriptor.input := by
  cases step <;> try rfl
  all_goals
    simp only [State.setDescriptor, Function.update_apply]
    split
    · subst fd
      simp_all
    · rfl

theorem Step.read_other_descriptor {before after : State} {fd address count : Nat}
    {event : Event} {reply : Reply}
    (step : Step before (.read fd address count) event reply after)
    (other : Nat) (different : other ≠ fd) :
    after.descriptors other = before.descriptors other := by
  cases step <;> simp [State.setDescriptor, different]

theorem Step.write_other_descriptor {before after : State} {fd address count : Nat}
    {event : Event} {reply : Reply}
    (step : Step before (.write fd address count) event reply after)
    (other : Nat) (different : other ≠ fd) :
    after.descriptors other = before.descriptors other := by
  cases step <;> simp [State.setDescriptor, different]

/-- The raw success result always fits a nonnegative RV64 signed word. -/
theorem Step.success_bound {before after : State} {request : Request} {event : Event}
    {count : Nat} (step : Step before request event (.returned (.ok count)) after) :
    count ≤ maxTransfer := by
  cases step <;> first | assumption | simp [maxTransfer]

theorem Step.read_success {before after : State} {fd address requested count : Nat}
    {event : Event}
    (step : Step before (.read fd address requested) event (.returned (.ok count)) after) :
    ∃ bytes, event = .read fd bytes ∧ count = bytes.length ∧ count ≤ requested := by
  cases step
  · exact ⟨_, rfl, rfl, by assumption⟩
  · exact ⟨[], rfl, rfl, Nat.zero_le _⟩
  · exact ⟨[], rfl, rfl, Nat.zero_le _⟩

/-- Short writes report exactly the length of the accepted byte prefix. -/
theorem Step.write_success {before after : State} {fd address requested count : Nat}
    {event : Event}
    (step : Step before (.write fd address requested) event (.returned (.ok count)) after) :
    ∃ bytes, event = .write fd bytes ∧ count = bytes.length ∧ count ≤ requested := by
  cases step with
  | writeSome _ _ _ loaded bounded _ =>
    have length := Memory.readWith_length loaded
    exact ⟨_, rfl, by simp [List.length_take, length, Nat.min_eq_left bounded], bounded⟩

/-- Every process mapping remains backed, even on a clobbering read error. -/
theorem Step.memory_wellFormed {before after : State} {request : Request} {event : Event}
    {reply : Reply} {pageSize : Nat} (step : Step before request event reply after)
    (wellFormed : before.memory.WellFormed pageSize) : after.memory.WellFormed pageSize := by
  cases step with
  | readSome _ _ _ _ _ _ _ _ copied =>
    exact Memory.writeBytes_wellFormed wellFormed copied
  | readError _ _ _ _ _ _ _ frame backed =>
    refine ⟨wellFormed.pageSize_pos, ?_, ?_, ?_⟩
    · simpa only [frame.1] using wellFormed.region_valid
    · simpa only [frame.1] using wellFormed.disjoint
    · intro region member location inside
      rw [frame.1] at member
      exact (backed location).symm.trans (wellFormed.backed region member location inside)
  | _ => exact wellFormed

end Silmaril.Process.Syscall
