module

public import Silmaril.Process.Syscall

/-! # What a command-line process shows

A CLI process is observed through the byte streams it exchanges with its
environment and the way it ends. The events are `Process.Syscall.Event`s, one
per completed system call; this file only adds projections, so that a
specification never depends on how a program splits its I/O into calls.
`write 1 "ab"` and `write 1 "a"; write 1 "b"` have different event lists and
the same projections (compare the byte-granular events of theorem-labs' LPS,
`State.event`, where the two traces are equal).

The outcomes are those of a whole process, not of a function:

* `exited status`: the process called `exit`/`exit_group`; `status` is already
  reduced modulo 256 by `Syscall.Step.exit`;
* `crashed fault`: the instruction-set model reports a fault. The signal a
  real kernel would deliver is deliberately not named: a data fault next to
  the stack mapping may be a stack growth on Linux, so naming SIGSEGV would be
  unsound for the fixed-mapping memory model. Specifications forbid crashes;
* `unmodeled`: the run reached a configuration the model gives no meaning to
  (an undecodable instruction, an undefined condition, a system call outside
  the profile). Every statement in `CLI.Spec` excludes it ("coverage");
* `diverges`: an infinite run of completed steps. A blocked system call is not
  divergence: it is the absence of a completed transition.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

/-- How a machine model classifies a fault. Only `unmodeled` is a coverage
failure; the others are architectural faults that end the process. -/
inductive Fault where
  | memory
  | divide
  | illegal
  | unmodeled
  deriving DecidableEq, Repr

/-- The outcome of a whole process run. -/
inductive Outcome where
  | exited (status : Nat)
  | crashed (fault : Fault)
  | unmodeled
  | diverges
  deriving DecidableEq, Repr

/-! ## Projections of an event trace -/

/-- Bytes delivered by successful reads on `fd`, in order. -/
def readOn (fd : Nat) : List Event → List Byte
  | [] => []
  | .read d bytes :: rest => (if d = fd then bytes else []) ++ readOn fd rest
  | _ :: rest => readOn fd rest

/-- Bytes accepted by successful writes on `fd`, in order. -/
def writtenOn (fd : Nat) : List Event → List Byte
  | [] => []
  | .write d bytes :: rest => (if d = fd then bytes else []) ++ writtenOn fd rest
  | _ :: rest => writtenOn fd rest

def stdinRead (events : List Event) : List Byte := readOn 0 events
def stdout (events : List Event) : List Byte := writtenOn 1 events
def stderr (events : List Event) : List Byte := writtenOn 2 events

/-- A read on `fd` reported end of file: a successful empty read. (An empty read
of a zero-byte request also has this event; `Syscall.Step.readZero`.) -/
def SawEof (fd : Nat) (events : List Event) : Prop := Event.read fd [] ∈ events

/-- The environment refused something: an error return, or a write that
accepted no byte. These are the only events that may justify a failure. -/
def _root_.Silmaril.Process.Syscall.Event.IsRefusal : Event → Prop
  | .error _ _ => True
  | .write _ [] => True
  | _ => False

instance (event : Event) : Decidable event.IsRefusal := by
  cases event with
  | error => exact isTrue trivial
  | write fd bytes => cases bytes <;> simp only [Event.IsRefusal] <;> infer_instance
  | read => exact isFalse id
  | exit => exact isFalse id

def Refused (events : List Event) : Prop := ∃ event ∈ events, event.IsRefusal

/-- Writes only to the given descriptors. -/
def WritesOnlyTo (fds : List Nat) (events : List Event) : Prop :=
  ∀ fd bytes, Event.write fd bytes ∈ events → fd ∈ fds

@[simp] theorem readOn_nil (fd : Nat) : readOn fd [] = [] := rfl
@[simp] theorem writtenOn_nil (fd : Nat) : writtenOn fd [] = [] := rfl

theorem readOn_append (fd : Nat) (first second : List Event) :
    readOn fd (first ++ second) = readOn fd first ++ readOn fd second := by
  induction first with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [readOn, ih]

theorem writtenOn_append (fd : Nat) (first second : List Event) :
    writtenOn fd (first ++ second) = writtenOn fd first ++ writtenOn fd second := by
  induction first with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [writtenOn, ih]

/-- Splitting a write does not change any projection. -/
theorem writtenOn_split (fd d : Nat) (first second : List Byte) :
    writtenOn fd [.write d (first ++ second)] = writtenOn fd [.write d first, .write d second] := by
  by_cases h : d = fd <;> simp [writtenOn, h]

theorem refused_append {first second : List Event} :
    Refused (first ++ second) ↔ Refused first ∨ Refused second := by
  simp only [Refused, List.mem_append]
  constructor
  · rintro ⟨event, member | member, refusal⟩
    · exact .inl ⟨event, member, refusal⟩
    · exact .inr ⟨event, member, refusal⟩
  · rintro (⟨event, member, refusal⟩ | ⟨event, member, refusal⟩)
    · exact ⟨event, .inl member, refusal⟩
    · exact ⟨event, .inr member, refusal⟩

end Silmaril.Process.CLI
