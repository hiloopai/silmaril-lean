module

@[expose] public section

/-!
# Cancellation liveness for an abstract work-tick machine

A small, self-contained abstract model of SQLite-style cooperative cancellation
(`sqlite3_interrupt` setting a flag that the VDBE observes at poll points). It is
**not** a model of SQLite: it isolates the liveness argument so the native
obligations it leaves are explicit.

## The layers, kept apart

* **Counted modeled steps.** `MState.step` is one internal step of the operation:
  a VM instruction, one helper tick, or a poll. Only these are counted.
* **Scheduling.** `Ev.run` grants the operation one counted step; `Ev.idle`
  models time given to anything else. No bound on scheduling gaps is assumed.
* **External calls.** `Instr.call` parks the operation in `Status.waiting`;
  `Ev.extReturn` is the host returning. Its duration is not counted or bounded.
* **Delivery ≠ visibility ≠ observation.** `Ev.deliver e` records a cancel for
  epoch `e` in `Sys.pending` (only when `e` names the active operation);
  `Ev.publish` makes delivered cancels visible (`Sys.visible`); a poll *observes*
  a visible cancel by stopping with `StopReason.cancelled`.
* **Quiescence ≠ return ≠ cleanup/rollback ≠ wall clock.** The theorems conclude
  `MState.Stopped`: the operation's machine performs no further counted step.
  Returning to the API caller, finalization, cleanup and rollback are not modeled,
  and nothing here measures wall-clock time.

## Lifecycle and visibility scope

`Sys.epoch` names the single active operation. `Ev.begin e m` starts a new
operation, only once the current one has stopped, and resets the cancel flags,
so a flag never outlives its operation. A cancel is *relevant* when it names the
current epoch while that operation is active. `Ev.clear` drops visible and
pending cancels; a *coherently managed* operation receives no `clear` while it
is being cancelled (`CoherentFrom`).

## Inputs

Code is an arbitrary `List Nat`; every natural number decodes (`decode`) to an
instruction, with malformed operands and unsupported opcodes decoding to
explicit faults. Data input is an arbitrary `List Nat`, exhaustion is a fault,
and every program counter, poll counter and helper count is allowed.
-/

namespace Silmaril.Semantics.SQLite.Isolation.Cancel

/-- Deployment profile: a poll is due once `period` counted steps have run since the last
poll (`period = 0` polls before every step). -/
structure Profile where
  period : Nat
deriving DecidableEq, Repr

/-- How a helper (an internal routine entered by `Instr.helper`) runs.
`next` is its abstract progress on the remaining count; it may stutter (`next = id`).
When `pollsInside` holds, each helper tick is a counted step charged to the poll budget,
and the helper polls when the budget is spent. Otherwise polls happen only at the
outer instruction loop. -/
structure HelperDiscipline where
  next : Nat → Nat
  pollsInside : Bool

/-- Decoded instructions. `unsupported` and `malformed` keep the raw word. -/
inductive Instr where
  | halt
  | work
  | jump (target : Nat)
  /-- Read one input word: jump to `target` when it is `0`, else fall through. -/
  | branch (target : Nat)
  /-- Enter a helper with `count` remaining ticks. -/
  | helper (count : Nat)
  /-- An external call: the operation waits for the host to return. -/
  | call
  /-- An explicit poll of the cancel flag. -/
  | poll
  | unsupported (raw : Nat)
  | malformed (raw : Nat)
deriving DecidableEq, Repr

/-- Total decoder: opcode `raw % 8`, operand `raw / 8`. -/
def decode (raw : Nat) : Instr :=
  match raw % 8 with
  | 0 => if raw / 8 = 0 then .halt else .malformed raw
  | 1 => if raw / 8 = 0 then .work else .malformed raw
  | 2 => .jump (raw / 8)
  | 3 => .branch (raw / 8)
  | 4 => .helper (raw / 8)
  | 5 => if raw / 8 = 0 then .call else .malformed raw
  | 6 => if raw / 8 = 0 then .poll else .malformed raw
  | _ => .unsupported raw

/-- Encoder for the supported instructions; faults encode as their raw word. -/
def encode : Instr → Nat
  | .halt => 0
  | .work => 1
  | .jump t => 8 * t + 2
  | .branch t => 8 * t + 3
  | .helper n => 8 * n + 4
  | .call => 5
  | .poll => 6
  | .unsupported raw => raw
  | .malformed raw => raw

/-- The instructions a compiler may emit. -/
def Instr.Supported : Instr → Prop
  | .unsupported _ | .malformed _ => False
  | _ => True

inductive StopReason where
  | done
  | cancelled
  | pcOutOfRange
  | inputExhausted
  | unsupported
  | malformed
deriving DecidableEq, Repr

inductive Status where
  | running
  /-- Parked in an external call until the host returns. -/
  | waiting
  | stopped (reason : StopReason)
deriving DecidableEq, Repr

/-- Machine state. Every field is arbitrary: no reachability invariant is assumed. -/
structure MState where
  pc : Nat
  /-- Counted steps since the last poll. -/
  sincePoll : Nat
  /-- Remaining helper count; `0` means the outer loop is running. -/
  helperLeft : Nat
  /-- Remaining raw input words. -/
  input : List Nat
  status : Status
deriving DecidableEq, Repr

namespace MState

def Stopped (s : MState) : Prop := ∃ r, s.status = .stopped r

def active (s : MState) : Bool :=
  match s.status with
  | .stopped _ => false
  | _ => true

def stopWith (r : StopReason) (s : MState) : MState := { s with status := .stopped r }

/-- A poll: observe a visible cancel by stopping, otherwise reset the budget. -/
def poll (vis : Bool) (s : MState) : MState :=
  if vis then s.stopWith .cancelled else { s with sincePoll := 0 }

/-- Execute one decoded outer instruction. -/
def exec (vis : Bool) (s : MState) : Instr → MState
  | .halt => s.stopWith .done
  | .work => { s with pc := s.pc + 1, sincePoll := s.sincePoll + 1 }
  | .jump t => { s with pc := t, sincePoll := s.sincePoll + 1 }
  | .branch t =>
    match s.input with
    | [] => s.stopWith .inputExhausted
    | b :: rest =>
      { s with input := rest, pc := if b = 0 then t else s.pc + 1, sincePoll := s.sincePoll + 1 }
  | .helper n => { s with helperLeft := n, pc := s.pc + 1, sincePoll := s.sincePoll + 1 }
  | .call => { s with status := .waiting, pc := s.pc + 1, sincePoll := s.sincePoll + 1 }
  | .poll => poll vis { s with pc := s.pc + 1 }
  | .unsupported _ => s.stopWith .unsupported
  | .malformed _ => s.stopWith .malformed

/-- One counted step of a running operation, reading the cancel flag `vis`. -/
def runningStep (P : Profile) (H : HelperDiscipline) (code : List Nat) (vis : Bool)
    (s : MState) : MState :=
  if s.helperLeft ≠ 0 then
    if H.pollsInside then
      if P.period ≤ s.sincePoll then s.poll vis
      else { s with helperLeft := H.next s.helperLeft, sincePoll := s.sincePoll + 1 }
    else { s with helperLeft := H.next s.helperLeft }
  else if P.period ≤ s.sincePoll then s.poll vis
  else
    match code[s.pc]? with
    | none => s.stopWith .pcOutOfRange
    | some raw => s.exec vis (decode raw)

/-- A counted modeled step. Waiting and stopped operations take no step. -/
def step (P : Profile) (H : HelperDiscipline) (code : List Nat) (vis : Bool)
    (s : MState) : MState :=
  match s.status with
  | .running => s.runningStep P H code vis
  | _ => s

/-- The host returning from an external call (not a counted step). -/
def resume (s : MState) : MState :=
  match s.status with
  | .waiting => { s with status := .running }
  | _ => s

/-- The internal rank: counted steps left before a poll is due. -/
def rank (P : Profile) (s : MState) : Nat := P.period - s.sincePoll

/-- Counted steps with every external call returning at once: `k` steps from `s`. -/
def drive (P : Profile) (H : HelperDiscipline) (code : List Nat) (vis : Bool) :
    Nat → MState → MState
  | 0, s => s
  | k + 1, s => drive P H code vis k (resume (step P H code vis s))

end MState

/-- Scheduler, host and cancellation events. -/
inductive Ev where
  /-- Time given to something else. -/
  | idle
  /-- The scheduler grants the operation one step. -/
  | run
  /-- The host returns from an external call. -/
  | extReturn
  /-- A cancel request for operation `epoch` is delivered. -/
  | deliver (epoch : Nat)
  /-- Delivered cancels become visible to the operation's polls. -/
  | publish
  /-- Visible and pending cancels are dropped (incoherent management). -/
  | clear
  /-- A new operation `epoch` starts with machine `m` (only after the current one stopped). -/
  | begin (epoch : Nat) (m : MState)

/-- The operation together with its cancellation state. -/
structure Sys where
  epoch : Nat
  mach : MState
  pending : Bool
  visible : Bool

namespace Sys

def step (P : Profile) (H : HelperDiscipline) (code : List Nat) (s : Sys) : Ev → Sys
  | .idle => s
  | .run => { s with mach := s.mach.step P H code s.visible }
  | .extReturn => { s with mach := s.mach.resume }
  | .deliver e => if e = s.epoch ∧ s.mach.active = true then { s with pending := true } else s
  | .publish => { s with visible := s.visible || s.pending, pending := false }
  | .clear => { s with visible := false, pending := false }
  | .begin e m =>
    if s.mach.active = true then s
    else { epoch := e, mach := m, pending := false, visible := false }

/-- A relevant cancel is visible to the active operation. -/
def RelevantVisible (s : Sys) : Prop := s.visible = true ∧ s.mach.active = true

end Sys

/-- The system state after the first `n` events. -/
def run (P : Profile) (H : HelperDiscipline) (code : List Nat) (s₀ : Sys) (ev : Nat → Ev) :
    Nat → Sys
  | 0 => s₀
  | n + 1 => (run P H code s₀ ev n).step P H code (ev n)

/-- Fair scheduling from `t`: the operation is granted a step infinitely often. -/
def FairFrom (ev : Nat → Ev) (t : Nat) : Prop := ∀ n, t ≤ n → ∃ m, n ≤ m ∧ ev m = .run

/-- External calls return: whenever the operation waits (from `t`), the host later returns. -/
def ExternalReturnsFrom (P : Profile) (H : HelperDiscipline) (code : List Nat) (s₀ : Sys)
    (ev : Nat → Ev) (t : Nat) : Prop :=
  ∀ n, t ≤ n → (run P H code s₀ ev n).mach.status = .waiting →
    ∃ m, n ≤ m ∧ ev m = .extReturn

/-- Coherent management from `t`: no event drops the cancel flags. -/
def CoherentFrom (ev : Nat → Ev) (t : Nat) : Prop := ∀ m, t ≤ m → ev m ≠ .clear

/-- Whether event `ev` at state `s` is a counted modeled step of the operation. -/
def Counted (s : Sys) : Ev → Bool
  | .run => s.mach.status == .running
  | _ => false

/-- Counted modeled steps among the `k` events after `t`. -/
def countedAfter (P : Profile) (H : HelperDiscipline) (code : List Nat) (s₀ : Sys)
    (ev : Nat → Ev) (t : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => countedAfter P H code s₀ ev t k +
      if Counted (run P H code s₀ ev (t + k)) (ev (t + k)) then 1 else 0

/-! ## A tiny source work language and its compiler -/

/-- Source programs. `forever` is an outer loop that runs until cancelled. -/
inductive Work where
  | tick
  | call
  | helper (count : Nat)
  | halt
  | seq (a b : Work)
  | forever (body : Work)

/-- Compile at code offset `base`. -/
def compileAt : Work → Nat → List Instr
  | .tick, _ => [.work]
  | .call, _ => [.call]
  | .helper n, _ => [.helper n]
  | .halt, _ => [.halt]
  | .seq a b, base => compileAt a base ++ compileAt b (base + (compileAt a base).length)
  | .forever body, base => compileAt body base ++ [.jump base]

/-- Raw code for a source program, ending in `halt`. -/
def compile (w : Work) : List Nat := (compileAt w 0 ++ [Instr.halt]).map encode

/-! ## Abstract countermodel and premise witnesses (benign, no payloads) -/

/-- A helper that stutters forever and polls only at the outer loop. -/
def stutterHelper : HelperDiscipline := ⟨id, false⟩

/-- The same stuttering helper, charged to the poll budget. -/
def chargedStutterHelper : HelperDiscipline := ⟨id, true⟩

def onePoll : Profile := ⟨1⟩

/-- An outer loop entering a helper once, then halting. -/
def helperCode : List Nat := [encode (.helper 1), encode .halt]

/-- A fresh running machine at `pc = 0`. -/
def fresh : MState := ⟨0, 0, 0, [], .running⟩

/-- Operation `0`, already holding a visible relevant cancel. -/
def cancelledAtStart : Sys := ⟨0, fresh, false, true⟩

/-- An outer loop of ticks. -/
def loopCode : List Nat := compile (.forever .tick)

/-- Schedule the operation at every event. -/
def alwaysRun : Nat → Ev := fun _ => .run

/-- Never schedule the operation. -/
def neverRun : Nat → Ev := fun _ => .idle

/-- Incoherent management: the visible cancel is cleared, then the operation is scheduled. -/
def clearThenRun : Nat → Ev
  | 0 => .clear
  | _ + 1 => .run

/-- A single external call. -/
def callCode : List Nat := [encode .call, encode .halt]

end Silmaril.Semantics.SQLite.Isolation.Cancel
