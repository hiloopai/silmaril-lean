module

public import Silmaril.Containers.Check.Defs
public import Silmaril.Containers.Machine.Defs
public import Silmaril.Process.TypedSyscall.Defs
public import Silmaril.Semantics.Streams.Defs

@[expose] public section

namespace Silmaril.Containers.TypedSyscall

open Silmaril.Process.TypedSyscall (Outcome)

/-- One completed typed-process step as an existing container transition.
The loader supplies an image, initial pool and store. An emitted event is the
kernel's event, not a serialization of the dependent return type. Silent CPU
steps become `tau`. Exit uses the low eight bits; a classified stop is unchanged.

This is a completed-step adapter, not a scheduling or blocking implementation.
Idle and absent completions have no edge here. If reached with no alternative
or final state, the existing container interpreter reports `undefined stuck`,
not input blocking, a returned error, or a concrete fault. There is no clone edge. -/
def completedMachine {Image Pool Store Event : Type} (isInput : Event → Bool)
    (step : Image → Pool → Store → Option Event → Outcome Pool Store Stop → Prop) :
    Mach.MachineSem (Image × Pool × Store) Event where
  State := Image × Outcome Pool Store Stop
  isIn := isInput
  load program state := state = (program.1, .running program.2.1 program.2.2)
  step
    | (image, .running pool store), action, (nextImage, outcome) =>
        nextImage = image ∧ outcome ≠ .idle ∧
          ∃ observation, action = observation.elim .tau .ev ∧ step image pool store observation outcome
    | _, _, _ => False
  final
    | (_, .exited status _), stop => stop = .exited (UInt8.ofNat status)
    | (_, .stopped reason), stop => stop = reason
    | _, _ => False

/-- The complete observation of a stopped run, as a finite stream word. -/
def stoppedWord {Event : Type} (events : List Event) (stop : Stop) : Streams.Word (Check.Obs Event) :=
  .fin (events.map .ev ++ [.stop stop])

/-- Relabel each event, leaving every terminal observation intact. -/
def relabel {Event Other : Type} (label : Event → Other) : Check.Obs Event → Check.Obs Other
  | .ev event => .ev (label event)
  | .stop stop => .stop stop

end Silmaril.Containers.TypedSyscall
