module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Defs
import Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame

public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)} {first second : Continuation E Host}

/-- Start comparing after the call installed its saved return frame. Other
frames, including a parked Core caller, are paired unchanged. -/
theorem installed (cfg : Config E Host) (thread : Option ThreadId) (body : P E Host (Ret E))
    (frames : List (Seg E Host)) (rest : List (Activation E Host)) :
    Paired first second { cfg with ctl := ⟨thread, .prog body, .prog first :: frames⟩ :: rest }
      { cfg with ctl := ⟨thread, .prog body, .prog second :: frames⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.installed cfg thread body frames rest

/-- Recover both reached cursors and the common result from a witnessed pop. -/
theorem Returned.inputs {left right leftAfter rightAfter : Config E Host} {label : Label E Host}
    (popped : Returned first second left right label leftAfter rightAfter) :
    ∃ thread value leftFrames rightFrames leftRest rightRest,
      left.ctl = ⟨thread, .prog (.pure value), .prog first :: leftFrames⟩ :: leftRest ∧
      right.ctl = ⟨thread, .prog (.pure value), .prog second :: rightFrames⟩ :: rightRest := by
  cases popped with
  | mk edge atLeft atRight => cases edge; exact ⟨_, _, _, _, _, _, atLeft, atRight⟩

/-- Equality is between the two machines at the reached point, not between
the reached and original states of the callback. -/
theorem Paired.data {left right : Config E Host} (paired : Paired first second left right) :
    left.store = right.store ∧ left.host = right.host ∧ left.pending = right.pending ∧
      left.results = right.results ∧ left.cancels = right.cancels := by
  cases paired
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Find the corresponding activation and keep its segment stack and the
blocked frames paired under a matched focus update. -/
theorem Paired.retarget {left right : Config E Host} (paired : Paired first second left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (host : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired first second { left with host, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.retarget paired focused next host

/-- A single replay step either keeps the framed relation or pops the
substituted continuation with the same result on both sides. -/
theorem step {left right next : Config E Host} {label : Label E Host}
    (paired : Paired first second left right) (run : Step profile ready dispatch left label next) :
    (∃ next', Step profile ready dispatch right label next' ∧ Paired first second next next') ∨
    (∃ next', Step profile ready dispatch right label next' ∧ Returned first second left right label next next') :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.step paired run

/-- Replay any finite run, with identical labels and reached data, up to and
including the first pop of a substituted frame. That pop supplies the same
result to each continuation. If no such frame is popped, also replay the
final configuration (including traps). Nothing requires the call to return. -/
theorem steps {left right next : Config E Host} {labels : List (Label E Host)}
    (paired : Paired first second left right) (run : Steps profile ready dispatch left labels next) :
    (∃ next', Steps profile ready dispatch right labels next' ∧ Paired first second next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch left leading atLeft ∧
      Steps profile ready dispatch right leading atRight ∧ Paired first second atLeft atRight ∧
      Returned first second atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      Steps profile ready dispatch afterLeft trailing next) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.steps paired run

namespace Related

variable {changes : Substitutions E Host}

theorem Paired.set_store {left right : Config E Host} (paired : Paired changes left right) (store : CStore E) :
    Paired changes { left with store } { right with store } := by
  cases paired with
  | mk control blocked => exact .mk control blocked

theorem Paired.clear_control {left right : Config E Host} (paired : Paired changes left right) :
    Paired changes { left with ctl := [] } { right with ctl := [] } := by
  cases paired with
  | mk _ blocked => exact .mk .nil blocked

theorem Returned.left_input {left right leftAfter rightAfter : Config E Host} {label : Label E Host}
    (popped : Returned changes left right label leftAfter rightAfter) :
    ∃ resume otherResume thread value frames rest, changes resume otherResume ∧
      left.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest := by
  cases popped with
  | mk edge atLeft _ => exact ⟨_, _, _, _, _, _, edge, atLeft⟩

theorem Paired.data {left right : Config E Host} (paired : Paired changes left right) :
    left.store = right.store ∧ left.host = right.host ∧ left.pending = right.pending ∧
      left.results = right.results ∧ left.cancels = right.cancels := by
  cases paired
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Paired.retarget {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (host : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired changes { left with host, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.retarget paired focused next host

/-- A saved Core caller is shared; only older program continuations can differ. -/
theorem Paired.retarget_core_frame {left right : Config E Host} (paired : Paired changes left right)
    {thread focus core coreNext frames rest}
    (focused : left.ctl = ⟨thread, focus, .core core coreNext :: frames⟩ :: rest)
    (next : Focus E Host) (host : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, .core core coreNext :: otherFrames⟩ :: otherRest ∧
      Paired changes { left with host, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.retargetCoreFrame paired focused next host

/-- Move the current activation and its shared Core caller into the blocked slot. -/
theorem Paired.park_core {left right : Config E Host} (paired : Paired changes left right)
    {thread core coreNext frames rest} (focused : left.ctl = ⟨some thread, .core core coreNext, frames⟩ :: rest)
    (saved : Focus E Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨some thread, .core core coreNext, otherFrames⟩ :: otherRest ∧
      Paired changes
        { (left.setCont thread (some ⟨some thread, saved, .core core coreNext :: frames⟩)) with ctl := rest }
        { (right.setCont thread (some ⟨some thread, saved, .core core coreNext :: otherFrames⟩)) with ctl := otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.parkCore paired focused saved

/-- Restore the actual saved activation, preserving both sets of older frames. -/
theorem Paired.resume_core {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest target saved core coreNext savedFrames}
    (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (found : left.cont? target = some ⟨some target, saved, .core core coreNext :: savedFrames⟩)
    (ongoing resumed : Focus E Host) :
    ∃ otherFrames otherRest otherSaved, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      right.cont? target = some ⟨some target, saved, .core core coreNext :: otherSaved⟩ ∧
      Paired changes
        { (left.setCont target none) with ctl :=
          ⟨some target, resumed, .core core coreNext :: savedFrames⟩ :: ⟨thread, ongoing, frames⟩ :: rest }
        { (right.setCont target none) with ctl :=
          ⟨some target, resumed, .core core coreNext :: otherSaved⟩ :: ⟨thread, ongoing, otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.resumeCore paired focused found ongoing resumed

/-- Save the same caller segment on both sides (including a Core caller).
Active and blocked frame substitutions are unchanged. -/
theorem Paired.push_shared {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (frame : Seg E Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired changes { left with ctl := ⟨thread, next, frame :: frames⟩ :: rest }
        { right with ctl := ⟨thread, next, frame :: otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.pushShared paired focused next frame

/-- Install a common continuation prefix without replacing older frames. -/
theorem Paired.push_shared_frames {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (shared : List (Seg E Host)) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired changes { left with ctl := ⟨thread, next, shared ++ frames⟩ :: rest }
        { right with ctl := ⟨thread, next, shared ++ otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.pushSharedFrames paired focused next shared

/-- Enter the actual saved activation and install a common resumer prefix. -/
theorem Paired.reenter_saved {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest target saved} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (found : left.cont? target = some saved) (ongoing : Focus E Host) (shared : List (Seg E Host)) :
    ∃ otherFrames otherRest otherSaved, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      right.cont? target = some otherSaved ∧
      Paired changes
        { (left.setCont target none) with ctl := saved :: ⟨thread, ongoing, shared ++ frames⟩ :: rest }
        { (right.setCont target none) with ctl := otherSaved :: ⟨thread, ongoing, shared ++ otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.reenterSaved paired focused found ongoing shared

/-- Push a new substituted continuation at the current focus. All already
paired frames, including those in blocked activations, keep their relation. -/
theorem Paired.push {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (body : P E Host (Ret E)) (first second : Continuation E Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired (Extend changes first second)
        { left with ctl := ⟨thread, .prog body, .prog first :: frames⟩ :: rest }
        { right with ctl := ⟨thread, .prog body, .prog second :: otherFrames⟩ :: otherRest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.push paired focused body first second

theorem step {left right next : Config E Host} {label : Label E Host}
    (paired : Paired changes left right) (run : Step profile ready dispatch left label next) :
    (∃ next', Step profile ready dispatch right label next' ∧ Paired changes next next') ∨
    (∃ next', Step profile ready dispatch right label next' ∧ Returned changes left right label next next') :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.step paired run

/-- Replay an actual finite scheduler run until it consumes a substitution.
The cut carries the reached pair, which may be an older blocked frame rather
than the most recently installed one. -/
theorem steps {left right next : Config E Host} {labels : List (Label E Host)}
    (paired : Paired changes left right) (run : Steps profile ready dispatch left labels next) :
    (∃ next', Steps profile ready dispatch right labels next' ∧ Paired changes next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch left leading atLeft ∧
      Steps profile ready dispatch right leading atRight ∧ Paired changes atLeft atRight ∧
      Returned changes atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      Steps profile ready dispatch afterLeft trailing next) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.steps paired run

end Related

end Silmaril.Wasm.Component.Machine.ReturnFrame
