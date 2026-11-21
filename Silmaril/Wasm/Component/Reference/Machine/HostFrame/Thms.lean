module

public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame

public section

namespace Silmaril.Wasm.Component.Machine.HostFrame

open Silmaril.Wasm Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)}

/-- A different host does not change the step unless its reached read changes
the residual program. A common host write can replace both hosts. -/
theorem step {before after : Config E Host} {label : Label E Host} (other : Host)
    (run : Step profile ready dispatch before label after) :
    (∃ host, Step profile ready dispatch (replace before other) label (replace after host)) ∨
    (∃ alternate, Step profile ready dispatch (replace before other) label alternate ∧
      ReadCut before other label after alternate) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.step other run

/-- Replay an actual finite prefix up to the first host read whose residual
program differs. Replaying a trap or a blocked prefix does not require a return. -/
theorem steps {before after : Config E Host} {labels : List (Label E Host)} (other : Host)
    (run : Steps profile ready dispatch before labels after) :
    (∃ host, Steps profile ready dispatch (replace before other) labels (replace after host)) ∨
    (∃ leading label trailing reached reachedHost next alternate,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch before leading reached ∧
      Steps profile ready dispatch (replace before other) leading (replace reached reachedHost) ∧
      ReadCut reached reachedHost label next alternate ∧
      Step profile ready dispatch reached label next ∧
      Step profile ready dispatch (replace reached reachedHost) label alternate ∧
      Steps profile ready dispatch next trailing after) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.steps other run

/-- A host-and-return-frame pair shares reached store and scheduler data;
neither configuration's host is asserted to survive a callback unchanged. -/
theorem Paired.data {first second : ReturnFrame.Continuation E Host} {left right : Config E Host}
    (paired : Paired first second left right) :
    left.store = right.store ∧ left.pending = right.pending ∧ left.results = right.results ∧
      left.cancels = right.cancels :=
  ⟨ReturnFrame.Paired.data paired |>.1, ReturnFrame.Paired.data paired |>.2.2⟩

/-- A matched segment that changes only the active focus and the respective
hosts can rejoin without equating writers or saved continuations. -/
theorem Paired.retarget {first second : ReturnFrame.Continuation E Host} {left right : Config E Host}
    (paired : Paired first second left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (leftHost rightHost : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired first second { left with host := leftHost, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host := rightHost, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } :=
  ReturnFrame.Paired.retarget paired focused next rightHost

/-- With unequal hosts and substituted return frames, replay both sides up
to the first different reached host read or the pop of a substituted frame.
Both boundary steps execute with the actual reached data. -/
theorem paired_steps {first second : ReturnFrame.Continuation E Host}
    {left right next : Config E Host} {labels : List (Label E Host)}
    (paired : Paired first second left right) (run : Steps profile ready dispatch left labels next) :
    (∃ next', Steps profile ready dispatch right labels next' ∧ Paired first second next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch left leading atLeft ∧
      Steps profile ready dispatch right leading atRight ∧ Paired first second atLeft atRight ∧
      Boundary first second atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      Steps profile ready dispatch afterLeft trailing next) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.paired_steps paired run

/-- Preserve growth evidence on both sides when replaying
up to a host read or saved return. This does not constrain callback writes. -/
theorem paired_growing_steps {grow : SingleThreaded.GrowOracle}
    {ready : HostReady Host} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {first second : ReturnFrame.Continuation (core3 grow) Host}
    {left right next : Config (core3 grow) Host} {labels : List (Label (core3 grow) Host)}
    (paired : Paired first second left right) (run : CoreGrowthSteps profile ready dispatch left labels next) :
    (∃ next', CoreGrowthSteps profile ready dispatch right labels next' ∧ Paired first second next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      CoreGrowthSteps profile ready dispatch left leading atLeft ∧
      CoreGrowthSteps profile ready dispatch right leading atRight ∧ Paired first second atLeft atRight ∧
      Boundary first second atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      CoreGrowthSteps profile ready dispatch afterLeft trailing next) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.paired_growing_steps paired run

/-- A reached interior step replays with the same label, including a Core
step that changes bytes, without an assumption on the other host. -/
theorem interior_step {grow : SingleThreaded.GrowOracle}
    {ready : HostReady Host} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {first second : ReturnFrame.Continuation (core3 grow) Host}
    {left right next : Config (core3 grow) Host} {label : Label (core3 grow) Host}
    (paired : Paired first second left right) (interior : Interior first left)
    (grows : CoreUpdateGrows left) (run : Step profile ready dispatch left label next) :
    ∃ other, CoreGrowthSteps profile ready dispatch right [label] other ∧ Paired first second next other :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.interior_step
    (fun _ _ edge => by cases edge; rfl) paired interior grows run

/-- Only host predicates of reached, blocked candidate threads need agree.
Store-only predicates and threads not making a host query add no premise. -/
theorem instCandidates_eq (store : CStore E) (inst : InstId) (left right : Nat → Bool)
    (agree : ∀ entry, store.inst? inst = some entry → ∀ thread ∈ entry.threads.elements,
      ∀ suspended, store.thread? thread = some suspended → suspended.blocked = true →
        ∀ query, suspended.readyCond = some (.host query) → left query = right query) :
    store.instCandidates left inst = store.instCandidates right inst :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.instCandidates_eq store inst left right agree

/-- The actual synchronous lift loop reaches the same choice or trap
program when its reached candidate lists agree. No runnable thread is assumed. -/
theorem sync_readiness {first second : ReturnFrame.Continuation E Host} {cfg other : Config E Host}
    (paired : Paired first second cfg other) (task : TaskId) {entry : Task E}
    (found : ArenaField.tasks.get? cfg.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : cfg.store.instCandidates (ready cfg.host) entry.inst = cfg.store.instCandidates (ready other.host) entry.inst)
    {thread frames rest} (focused : cfg.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest) :
    ∃ next next', Steps profile ready dispatch cfg [.tau, .tau, .tau] next ∧
      Steps profile ready dispatch other [.tau, .tau, .tau] next' ∧ Paired first second next next' :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.sync_readiness paired task found waiting agrees focused

namespace Related

variable {changes : ReturnFrame.Substitutions E Host}

theorem Paired.data {left right : Config E Host} (paired : Paired changes left right) :
    left.store = right.store ∧ left.pending = right.pending ∧ left.results = right.results ∧
      left.cancels = right.cancels :=
  ⟨ReturnFrame.Related.Paired.data paired |>.1, ReturnFrame.Related.Paired.data paired |>.2.2⟩

theorem Paired.retarget {left right : Config E Host} (paired : Paired changes left right)
    {thread focus frames rest} (focused : left.ctl = ⟨thread, focus, frames⟩ :: rest)
    (next : Focus E Host) (leftHost rightHost : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, otherFrames⟩ :: otherRest ∧
      Paired changes { left with host := leftHost, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host := rightHost, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } :=
  ReturnFrame.Related.Paired.retarget paired focused next rightHost

theorem Paired.retarget_core_frame {left right : Config E Host} (paired : Paired changes left right)
    {thread focus core coreNext frames rest}
    (focused : left.ctl = ⟨thread, focus, .core core coreNext :: frames⟩ :: rest)
    (next : Focus E Host) (leftHost rightHost : Host) :
    ∃ otherFrames otherRest, right.ctl = ⟨thread, focus, .core core coreNext :: otherFrames⟩ :: otherRest ∧
      Paired changes { left with host := leftHost, ctl := ⟨thread, next, frames⟩ :: rest }
        { right with host := rightHost, ctl := ⟨thread, next, otherFrames⟩ :: otherRest } :=
  ReturnFrame.Related.Paired.retarget_core_frame paired focused next rightHost

theorem Paired.set_store {left right : Config E Host} (paired : Paired changes left right) (store : CStore E) :
    Paired changes { left with store } { right with store } :=
  ReturnFrame.Related.Paired.set_store paired store

theorem Paired.clear_control {left right : Config E Host} (paired : Paired changes left right) :
    Paired changes { left with ctl := [] } { right with ctl := [] } :=
  ReturnFrame.Related.Paired.clear_control paired

theorem paired_step {left right next : Config E Host} {label : Label E Host}
    (paired : Paired changes left right) (run : Step profile ready dispatch left label next) :
    ∃ other, Step profile ready dispatch right label other ∧
      (Paired changes next other ∨ Boundary changes left right label next other) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.paired_step paired run

/-- A protected interior focus has neither a host read nor a substituted
return, so the actual step replays under the same label and growth evidence. -/
theorem interior_step {grow : SingleThreaded.GrowOracle}
    {ready : HostReady Host} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {changes : ReturnFrame.Substitutions (core3 grow) Host}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) Host → Prop}
    (covers : ∀ first second, changes first second → protectedReturn first)
    {left right next : Config (core3 grow) Host} {label : Label (core3 grow) Host}
    (paired : Paired changes left right) (interior : InteriorFor protectedReturn left)
    (grows : CoreUpdateGrows left) (run : Step profile ready dispatch left label next) :
    ∃ other, CoreGrowthSteps profile ready dispatch right [label] other ∧ Paired changes next other :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.interior_step covers paired interior grows run

/-- Replay actual growth-certified callback steps when the hosts differ and
several saved calls are already paired. A reached host-read divergence or
the pop of any substituted frame is an explicit boundary. -/
theorem paired_growing_steps {grow : SingleThreaded.GrowOracle}
    {ready : HostReady Host} {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    {changes : ReturnFrame.Substitutions (core3 grow) Host}
    {left right next : Config (core3 grow) Host} {labels : List (Label (core3 grow) Host)}
    (paired : Paired changes left right) (run : CoreGrowthSteps profile ready dispatch left labels next) :
    (∃ next', CoreGrowthSteps profile ready dispatch right labels next' ∧ Paired changes next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      CoreGrowthSteps profile ready dispatch left leading atLeft ∧
      CoreGrowthSteps profile ready dispatch right leading atRight ∧ Paired changes atLeft atRight ∧
      Boundary changes atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      CoreGrowthSteps profile ready dispatch afterLeft trailing next) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineHostFrame.paired_growing_steps paired run

end Related

end Silmaril.Wasm.Component.Machine.HostFrame
