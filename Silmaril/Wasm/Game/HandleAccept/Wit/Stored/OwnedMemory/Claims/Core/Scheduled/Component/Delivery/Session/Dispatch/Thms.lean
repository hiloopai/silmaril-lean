module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Session.Dispatch

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession.Dispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)} {callees : List (Callee sig)}
  {start finish : Config (core3 grow) (HostState sig)}

theorem ClosedAt.agrees (closed : ClosedAt start) : AgreesAt ready bindings callees start :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.closedAgrees closed

/-- An actual scheduler block cannot reach the component host overlay. -/
theorem Compatible.block {thread : ThreadId} {next frames rest}
    (focused : start.ctl = ⟨some thread, .prog (.op (.block none) next), frames⟩ :: rest) :
    Compatible profile ready bindings callees start [.tau]
      { (start.setCont thread (some (StepDefs.blockedAct thread next frames))) with
        store := StepDefs.threadStatusSt thread .blocked start.store, ctl := rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.blockPrefix focused

/-- Resume the actual saved activation; no agreement about an open hook or
the code that will run after resuming is necessary for this transition. -/
theorem Compatible.resume_thread {thread : Option ThreadId} {target : ThreadId} {next frames rest blocked}
    (focused : start.ctl = ⟨thread, .prog (.op (.resumeThread target) next), frames⟩ :: rest)
    (saved : start.cont? target = some blocked) :
    Compatible profile ready bindings callees start [.tau]
      { (start.setCont target none) with
        store := StepDefs.threadStatusSt target .running start.store,
        ctl := blocked :: ⟨thread, .prog (next ()), frames⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.resumePrefix focused saved

theorem Compatible.steps {labels} (run : Compatible profile ready bindings callees start labels finish) :
    Steps profile ready (linked ready bindings callees) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.compatibleSteps run

/-- Dispatch and read the reached function slot. Only the selected lifted
branch is compared; no assumption on the unused host function is needed. -/
theorem liftedLookup_steps {impl : HostImpl (core3 grow) (HostState sig)}
    {thread func caller next frames rest core fnType opts inst}
    (focus : start.ctl = ⟨thread, .prog (.op (.call (.funcInst func caller)) next), frames⟩ :: rest)
    (lookup : start.store.func? func = some (.lifted core fnType opts inst)) :
    Steps profile ready (specDispatch ready impl) start [.tau, .tau]
      { start with ctl := ⟨thread, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller),
        .prog next :: frames⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.liftedLookupSteps focus lookup

theorem Compatible.append {middle : Config (core3 grow) (HostState sig)} {leading trailing}
    (before : Compatible profile ready bindings callees start leading middle)
    (after : Compatible profile ready bindings callees middle trailing finish) :
    Compatible profile ready bindings callees start (leading ++ trailing) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.compatibleAppend before after

theorem Compatible.of_closed {labels} (run : Steps profile ready (coreOnly ready bindings) start labels finish)
    (closed : ClosedThrough profile ready bindings start labels finish) : Compatible profile ready bindings callees start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.closedPrefix run closed

/-- Classify the actual finite Core-binding path under the component overlay.
At a reached lifted slot, compare the installed programs after the actual
arena read and continue with the shorter source suffix. A cut remains only
at an unequal direct install not covered by the finite observed lookup. -/
theorem compatible_or_lookup {labels} (run : Steps profile ready (coreOnly ready bindings) start labels finish) :
    Compatible profile ready bindings callees start labels finish ∨ LookupCut profile ready bindings callees start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.compatibleOrLookup run

/-- A closed prefix retains exactly the same allocator occurrence under the
linked dispatch overlay, including at a saved slot. -/
theorem occurrence_of_closed {labels origin mark}
    (path : ReturnFrame.Occurrence.Prefix profile ready (coreOnly ready bindings) start origin labels finish mark)
    (closed : ClosedThrough profile ready bindings start labels finish) :
    ReturnFrame.Occurrence.Prefix profile ready (linked ready bindings callees) start origin labels finish mark :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.closedOccurrence path closed

/-- All steps of a finite guest-only prefix classify without a host
agreement premise. This transports its exact Core effects, not a frame on
the bytes it was allowed to change. -/
theorem Compatible.of_core {count : Nat}
    (run : Steps profile ready (coreOnly ready bindings) start (List.replicate count .core) finish) :
    Compatible profile ready bindings callees start (List.replicate count .core) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FiniteSession.Dispatch.corePrefix run

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession.Dispatch
