module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession.Dispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

abbrev coreOnly (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) :=
  specDispatch (E := core3 grow) ready (host bindings)

abbrev linked (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) (callees : List (Callee sig)) :=
  specDispatch (E := core3 grow) ready (hostWithComponent bindings callees)

/-- Test the actual focused late-bound request, not all component function
implementations. The other two dispatching machine rules (Core callout and
thread installation) agree for this overlay without conditions. -/
def AgreesAt (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) (callees : List (Callee sig))
    (start : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {thread call next frames rest}, start.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest →
    coreOnly ready bindings call = linked ready bindings callees call

/-- A reached trace at common cuts of both dispatchers. A lifted function
lookup can cross two steps at once: the installed programs may differ, but
the actual arena read selects the same continuation. No equality of writers,
guest bytes, or callback return is imposed. -/
inductive Compatible (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (callees : List (Callee sig)) :
    Config (core3 grow) (HostState sig) → List (Label (core3 grow) (HostState sig)) → Config (core3 grow) (HostState sig) → Prop where
  | done (state : Config (core3 grow) (HostState sig)) : Compatible profile ready bindings callees state [] state
  | next {start middle finish label labels}
      (agreement : AgreesAt ready bindings callees start)
      (step : Step profile ready (coreOnly ready bindings) start label middle)
      (tail : Compatible profile ready bindings callees middle labels finish) :
      Compatible profile ready bindings callees start (label :: labels) finish
  | liftedLookup {start finish labels thread func caller next frames rest core fnType opts inst}
      (focus : start.ctl = ⟨thread, .prog (.op (.call (.funcInst func caller)) next), frames⟩ :: rest)
      (lookup : start.store.func? func = some (.lifted core fnType opts inst))
      (tail : Compatible profile ready bindings callees
        { start with ctl := ⟨thread, .prog (canonLift Limits.spec Quirks.none core fnType opts inst caller),
          .prog next :: frames⟩ :: rest } labels finish) :
      Compatible profile ready bindings callees start (.tau :: .tau :: labels) finish

/-- The only direct requests that can see the component function overlay. -/
def UsesComponent (call : Call (core3 grow)) : Prop :=
  match call with
  | .funcInst .. | .hostFunc .. => True
  | _ => False

def ClosedAt (start : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {thread call next frames rest}, start.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest → ¬ UsesComponent call

/-- A route is closed through the selected cut if no proper reached prefix
of that trace enters either component-function dispatch boundary. -/
def ClosedThrough (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (start : Config (core3 grow) (HostState sig)) (labels : List (Label (core3 grow) (HostState sig)))
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {leading cut label trailing}, labels = leading ++ label :: trailing →
    Steps profile ready (coreOnly ready bindings) start leading cut →
    Steps profile ready (coreOnly ready bindings) cut (label :: trailing) finish → ClosedAt cut

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession.Dispatch
