module

public import Silmaril.Net.Http3.Stream.Defs
public import Silmaril.Automata.Named.Derive
public import Silmaril.Automata.Machine.Defs

@[expose] public section

/-!
# HTTP/3 stream machines as finite machines (`Silmaril.Automata`)

The request/push-stream reader and the control-stream reader of `Silmaril.Net.Http3.Stream`
abstracted to finite machines, so that the verified reachability procedures of
`Silmaril.Automata` decide properties of the frame grammar (RFC 9114 §4.1, §6.2.1).

* `requestMachine k`: states are the reader's `Phase`; labels are frame kinds (`FrameKind`).
  It is exact on phases: `Thms.requestMachine_step` relates it to `reqStep` (the machine
  forgets only the accumulated message parts).
* `controlMachine peer`: states `awaitSettings`/`ready`; labels are control-frame kinds. It
  over-approximates `controlStep`: the GOAWAY and MAX_PUSH_ID value checks (monotonicity,
  request-stream IDs) are data, not states, and are proved separately in `Stream.Thms`;
  `Thms.controlStep_machine` shows every accepted frame is an edge of the machine.
-/

namespace Silmaril.Net.Http3

silmaril_finite Phase

/-- The kind of a frame, as the request-stream reader of kind `k` sees it. -/
inductive FrameKind where
  | headersFinal | headersInterim | data | pushPromise | unknown
  /-- SETTINGS, CANCEL_PUSH, GOAWAY or MAX_PUSH_ID: control-stream frames. -/
  | control
  | h2Reserved
  deriving DecidableEq, Repr, Inhabited

silmaril_finite FrameKind

/-- The kind of a frame; HEADERS is interim only on responses and pushes. -/
def Frame.kind (k : StreamKind) (interim : List UInt8 → Bool) : Frame → FrameKind
  | .headers h => if k ≠ .request ∧ interim h then .headersInterim else .headersFinal
  | .data _ => .data
  | .pushPromise _ _ => .pushPromise
  | .unknown _ _ => .unknown
  | .settings _ | .cancelPush _ | .goaway _ | .maxPushId _ => .control
  | .h2Reserved _ _ => .h2Reserved

/-- The phase transitions of the request/push-stream reader (§4.1). -/
def phaseStep (k : StreamKind) : Phase → FrameKind → Option Phase
  | .awaitHeaders, .headersInterim => some .awaitHeaders
  | .awaitHeaders, .headersFinal => some .body
  | .body, .headersFinal => some .done
  | .body, .headersInterim => some .done
  | .body, .data => some .body
  | p, .pushPromise => if k = .response then some p else none
  | p, .unknown => some p
  | _, _ => none

/-- The request/push-stream reader as a finite deterministic machine. -/
def requestMachine (k : StreamKind) : Silmaril.Automata.DMachine Phase FrameKind := ⟨phaseStep k⟩

/-- Control-stream phases (§6.2.1). -/
inductive ControlPhase where
  | awaitSettings | ready
  deriving DecidableEq, Repr, Inhabited

silmaril_finite ControlPhase

/-- Control-stream frame kinds. -/
inductive ControlKind where
  | settings | goaway | maxPushId | cancelPush | unknown
  /-- DATA, HEADERS, PUSH_PROMISE, HTTP/2-reserved. -/
  | forbidden
  deriving DecidableEq, Repr, Inhabited

silmaril_finite ControlKind

/-- The kind of a control-stream frame. -/
def Frame.controlKind : Frame → ControlKind
  | .settings _ => .settings
  | .goaway _ => .goaway
  | .maxPushId _ => .maxPushId
  | .cancelPush _ => .cancelPush
  | .unknown _ _ => .unknown
  | .data _ | .headers _ | .pushPromise _ _ | .h2Reserved _ _ => .forbidden

/-- Control-stream transitions; MAX_PUSH_ID is accepted only from clients (§7.2.7). -/
def controlPhaseStep (peer : Role) : ControlPhase → ControlKind → Option ControlPhase
  | .awaitSettings, .settings => some .ready
  | .ready, .goaway | .ready, .cancelPush | .ready, .unknown => some .ready
  | .ready, .maxPushId => if peer = .client then some .ready else none
  | _, _ => none

/-- The control-stream reader as a finite deterministic machine. -/
def controlMachine (peer : Role) : Silmaril.Automata.DMachine ControlPhase ControlKind :=
  ⟨controlPhaseStep peer⟩

/-- The phase of a control-stream reader state. -/
def ControlState.phase (s : ControlState) : ControlPhase :=
  if s.settings.isSome then .ready else .awaitSettings

end Silmaril.Net.Http3
