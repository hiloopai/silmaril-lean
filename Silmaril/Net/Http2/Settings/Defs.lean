module

public import Silmaril.Net.Http2.Frame.Defs

@[expose] public section

/-!
# HTTP/2 settings and flow control (RFC 9113 §6.5, §6.9)

**Settings (§6.5.2).** The parameters a peer announces in SETTINGS frames, with their initial
values, and the checks on receipt:

| Parameter | Id | Initial | Constraint on receipt |
| --- | --- | --- | --- |
| `SETTINGS_HEADER_TABLE_SIZE` | 0x1 | 4096 | none |
| `SETTINGS_ENABLE_PUSH` | 0x2 | 1 | 0 or 1, else `PROTOCOL_ERROR` |
| `SETTINGS_MAX_CONCURRENT_STREAMS` | 0x3 | unlimited | none |
| `SETTINGS_INITIAL_WINDOW_SIZE` | 0x4 | 65535 | at most 2^31-1, else `FLOW_CONTROL_ERROR` |
| `SETTINGS_MAX_FRAME_SIZE` | 0x5 | 16384 | 2^14 to 2^24-1, else `PROTOCOL_ERROR` |
| `SETTINGS_MAX_HEADER_LIST_SIZE` | 0x6 | unlimited | none |

"An endpoint that receives a SETTINGS frame with any unknown or unsupported identifier MUST
ignore that setting" (§6.5.2). The payload is a list of 6-octet parameters (16-bit identifier,
32-bit value); "a SETTINGS frame with a length other than a multiple of 6 octets MUST be
treated as a connection error … of type FRAME_SIZE_ERROR" (§6.5).

**Flow control (§5.2, §6.9).** A flow-control window is a signed integer: a sender may not
send flow-controlled frames (DATA) beyond it (`consume`); WINDOW_UPDATE adds a non-zero
increment (`increment`), and "a sender MUST NOT allow a flow-control window to exceed 2^31-1
octets" (§6.9.1: `FLOW_CONTROL_ERROR`). A change of `SETTINGS_INITIAL_WINDOW_SIZE` shifts every
stream window by the difference and may make it negative (§6.9.2, `adjustInitial`).
-/

namespace Silmaril.Net.Http2

/-- The largest flow-control window, `2^31 - 1` (§6.9.1). -/
def maxWindow : Nat := 2 ^ 31 - 1

/-- A peer's settings (§6.5.2). -/
structure Settings where
  headerTableSize : Nat := 4096
  enablePush : Bool := true
  maxConcurrentStreams : Option Nat := none
  initialWindowSize : Nat := 65535
  maxFrameSize : Nat := 16384
  maxHeaderListSize : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- The initial settings (§6.5.2). -/
def Settings.initial : Settings := {}

/-- The constraints of §6.5.2 on the values. -/
def Settings.Valid (s : Settings) : Prop :=
  s.initialWindowSize ≤ maxWindow ∧ 2 ^ 14 ≤ s.maxFrameSize ∧ s.maxFrameSize ≤ 2 ^ 24 - 1

/-- Apply one parameter on receipt (§6.5.2). -/
def Settings.apply (s : Settings) (id value : Nat) : Except ErrorCode Settings :=
  match id with
  | 0x1 => .ok { s with headerTableSize := value }
  | 0x2 =>
    if value = 0 then .ok { s with enablePush := false }
    else if value = 1 then .ok { s with enablePush := true }
    else .error .protocolError
  | 0x3 => .ok { s with maxConcurrentStreams := some value }
  | 0x4 =>
    if value ≤ maxWindow then .ok { s with initialWindowSize := value }
    else .error .flowControlError
  | 0x5 =>
    if 2 ^ 14 ≤ value ∧ value ≤ 2 ^ 24 - 1 then .ok { s with maxFrameSize := value }
    else .error .protocolError
  | 0x6 => .ok { s with maxHeaderListSize := some value }
  | _ => .ok s

/-- Apply parameters in order ("processed in the order in which they appear", §6.5.3). -/
def Settings.applyAll (s : Settings) : List (Nat × Nat) → Except ErrorCode Settings
  | [] => .ok s
  | (id, v) :: ps => match s.apply id v with
    | .ok s' => s'.applyAll ps
    | .error e => .error e

/-- The parameters of a SETTINGS payload (§6.5.1), 6 octets each. -/
def decodeSettingsPayload : List UInt8 → Except ErrorCode (List (Nat × Nat))
  | [] => .ok []
  | a :: b :: c :: d :: e :: f :: rest =>
    match decodeSettingsPayload rest with
    | .ok ps => .ok ((a.toNat * 256 + b.toNat,
        ((c.toNat * 256 + d.toNat) * 256 + e.toNat) * 256 + f.toNat) :: ps)
    | .error err => .error err
  | _ => .error .frameSizeError

/-! ## Flow control (§6.9) -/

/-- Send (or receive) `n` octets of flow-controlled data against the window `w` (§6.9.1). -/
def consume (w : Int) (n : Nat) : Except ErrorCode Int :=
  if (n : Int) ≤ w then .ok (w - n) else .error .flowControlError

/-- A WINDOW_UPDATE with increment `inc` (§6.9, §6.9.1): 0 is a `PROTOCOL_ERROR`, and a window
above `2^31 - 1` a `FLOW_CONTROL_ERROR`. -/
def increment (w : Int) (inc : Nat) : Except ErrorCode Int :=
  if inc = 0 then .error .protocolError
  else if w + inc ≤ (maxWindow : Int) then .ok (w + inc) else .error .flowControlError

/-- A change of `SETTINGS_INITIAL_WINDOW_SIZE` from `old` to `new` (§6.9.2). -/
def adjustInitial (w : Int) (old new : Nat) : Except ErrorCode Int :=
  if w + new - old ≤ (maxWindow : Int) then .ok (w + new - old) else .error .flowControlError

/-- Flow-control events on one window. -/
inductive FlowEvent where
  | data (n : Nat)
  | update (inc : Nat)
  deriving DecidableEq, Repr

/-- Run flow-control events. -/
def runFlow (w : Int) : List FlowEvent → Except ErrorCode Int
  | [] => .ok w
  | .data n :: es => match consume w n with
    | .ok w' => runFlow w' es
    | .error e => .error e
  | .update k :: es => match increment w k with
    | .ok w' => runFlow w' es
    | .error e => .error e

/-- The data octets of a list of events. -/
def dataSent : List FlowEvent → Nat
  | [] => 0
  | .data n :: es => n + dataSent es
  | .update _ :: es => dataSent es

/-- The credit granted by a list of events. -/
def credit : List FlowEvent → Nat
  | [] => 0
  | .data _ :: es => credit es
  | .update k :: es => k + credit es

end Silmaril.Net.Http2
