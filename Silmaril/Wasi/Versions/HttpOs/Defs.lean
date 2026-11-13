module

public import Silmaril.Wasi.Versions.SockOs.Defs
public import Silmaril.Wasi.Versions.HttpBody2Over.Defs

@[expose] public section

/-!
# The OS image of WASI HTTP, over the extended events of `IoSpecNet`

`Silmaril.Machine.Process.IoSpecNet` extends the LPS events with socket events (`SockEv`) and the
network `NetEnv`; `Silmaril.Wasi.Versions.SockOs` gives the socket slices their image. This module
gives the HTTP slices one, in the same vocabulary, without new event constructors: an exchange
for the request of key `k = (authority, path-with-query)` is observed at the address `keyV k`
(the record of the two values).

* **Events** (`List (SockEv Val)`), stateful along the theory states:
  - 0.2 (`evHttp2`, state `HttpSt`): `future-incoming-response.get(f)` of a tied future answered
    `some(ok(ok(_)))` / `some(ok(error(code)))` is `connect f (keyV k) none` /
    `connect f (keyV k) (some code)`; `incoming-response.status(rs)` of a tied response answered
    `s` is `recv (keyV k) s` (the status, as a `u16` value);
  - 0.3 (`evHttp3`, state `Http3St`): `send(r)` answered `ok(_)` / `error(code)` is the same
    connect event, `get-status-code(rs)` the same recv event;
  - response bodies (`evBody2`, `evBody3`, states `BodySt`, `Body3St`): additionally each chunk
    read from a tracked body stream (0.2 `read`/`blocking-read` answered `ok(bytes)`, 0.3
    `stream.read` answered `COMPLETED`) is `recv (keyV k) bytes`.
* **The network of a web** (`httpNet W body`): connecting to `keyV k` has the outcome of the web
  (`none` for a status, `some code` for an `error-code`); the inbox of `keyV k` holds the
  status of the web and every chunk (a contiguous part, `<:+:`) of `body k`. A failed request
  admits any status (no response exists in a run of the theories). `peer` and `resolver` are
  empty: HTTP does not observe them.
* **The extended image** (`xHttp2 ch`, `xHttp3 ch`): `SockOs.xRun` with the stdout image and
  the HTTP body images.

**Not imaged**: trailers, headers, outgoing bodies, `subscribe`. The address `keyV k` is a
name for the exchange, not an IP socket address: the image says what the process observed of
the web, not how the host reached it.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.HttpOs

open Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.SockOs
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-! ## The network of a web -/

/-- The address of the exchange of the request of key `k`. -/
def keyV (k : Val × Val) : Val := .record [k.1, k.2]

/-- The connection outcome of a request address. -/
def connOf (W : Web) : Val → Option Nat
  | .record [a, p] =>
    match W a p with
    | .status _ => none
    | .error c => some c
  | _ => none

/-- A status the web admits for the request of key `k` (any status for a failed request). -/
def statusIn (W : Web) (k : Val × Val) (d : Val) : Bool :=
  match W k.1 k.2, d with
  | .status s, .u16 s' => s' == s
  | .error _, _ => true
  | _, _ => false

/-- A chunk of the body of the request of key `k`. -/
def chunkIn (body : Val × Val → List (BitVec 8)) (k : Val × Val) : Val → Bool
  | .record vs =>
    match u8sOf vs with
    | some bs => decide (bs <:+: body k)
    | none => false
  | _ => false

/-- The inbox of a request address: the status and the body chunks. -/
def inboxOf (W : Web) (body : Val × Val → List (BitVec 8)) : Val → Val → Bool
  | .record [a, p], d => statusIn W (a, p) d || chunkIn body (a, p) d
  | _, _ => false

/-- **The network of the web `W` with the bodies `body`.** -/
def httpNet (W : Web) (body : Val × Val → List (BitVec 8)) : NetEnv Val :=
  ⟨connOf W, inboxOf W body, fun _ _ => false, fun _ _ => false⟩

/-! ## Events -/

/-- The outcome of an inner `result<response, error-code>`. -/
def innerOutcome : Val → Option (Option Nat)
  | .variant 0 (some (.u32 _)) => some none
  | .variant 1 (some (.variant c _)) => some (some c)
  | _ => none

/-- The socket events of a 0.2 outgoing HTTP answer. -/
def evHttp2 (q : HttpSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 h :: _) (some [.variant 1 (some (.variant 0 (some x)))]) =>
    if f = futGet then
      match lookup h q.futs, innerOutcome x with
      | some k, some o => [.connect (hw h) (keyV k) o]
      | _, _ => []
    else []
  | .imp f (.u32 h :: _) (some [.u16 s]) =>
    if f = respStatus then
      match lookup h q.resps with
      | some k => [.recv (keyV k) (.u16 s)]
      | none => []
    else []
  | _ => []

/-- The socket events of a 0.3 outgoing HTTP answer. -/
def evHttp3 (q : Http3St) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 r :: _) (some [x]) =>
    if f = send3 then
      match innerOutcome x with
      | some o => [.connect (hw r) (keyV (q.key r)) o]
      | none => []
    else if f = getStatus3 then
      match x, lookup r q.resps with
      | .u16 s, some k => [.recv (keyV k) (.u16 s)]
      | _, _ => []
    else []
  | _ => []

/-- The body chunk of a 0.2 read answer. -/
def chunkEv2 (q : BodySt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 h :: _) (some [.variant 0 (some (.record vs))]) =>
    if isReadFn f then
      match lookup h q.streams with
      | some (some (k, _)) => [.recv (keyV k) (.record vs)]
      | _ => []
    else []
  | _ => []

/-- The body chunk of a 0.3 `stream.read` answer. -/
def chunkEv3 (q : Body3St) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 h :: _) (some [.u32 pv, .record vs]) =>
    if f = P3.cStreamRead then
      match lookup h q.streams, copy3 pv with
      | some (some (k, _)), some (some (.completed, _)) => [.recv (keyV k) (.record vs)]
      | _, _ => []
    else []
  | _ => []

/-- The socket events of a 0.2 HTTP answer with bodies. -/
def evBody2 (q : BodySt) (e : WEv) : List (SockEv Val) := evHttp2 q.base e ++ chunkEv2 q e

/-- The socket events of a 0.3 HTTP answer with bodies. -/
def evBody3 (q : Body3St) (e : WEv) : List (SockEv Val) := evHttp3 q.base e ++ chunkEv3 q e

/-! ## The extended image -/

/-- **The extended OS image of a 0.2 HTTP run**: stdout on `ch`, then the HTTP events. -/
def xHttp2 (ch : Silmaril.Process.LPS.Word) (t : List WEv) : List XEv :=
  xRun (fun (_ : Unit) e => ((), Silmaril.Wasi.Os.osEv ch e)) bodyNext evBody2 () {} t

/-- **The extended OS image of a 0.3 HTTP run**: stdout on `ch` (`osStep3`), then the HTTP
events. -/
def xHttp3 (ch : Silmaril.Process.LPS.Word) (t : List WEv) : List XEv :=
  xRun (P3.osStep3 ch) body3Next evBody3 {} {} t

end Silmaril.Wasi.Versions.HttpOs
