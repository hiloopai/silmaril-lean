module

public import Silmaril.Wasi.Versions.HttpOs.Defs

@[expose] public section

/-!
# The OS image of WASI HTTP with trailers

A variant of `Silmaril.Wasi.Versions.HttpOs` that also images the trailers of a response. In the
same vocabulary (`IoSpecNet` socket events, the exchange of the request of key `k` observed at
`keyV k`), the answer `x` of 0.2 `fields.entries(t)` / 0.3 `fields.copy-all(t)` on a tracked
trailer resource `t` of the request `k` is the event `recv (keyV k) x`.

* **The network** `httpNetT B`: the network `httpNet B.web B.body` of `HttpOs`, whose inbox
  at `keyV k` also admits a value that decodes (`fieldsOf`) to the trailers of the web's
  response, and any value when the web gives none (a failed request, or a response without
  trailers, where the theories do not constrain `entries` either).
* **Events** `evBodyT2`, `evBodyT3`: `evBody2`/`evBody3` followed by the trailer event.

**Not imaged**: headers (the body web `BWeb` has no response headers, and the request headers a
process sends would be `send` events, which every network admits), outgoing bodies and
`subscribe`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.HttpOs

open Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-- A trailers value the web admits for the request of key `k`. -/
def trailIn (B : BWeb) (k : Val × Val) (d : Val) : Bool :=
  match B.trailers k with
  | some l => fieldsOf d == some l
  | none => true

/-- The inbox of a request address: status, body chunks and trailers. -/
def inboxT (B : BWeb) : Val → Val → Bool
  | .record [a, p], d => inboxOf B.web B.body (.record [a, p]) d || trailIn B (a, p) d
  | _, _ => false

/-- **The network of the body web `B`, with trailers.** -/
def httpNetT (B : BWeb) : NetEnv Val :=
  ⟨connOf B.web, inboxT B, fun _ _ => false, fun _ _ => false⟩

/-- The trailers event of a 0.2 `entries` answer. -/
def trEv2 (q : BodySt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 h :: _) (some [x]) =>
    if f = entries2 then
      match lookup h q.trs with
      | some (some k) => [.recv (keyV k) x]
      | _ => []
    else []
  | _ => []

/-- The trailers event of a 0.3 `copy-all` answer. -/
def trEv3 (q : Body3St) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 h :: _) (some [x]) =>
    if f = copyAll3 then
      match lookup h q.trs with
      | some (some k) => [.recv (keyV k) x]
      | _ => []
    else []
  | _ => []

/-- The socket events of a 0.2 HTTP answer with bodies and trailers. -/
def evBodyT2 (q : BodySt) (e : WEv) : List (SockEv Val) := evBody2 q e ++ trEv2 q e

/-- The socket events of a 0.3 HTTP answer with bodies and trailers. -/
def evBodyT3 (q : Body3St) (e : WEv) : List (SockEv Val) := evBody3 q e ++ trEv3 q e

end Silmaril.Wasi.Versions.HttpOs
