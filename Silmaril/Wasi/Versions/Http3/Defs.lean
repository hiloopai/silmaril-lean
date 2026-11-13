module

public import Silmaril.Wasi.Versions.Net.Defs

@[expose] public section

/-!
# WASI 0.3 `wasi:http` (outgoing requests) as a theory

Checked against `specs/wasi/0.3.2/http/{worlds,types}.wit`:

* `wasi:http/client@0.3.2` `send: async func(request: request) -> result<response, error-code>`
  (`send3`, observed sync-lowered as in `Silmaril.Wasi.Versions.P3`); the `handler.handle` export
  has the same type;
* `wasi:http/types@0.3.2` `[method]request.set-authority(authority: option<string>) -> result`,
  `[method]request.set-path-with-query(path-with-query: option<string>) -> result`
  (`setAuth3`, `setPath3`; `result` without payloads);
* `[method]response.get-status-code() -> status-code` (`getStatus3`, `status-code = u16`).

0.3 has no `future-incoming-response`: the async `send` returns the response. The `error-code`
variant begins with `DNS-timeout` (case `0`) in both versions.

`httpTh3 W` for a web `W : Web` (as `Net.httpTh`): an answer of `send(r)` is `ok(response)`
when `W` answers a status for the authority and path set on `r`, `error(k)` when `W` fails
with `k`, or a trap (a safety theory, as `tcpTh3`); `get-status-code` of a response of `r`
answers `W`'s status. Decisive: a `send` that does not trap (`webUp`/`webDown` admit no common
one). `httpImpl3 W` is the concrete host. Bodies, headers, trailers and request options
(`request.new` with its `stream<u8>`/`future` contents) are not part of the slice.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- `wasi:http/client@0.3.2.send` (async, observed sync-lowered). -/
def send3 : FnName := ⟨"wasi:http/client@0.3.2", "send"⟩
/-- `wasi:http/types@0.3.2.[method]request.set-authority`. -/
def setAuth3 : FnName := ⟨"wasi:http/types@0.3.2", "[method]request.set-authority"⟩
/-- `wasi:http/types@0.3.2.[method]request.set-path-with-query`. -/
def setPath3 : FnName := ⟨"wasi:http/types@0.3.2", "[method]request.set-path-with-query"⟩
/-- `wasi:http/types@0.3.2.[method]response.get-status-code`. -/
def getStatus3 : FnName := ⟨"wasi:http/types@0.3.2", "[method]response.get-status-code"⟩

/-- The 0.3 `wasi:http` functions of this slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `http3Fns_eq`. -/
def http3Fns : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.http3T) WitImport.http3Keys}

/-- **The imported functions of `http3Fns` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem http3Fns_eq : http3Fns = {send3, setAuth3, setPath3, getStatus3} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.http3T) WitImport.http3Keys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.http3T) WitImport.http3Keys).Perm [send3, setAuth3, setPath3, getStatus3] by decide +kernel).mem_iff]
  simp

/-- The theory state: authorities and paths set on requests, the request of each response. -/
structure Http3St where
  /-- Authorities set on requests. -/
  auth : List (BitVec 32 × Val) := []
  /-- Paths set on requests. -/
  path : List (BitVec 32 × Val) := []
  /-- The authority and path of the request of each response. -/
  resps : List (BitVec 32 × (Val × Val)) := []

/-- The authority and path of the request `r`. -/
def Http3St.key (q : Http3St) (r : BitVec 32) : Val × Val :=
  ((lookup r q.auth).getD noneV, (lookup r q.path).getD noneV)

/-- The next state (independent of the web). -/
def http3Next (q : Http3St) (e : WEv) : Http3St :=
  match e with
  | .imp f (.u32 r :: v :: _) (some [.variant 0 none]) =>
    if f = setAuth3 then { q with auth := (r, v) :: q.auth }
    else if f = setPath3 then { q with path := (r, v) :: q.path }
    else q
  | .imp f (.u32 r :: _) (some [.variant 0 (some (.u32 rs))]) =>
    if f = send3 then { q with resps := (rs, q.key r) :: q.resps } else q
  | _ => q

/-- A `send` answer for the outcome `o`. -/
def sendOk : HttpOutcome → Option (List Val) → Bool
  | .status _, some [.variant 0 (some (.u32 _))] => true
  | .error k, some [.variant 1 (some (.variant k' _))] => k' == k
  | _, _ => false

/-- The check of an answer against the web `W`. -/
def http3Ok (W : Web) (q : Http3St) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 r :: _) res =>
    if f = send3 then res.isNone || sendOk (W (q.key r).1 (q.key r).2) res
    else if f = getStatus3 then
      (match lookup r q.resps with
       | some k => statusOk W k res
       | none => true)
    else true
  | _ => true

/-- **The 0.3 outgoing HTTP theory** of the web `W`. -/
def httpTh3 (W : Web) : Protocol Http3St WEv := gated {} http3Next (http3Ok W)

/-- A decisive 0.3 HTTP event: a `send` that does not trap. -/
def httpDecisive3 (_ : Http3St) (e : WEv) : Prop :=
  ∃ r a res, e = .imp send3 (.u32 r :: a) (some res)

/-- The state after the answers `p`. -/
def http3State (p : List WEv) : Http3St := p.foldl http3Next {}

/-- The answer of `send` for an outcome (a fresh response handle). -/
def sendAns (n : Nat) : HttpOutcome → Option (List Val)
  | .status _ => some [okV (some (.u32 (BitVec.ofNat 32 n)))]
  | .error k => some [errV (some (.variant k none))]

/-- The status of a response of the request `k`. -/
def statusAns (W : Web) (k : Val × Val) : Option (List Val) :=
  match W k.1 k.2 with
  | .status s => some [.u16 s]
  | .error _ => some [.u16 200]

/-- **The concrete 0.3 HTTP host of the web `W`.** -/
def httpImpl3 (W : Web) : Impl := fun p f a =>
  if f = setAuth3 ∨ f = setPath3 then some [okV none]
  else if f = send3 then
    (match a with
     | .u32 r :: _ => sendAns p.length (W ((http3State p).key r).1 ((http3State p).key r).2)
     | _ => none)
  else if f = getStatus3 then
    (match a with
     | .u32 rs :: _ =>
       (match lookup rs (http3State p).resps with
        | some k => statusAns W k
        | none => some [.u16 200])
     | _ => some [.u16 200])
  else none

end Silmaril.Wasi.Versions.Net
