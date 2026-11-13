module

public import Silmaril.Wasi.Versions.P1.Theory.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs
public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.WitImport.Derived.Defs

@[expose] public section

/-!
# WASI 0.2 `wasi:sockets` (TCP connect) and `wasi:http` (outgoing handler) as theories

Checked against the vendored WIT `specs/wasi/0.2.12/sockets/{tcp,network,tcp-create-socket,
instance-network}.wit` and `specs/wasi/0.2.12/http/{handler,types}.wit` (the same signatures
as `specs/wasi/v0.2.9`; only the `@0.2.x` package versions differ). These are the parts of
0.2 that observe a **network**: a TCP connect to an address, and the response to an outgoing
HTTP request. Preview1 has no such call: its socket functions `sock_accept`, `sock_recv`,
`sock_send`, `sock_shutdown` act on descriptors that already exist (`p1_sock_fns`), and the
official adapter answers them with `unreachable!()` or `errno::notsock` (`adapter/lib.rs`).

## Functions

* `wasi:sockets/tcp.[method]tcp-socket.start-connect(self, network, remote-address)
  -> result<_, error-code>` and `finish-connect(self) -> result<tuple<input-stream,
  output-stream>, error-code>`; `wasi:sockets/tcp-create-socket.create-tcp-socket` and
  `wasi:sockets/instance-network.instance-network` (`tcpImports`).
* `wasi:http/outgoing-handler.handle(request, options) -> result<future-incoming-response,
  error-code>`, `wasi:http/types.[method]outgoing-request.set-authority`,
  `set-path-with-query`, `[method]future-incoming-response.get() ->
  option<result<result<incoming-response, error-code>>>`, `[method]incoming-response.status()
  -> status-code` (`httpImports`).

Values use the encodings of `Silmaril.Wasi.Theory` (`result`: `ok = 0`, `err = 1`; `option`:
`none = 0`, `some = 1`; enums are payload-free variants; handles are `u32`). The
`wasi:sockets/network.error-code` tags used: `not-in-progress = 7`, `would-block = 8`,
`connection-refused = 14`; `wasi:http/types.error-code`: `DNS-timeout = 0`.

## The theories: required observations relative to a network

A theory family is **gated** (`gated init next ok`): its state evolves by `next`, independently
of the network, and each answer is checked by `ok`, which depends on the network.

* `tcpTh N` for a network `N : Network` (the outcome of a connection to each address: `none`
  accepted, `some k` refused with `error-code` `k`): after `start-connect(s, _, addr)` answered
  `ok`, an answer of `finish-connect(s)` is `error(would-block)` (still in progress) or the
  outcome `N addr`: `ok(tuple<input-stream, output-stream>)` or `error(k)`. A decided connect
  is no longer pending.
* `httpTh W` for a web `W : Web` (the outcome of a request for an authority and a
  path-with-query: a status code or an `error-code`): `handle(r)` answered `ok(f)` ties the
  future `f` to the authority and path set on `r`; `get(f)` answers `none` (not ready),
  `some(err)` (already retrieved), or `some(ok(outcome))` matching `W`; the `status` of the
  response it returns is `W`'s status.

The **decisive** events (`TcpDecides`, `HttpDecides`): a `finish-connect` of a pending socket
answered other than `would-block`; a `get` of a tied future answered `some(ok(_))`.
`netUp`/`netDown` (every connection accepted / refused) and `webUp`/`webDown` (every request
answered `200` / `error(DNS-timeout)`) admit no common decisive answer.

## Concrete hosts

`tcpImpl N` and `httpImpl W` answer from the theory state of the answers so far; they are
models of `tcpTh N` and `httpTh W` (`Silmaril.Wasi.Versions.Net.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Gated protocols -/

/-- A protocol whose state evolves by `next` and whose events are checked by `ok`. -/
def gated {S : Type} (init : S) (next : S → WEv → S) (ok : S → WEv → Bool) : Protocol S WEv :=
  ⟨init, fun q e => if ok q e then some (next q e) else none⟩

/-- `t` has a decisive event: an event `e` with `D q e` in the state `q` reached before it. -/
def Decides {S : Type} (init : S) (next : S → WEv → S) (D : S → WEv → Prop) (t : List WEv) :
    Prop :=
  ∃ u e v, t = u ++ e :: v ∧ D (u.foldl next init) e

/-- The value of the key `k` in an association list. -/
def lookup {α : Type} (k : BitVec 32) (l : List (BitVec 32 × α)) : Option α :=
  (l.find? (·.1 == k)).map (·.2)

/-- The tag of a single-variant answer. -/
def resTag : Option (List Val) → Option Nat
  | some [.variant t _] => some t
  | _ => none

/-! ## `wasi:sockets` -/

/-- `wasi:sockets/instance-network.instance-network`. -/
def instanceNetwork : FnName := ⟨"wasi:sockets/instance-network", "instance-network"⟩
/-- `wasi:sockets/tcp-create-socket.create-tcp-socket`. -/
def createTcp : FnName := ⟨"wasi:sockets/tcp-create-socket", "create-tcp-socket"⟩
/-- `wasi:sockets/tcp.[method]tcp-socket.start-connect`. -/
def startConnect : FnName := ⟨"wasi:sockets/tcp", "[method]tcp-socket.start-connect"⟩
/-- `wasi:sockets/tcp.[method]tcp-socket.finish-connect`. -/
def finishConnect : FnName := ⟨"wasi:sockets/tcp", "[method]tcp-socket.finish-connect"⟩

/-- The `wasi:sockets` functions of this slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `tcpImports_eq`. -/
def tcpImports : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.sock2T) WitImport.tcpKeys}

/-- **The imported functions of `tcpImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem tcpImports_eq : tcpImports = {instanceNetwork, createTcp, startConnect, finishConnect} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.sock2T) WitImport.tcpKeys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.sock2T) WitImport.tcpKeys).Perm [instanceNetwork, createTcp, startConnect, finishConnect] by decide +kernel).mem_iff]
  simp

/-- `error-code.not-in-progress`. -/
abbrev eNotInProgress : Nat := 7
/-- `error-code.would-block`. -/
abbrev eWouldBlock : Nat := 8
/-- `error-code.connection-refused`. -/
abbrev eConnRefused : Nat := 14

/-- A network: the outcome of a TCP connection to each `ip-socket-address` (`none`: accepted;
`some k`: failed with the `error-code` tag `k`). -/
abbrev Network : Type := Val → Option Nat

/-- Every connection is accepted. -/
def netUp : Network := fun _ => none

/-- Every connection is refused. -/
def netDown : Network := fun _ => some eConnRefused

/-- An `error(k)` answer. -/
def errAnsN (k : Nat) : Option (List Val) := some [errV (some (.variant k none))]

/-- `error(would-block)`. -/
def isWouldBlock : Option (List Val) → Bool
  | some [.variant 1 (some (.variant 8 none))] => true
  | _ => false

/-- An answer of `finish-connect` for the outcome `o`. -/
def connectOk : Option Nat → Option (List Val) → Bool
  | none, some [.variant 0 (some (.record [.u32 _, .u32 _]))] => true
  | some k, some [.variant 1 (some (.variant k' none))] => k' == k
  | _, _ => false

/-- The theory state: the pending connects, by socket, with their addresses. -/
abbrev TcpSt : Type := List (BitVec 32 × Val)

/-- The next state (independent of the network). -/
def tcpNext (q : TcpSt) (e : WEv) : TcpSt :=
  match e with
  | .imp f a r =>
    if f = startConnect then
      (match a, r with
       | .u32 s :: _ :: addr :: _, some [.variant 0 none] => (s, addr) :: q
       | _, _ => q)
    else if f = finishConnect then
      (match a with
       | .u32 s :: _ => if isWouldBlock r then q else q.filter (·.1 != s)
       | _ => q)
    else q
  | _ => q

/-- The check of an answer against the network `N`. -/
def tcpOk (N : Network) (q : TcpSt) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 s :: _) r =>
    if f = finishConnect then
      (match lookup s q with
       | some addr => isWouldBlock r || connectOk (N addr) r
       | none => true)
    else true
  | _ => true

/-- **The TCP connect theory** of the network `N`. -/
def tcpTh (N : Network) : Protocol TcpSt WEv := gated [] tcpNext (tcpOk N)

/-- A decisive TCP event: `finish-connect` of a pending socket, not answered `would-block`. -/
def tcpDecisive (q : TcpSt) (e : WEv) : Prop :=
  ∃ s a r, e = .imp finishConnect (.u32 s :: a) r ∧ (lookup s q).isSome ∧ isWouldBlock r = false

/-- The answers decide a TCP connect. -/
def TcpDecides (t : List WEv) : Prop := Decides [] tcpNext tcpDecisive t

/-- The state of the TCP theory after the answers `p`. -/
def tcpState (p : List WEv) : TcpSt := p.foldl tcpNext []

/-- The answer of `finish-connect` for the outcome `o` (fresh stream handles). -/
def connectAns (n : Nat) : Option Nat → Option (List Val)
  | none => some [okV (some (.record [.u32 (BitVec.ofNat 32 n), .u32 (BitVec.ofNat 32 (n + 1))]))]
  | some k => errAnsN k

/-- The `self` handle of a method call. -/
def selfH : List Val → BitVec 32
  | .u32 h :: _ => h
  | _ => 0

/-- **The concrete TCP host of the network `N`**: fresh handles; `start-connect` succeeds;
`finish-connect` answers `N`'s outcome for a pending socket and `not-in-progress` otherwise. -/
def tcpImpl (N : Network) : Impl := fun p f a =>
  if f = instanceNetwork then some [.u32 (BitVec.ofNat 32 p.length)]
  else if f = createTcp then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = startConnect then some [okV none]
  else if f = finishConnect then
    (match lookup (selfH a) (tcpState p) with
     | some addr => connectAns p.length (N addr)
     | none => errAnsN eNotInProgress)
  else none

/-! ## `wasi:http` -/

/-- `wasi:http/outgoing-handler.handle`. -/
def httpHandle : FnName := ⟨"wasi:http/outgoing-handler", "handle"⟩
/-- `wasi:http/types.[method]outgoing-request.set-authority`. -/
def setAuthority : FnName := ⟨"wasi:http/types", "[method]outgoing-request.set-authority"⟩
/-- `wasi:http/types.[method]outgoing-request.set-path-with-query`. -/
def setPath : FnName := ⟨"wasi:http/types", "[method]outgoing-request.set-path-with-query"⟩
/-- `wasi:http/types.[method]future-incoming-response.get`. -/
def futGet : FnName := ⟨"wasi:http/types", "[method]future-incoming-response.get"⟩
/-- `wasi:http/types.[method]incoming-response.status`. -/
def respStatus : FnName := ⟨"wasi:http/types", "[method]incoming-response.status"⟩

/-- The `wasi:http` functions of this slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `httpImports_eq`. -/
def httpImports : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.http2T) WitImport.httpKeys}

/-- **The imported functions of `httpImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem httpImports_eq : httpImports = {httpHandle, setAuthority, setPath, futGet, respStatus} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.http2T) WitImport.httpKeys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.http2T) WitImport.httpKeys).Perm [httpHandle, setAuthority, setPath, futGet, respStatus] by decide +kernel).mem_iff]
  simp

/-- The outcome of an outgoing request: a status code, or an `error-code` tag. -/
inductive HttpOutcome where
  | status (s : BitVec 16)
  | error (k : Nat)

/-- A web: the outcome of a request for an authority and a path-with-query (both as their
`option<string>` values). -/
abbrev Web : Type := Val → Val → HttpOutcome

/-- Every request is answered `200`. -/
def webUp : Web := fun _ _ => .status 200

/-- Every request fails with `DNS-timeout`, its case number read from the vendored WIT. -/
def webDown : Web := fun _ _ => .error WitImport.eDnsTimeout3W

/-- `webDown` fails with case `0`: `DNS-timeout` is the first case of the imported 0.3 HTTP
`error-code` (kernel-checked). -/
theorem webDown_eq_hand : webDown = fun _ _ => .error 0 := by
  have h : WitImport.eDnsTimeout3W = 0 := by decide +kernel
  funext a p
  show HttpOutcome.error WitImport.eDnsTimeout3W = .error 0
  rw [h]

/-- The theory state: authorities and paths set on requests, the request of each future and
of each response. -/
structure HttpSt where
  /-- Authorities set on requests. -/
  auth : List (BitVec 32 × Val)
  /-- Paths set on requests. -/
  path : List (BitVec 32 × Val)
  /-- The authority and path of the request of each future. -/
  futs : List (BitVec 32 × (Val × Val))
  /-- The authority and path of the request of each response. -/
  resps : List (BitVec 32 × (Val × Val))

/-- The initial state. -/
def HttpSt.init : HttpSt := ⟨[], [], [], []⟩

/-- `option::none`. -/
def noneV : Val := .variant 0 none

/-- The next state (independent of the web). -/
def httpNext (q : HttpSt) (e : WEv) : HttpSt :=
  match e with
  | .imp f (.u32 r :: v :: _) (some [.variant 0 none]) =>
    if f = setAuthority then { q with auth := (r, v) :: q.auth }
    else if f = setPath then { q with path := (r, v) :: q.path }
    else q
  | .imp f (.u32 r :: _) (some [.variant 0 (some (.u32 fu))]) =>
    if f = httpHandle then
      { q with futs := (fu, ((lookup r q.auth).getD noneV, (lookup r q.path).getD noneV)) :: q.futs }
    else q
  | .imp f (.u32 fu :: _) (some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.u32 rs))))))]) =>
    if f = futGet then
      (match lookup fu q.futs with
       | some k => { q with resps := (rs, k) :: q.resps }
       | none => q)
    else q
  | _ => q

/-- An inner `result<incoming-response, error-code>` matching the outcome. -/
def outcomeOk : HttpOutcome → Val → Bool
  | .status _, .variant 0 (some (.u32 _)) => true
  | .error k, .variant 1 (some (.variant k' _)) => k' == k
  | _, _ => false

/-- An answer of `get` on a future of the request `k`. -/
def getOk (W : Web) (k : Val × Val) : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | some [.variant 1 (some (.variant 1 none))] => true
  | some [.variant 1 (some (.variant 0 (some x)))] => outcomeOk (W k.1 k.2) x
  | _ => false

/-- An answer of `status` on a response of the request `k` (unconstrained when the request
fails: no such response exists in a run of the theory). -/
def statusOk (W : Web) (k : Val × Val) (r : Option (List Val)) : Bool :=
  match W k.1 k.2 with
  | .status s => (match r with | some [.u16 s'] => s' == s | _ => false)
  | .error _ => true

/-- The check of an answer against the web `W`. -/
def httpOk (W : Web) (q : HttpSt) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 h :: _) r =>
    if f = futGet then
      (match lookup h q.futs with
       | some k => getOk W k r
       | none => true)
    else if f = respStatus then
      (match lookup h q.resps with
       | some k => statusOk W k r
       | none => true)
    else true
  | _ => true

/-- **The outgoing HTTP theory** of the web `W`. -/
def httpTh (W : Web) : Protocol HttpSt WEv := gated HttpSt.init httpNext (httpOk W)

/-- A decisive HTTP event: `get` of a tied future answered `some(ok(_))`. -/
def httpDecisive (q : HttpSt) (e : WEv) : Prop :=
  ∃ h a x, e = .imp futGet (.u32 h :: a) (some [.variant 1 (some (.variant 0 (some x)))]) ∧
    (lookup h q.futs).isSome

/-- The answers decide an outgoing request. -/
def HttpDecides (t : List WEv) : Prop := Decides HttpSt.init httpNext httpDecisive t

/-- The state of the HTTP theory after the answers `p`. -/
def httpState (p : List WEv) : HttpSt := p.foldl httpNext HttpSt.init

/-- The inner result of `get` for an outcome (a fresh response handle). -/
def outcomeV (n : Nat) : HttpOutcome → Val
  | .status _ => okV (some (.u32 (BitVec.ofNat 32 n)))
  | .error k => errV (some (.variant k none))

/-- **The concrete HTTP host of the web `W`**: fresh handles; setters succeed; `get` of a tied
future answers `some(ok(W's outcome))` and of another future `some(err)`; `status` answers
`W`'s status (`200` for an untied response). -/
def httpImpl (W : Web) : Impl := fun p f a =>
  if f = setAuthority ∨ f = setPath then some [okV none]
  else if f = httpHandle then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = futGet then
    (match lookup (selfH a) (httpState p).futs with
     | some k => some [.variant 1 (some (okV (some (outcomeV p.length (W k.1 k.2)))))]
     | none => some [.variant 1 (some (errV none))])
  else if f = respStatus then
    (match lookup (selfH a) (httpState p).resps with
     | some k => (match W k.1 k.2 with
       | .status s => some [.u16 s]
       | .error _ => some [.u16 200])
     | none => some [.u16 200])
  else none

/-- A system: what preview1 observes of it, its network and its web. -/
structure Sys (O : Type) where
  /-- The part of the system preview1 observes. -/
  obs : O
  /-- The network. -/
  net : Network
  /-- The web. -/
  web : Web

/-! ## Implementations over preview1 -/

/-- A component importing preview1 **implements the TCP theory over preview1**: for every
network `N` and every host model `η` of the preview1 theory, `link η σ` is a model of
`tcpTh N`. -/
def TcpOverP1 {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) : Prop :=
  ∀ (N : Network) (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports),
    (hostSat P1.th.Accepts).holds η → (hostSat (tcpTh N).Accepts).holds (link η σ)

/-- The same for the HTTP theory. -/
def HttpOverP1 {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) : Prop :=
  ∀ (W : Web) (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports),
    (hostSat P1.th.Accepts).holds η → (hostSat (httpTh W).Accepts).holds (link η σ)

/-- The composite **decides a connect** over some preview1 host model. -/
def TcpResponsive {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) : Prop :=
  ∃ (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports), (hostSat P1.th.Accepts).holds η ∧
    ∃ p ∈ link η σ, TcpDecides (htrace p)

/-- The composite **decides a request** over some preview1 host model. -/
def HttpResponsive {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) :
    Prop :=
  ∃ (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports), (hostSat P1.th.Accepts).holds η ∧
    ∃ p ∈ link η σ, HttpDecides (htrace p)

end Silmaril.Wasi.Versions.Net
