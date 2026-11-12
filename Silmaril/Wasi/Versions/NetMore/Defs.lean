module

public import Silmaril.Wasi.Versions.Net.Defs

@[expose] public section

/-!
# More network observations: UDP, name lookup, bind/listen/accept

Relation (d) of `docs/projects/wasm-wasi.md` extended beyond TCP connect and outgoing HTTP
(`Silmaril.Wasi.Versions.Net`). Each slice is a **gated** theory family indexed by an environment
(what the network delivers), with a decisive event that two environments answer differently.
Checked against `specs/wasi/0.2.12/sockets/{udp,udp-create-socket,ip-name-lookup,tcp}.wit` and
`specs/wasi/0.3.2/sockets/ip-name-lookup.wit`.

* **UDP receive** (`udpTh U`, 0.2). `[method]udp-socket.start-bind(self, network, local-address)
  -> result<_, error-code>` binds a socket; `[method]udp-socket.stream(self, remote-address:
  option<ip-socket-address>) -> result<tuple<incoming-datagram-stream,
  outgoing-datagram-stream>, error-code>` ties an incoming stream to the bound address;
  `[method]incoming-datagram-stream.receive(self, max-results: u64) ->
  result<list<incoming-datagram>, error-code>` answers datagrams. An inbox `U : Val → Val → Bool`
  says which `incoming-datagram` records the network delivers to each local address: every
  datagram received on a tied stream is delivered to its address (loss, duplication and
  reordering are allowed). Decisive: a nonempty `ok` list on a tied stream.
* **Name lookup** (`dnsTh R`, 0.2; `dnsTh3 R`, 0.3). 0.2: `resolve-addresses(network, name:
  string) -> result<resolve-address-stream, error-code>`, then
  `[method]resolve-address-stream.resolve-next-address() -> result<option<ip-address>,
  error-code>`; 0.3: `resolve-addresses: async func(name: string) -> result<list<ip-address>,
  error-code>` (sync-lowered). A resolver `R : Val → Val → Bool` says which addresses a name
  has; every address answered is one of them. Decisive: `ok(some a)` (0.2), a nonempty `ok` list
  (0.3).
* **Bind, listen, accept** (`acceptTh P`, 0.2). `[method]tcp-socket.start-bind(self, network,
  local-address)` binds; `[method]tcp-socket.accept() -> result<tuple<tcp-socket,
  input-stream, output-stream>, error-code>` accepts a connection;
  `[method]tcp-socket.remote-address() -> result<ip-socket-address, error-code>` of the
  accepted socket names the peer. Peers `P : Peers` say whether some peer connects to each local
  address (`P.connects`) and which remote addresses do (`P.peer`): `accept` on a socket bound to
  `local` answers `ok` only if some peer connects there, and the accepted socket's
  `remote-address` is a peer of `local`.

Environments are Boolean predicates rather than lists because `Val` has a derived `BEq` but no
lawful decidable equality.
  `start-listen`/`finish-listen` do not observe the network and are left unconstrained.
  Decisive: `accept` answered `ok` on a bound socket.

For each, the "quiet" environment (`udpQuiet`, `dnsEmpty`, `noPeers`) rejects every decisive
answer, so **any** environment and the quiet one admit no common decisive answer.

0.3 UDP (`udp-socket.receive: async func() -> result<tuple<list<u8>, ip-socket-address>,
error-code>`) and 0.3 `listen` (`func() -> result<stream<tcp-socket>, error-code>`, accepted
sockets read from a `stream<tcp-socket>` by `stream.read`) are not stated here.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Names -/

/-- `wasi:sockets/udp.[method]udp-socket.start-bind`. -/
def udpBind : FnName := ⟨"wasi:sockets/udp", "[method]udp-socket.start-bind"⟩
/-- `wasi:sockets/udp.[method]udp-socket.stream`. -/
def udpStream : FnName := ⟨"wasi:sockets/udp", "[method]udp-socket.stream"⟩
/-- `wasi:sockets/udp.[method]incoming-datagram-stream.receive`. -/
def udpReceive : FnName := ⟨"wasi:sockets/udp", "[method]incoming-datagram-stream.receive"⟩
/-- `wasi:sockets/udp-create-socket.create-udp-socket`. -/
def createUdp : FnName := ⟨"wasi:sockets/udp-create-socket", "create-udp-socket"⟩

/-- `wasi:sockets/ip-name-lookup.resolve-addresses` (0.2). -/
def resolve2 : FnName := ⟨"wasi:sockets/ip-name-lookup", "resolve-addresses"⟩
/-- `wasi:sockets/ip-name-lookup.[method]resolve-address-stream.resolve-next-address` (0.2). -/
def resolveNext : FnName :=
  ⟨"wasi:sockets/ip-name-lookup", "[method]resolve-address-stream.resolve-next-address"⟩
/-- `wasi:sockets/ip-name-lookup@0.3.2.resolve-addresses` (async, sync-lowered). -/
def resolve3 : FnName := ⟨"wasi:sockets/ip-name-lookup@0.3.2", "resolve-addresses"⟩

/-- `wasi:sockets/tcp.[method]tcp-socket.start-bind`. -/
def tcpBind : FnName := ⟨"wasi:sockets/tcp", "[method]tcp-socket.start-bind"⟩
/-- `wasi:sockets/tcp.[method]tcp-socket.start-listen`. -/
def tcpListen : FnName := ⟨"wasi:sockets/tcp", "[method]tcp-socket.start-listen"⟩
/-- `wasi:sockets/tcp.[method]tcp-socket.accept`. -/
def tcpAccept : FnName := ⟨"wasi:sockets/tcp", "[method]tcp-socket.accept"⟩
/-- `wasi:sockets/tcp.[method]tcp-socket.remote-address`. -/
def tcpRemote : FnName := ⟨"wasi:sockets/tcp", "[method]tcp-socket.remote-address"⟩

/-! ## UDP -/

/-- An inbox: which `incoming-datagram` records are delivered to each local address. -/
abbrev Inbox : Type := Val → Val → Bool

/-- No datagram arrives anywhere. -/
def udpQuiet : Inbox := fun _ _ => false

/-- The UDP theory state: bound sockets and tied incoming streams, with their local address. -/
structure UdpSt where
  /-- Bound sockets. -/
  bound : List (BitVec 32 × Val) := []
  /-- Incoming streams. -/
  ins : List (BitVec 32 × Val) := []

/-- The next UDP state (independent of the inbox). -/
def udpNext (q : UdpSt) (e : WEv) : UdpSt :=
  match e with
  | .imp f (.u32 s :: _ :: addr :: _) (some [.variant 0 none]) =>
    if f = udpBind then { q with bound := (s, addr) :: q.bound } else q
  | .imp f (.u32 s :: _) (some [.variant 0 (some (.record [.u32 i, _]))]) =>
    if f = udpStream then
      (match lookup s q.bound with
       | some addr => { q with ins := (i, addr) :: q.ins }
       | none => q)
    else q
  | _ => q

/-- A `receive` answer for the datagrams `d` delivered to the stream's address. -/
def recvOk (d : Val → Bool) : Option (List Val) → Bool
  | some [.variant 0 (some (.record l))] => l.all d
  | _ => true

/-- The check of a UDP answer against the inbox `U`. -/
def udpOk (U : Inbox) (q : UdpSt) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 i :: _) r =>
    if f = udpReceive then
      (match lookup i q.ins with
       | some addr => recvOk (U addr) r
       | none => true)
    else true
  | _ => true

/-- **The UDP receive theory** of the inbox `U`. -/
def udpTh (U : Inbox) : Protocol UdpSt WEv := gated {} udpNext (udpOk U)

/-- A decisive UDP event: a nonempty `receive` on a tied stream. -/
def udpDecisive (q : UdpSt) (e : WEv) : Prop :=
  ∃ i a x l, e = .imp udpReceive (.u32 i :: a) (some [.variant 0 (some (.record (x :: l)))]) ∧
    (lookup i q.ins).isSome

/-! ## Name lookup -/

/-- A resolver: which addresses each name has. -/
abbrev Resolver : Type := Val → Val → Bool

/-- No name resolves. -/
def dnsEmpty : Resolver := fun _ _ => false

/-- The 0.2 name lookup state: the name of each `resolve-address-stream`. -/
abbrev DnsSt : Type := List (BitVec 32 × Val)

/-- The next 0.2 name lookup state. -/
def dnsNext (q : DnsSt) (e : WEv) : DnsSt :=
  match e with
  | .imp f (_ :: name :: _) (some [.variant 0 (some (.u32 st))]) =>
    if f = resolve2 then (st, name) :: q else q
  | _ => q

/-- A `resolve-next-address` answer for the addresses `d`. -/
def nextOk (d : Val → Bool) : Option (List Val) → Bool
  | some [.variant 0 (some (.variant 1 (some a)))] => d a
  | _ => true

/-- The check of a 0.2 name lookup answer against `R`. -/
def dnsOk (R : Resolver) (q : DnsSt) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 st :: _) r =>
    if f = resolveNext then
      (match lookup st q with
       | some name => nextOk (R name) r
       | none => true)
    else true
  | _ => true

/-- **The 0.2 name lookup theory** of the resolver `R`. -/
def dnsTh (R : Resolver) : Protocol DnsSt WEv := gated [] dnsNext (dnsOk R)

/-- A decisive 0.2 name lookup event: `ok(some a)` on a stream of a name. -/
def dnsDecisive (q : DnsSt) (e : WEv) : Prop :=
  ∃ st a x, e = .imp resolveNext (.u32 st :: a) (some [.variant 0 (some (.variant 1 (some x)))]) ∧
    (lookup st q).isSome

/-- A 0.3 `resolve-addresses` answer for the addresses `d`. -/
def listOk (d : Val → Bool) : Option (List Val) → Bool
  | some [.variant 0 (some (.record l))] => l.all d
  | _ => true

/-- The check of a 0.3 name lookup answer against `R`. -/
def dnsOk3 (R : Resolver) (_ : Unit) (e : WEv) : Bool :=
  match e with
  | .imp f (name :: _) r => if f = resolve3 then listOk (R name) r else true
  | _ => true

/-- **The 0.3 name lookup theory** of the resolver `R`. -/
def dnsTh3 (R : Resolver) : Protocol Unit WEv := gated () (fun _ _ => ()) (dnsOk3 R)

/-- A decisive 0.3 name lookup event: a nonempty `ok` list. -/
def dnsDecisive3 (_ : Unit) (e : WEv) : Prop :=
  ∃ name a x l, e = .imp resolve3 (name :: a) (some [.variant 0 (some (.record (x :: l)))])

/-! ## Bind, listen, accept -/

/-- Peers: whether some peer connects to each local address, and which remote addresses do. -/
structure Peers where
  /-- Some peer connects to the local address. -/
  connects : Val → Bool
  /-- The remote address is a peer of the local address. -/
  peer : Val → Val → Bool

/-- Nobody connects anywhere. -/
def noPeers : Peers := ⟨fun _ => false, fun _ _ => false⟩

/-- The accept state: bound sockets and accepted sockets, with their local address. -/
structure AccSt where
  /-- Bound sockets. -/
  bound : List (BitVec 32 × Val) := []
  /-- Accepted sockets. -/
  acc : List (BitVec 32 × Val) := []

/-- The next accept state. -/
def accNext (q : AccSt) (e : WEv) : AccSt :=
  match e with
  | .imp f (.u32 s :: _ :: addr :: _) (some [.variant 0 none]) =>
    if f = tcpBind then { q with bound := (s, addr) :: q.bound } else q
  | .imp f (.u32 s :: _) (some [.variant 0 (some (.record [.u32 c, _, _]))]) =>
    if f = tcpAccept then
      (match lookup s q.bound with
       | some addr => { q with acc := (c, addr) :: q.acc }
       | none => q)
    else q
  | _ => q

/-- An `accept` answer when some peer connects (`c`) or not. -/
def acceptOk (c : Bool) : Option (List Val) → Bool
  | some [.variant 0 _] => c
  | _ => true

/-- A `remote-address` answer of an accepted socket whose peers are `d`. -/
def remoteOk (d : Val → Bool) : Option (List Val) → Bool
  | some [.variant 0 (some a)] => d a
  | _ => true

/-- The check of an accept answer against `P`. -/
def accOk (P : Peers) (q : AccSt) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 s :: _) r =>
    if f = tcpAccept then
      (match lookup s q.bound with
       | some addr => acceptOk (P.connects addr) r
       | none => true)
    else if f = tcpRemote then
      (match lookup s q.acc with
       | some addr => remoteOk (P.peer addr) r
       | none => true)
    else true
  | _ => true

/-- **The bind/listen/accept theory** of the peers `P`. -/
def acceptTh (P : Peers) : Protocol AccSt WEv := gated {} accNext (accOk P)

/-- A decisive accept event: `accept` answered `ok` on a bound socket. -/
def accDecisive (q : AccSt) (e : WEv) : Prop :=
  ∃ s a v, e = .imp tcpAccept (.u32 s :: a) (some [.variant 0 v]) ∧ (lookup s q.bound).isSome

/-! ## Implementations over preview1 -/

/-- A component importing preview1 **implements a gated theory family over preview1**: for
every environment `x` and every preview1 host model `η`, `link η σ` is a model of the theory of
`x`. -/
def ObsOverP1 {E S : Type} (init : S) (next : S → WEv → S) (ok : E → S → WEv → Bool)
    {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) : Prop :=
  ∀ (x : E) (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports),
    (hostSat P1.th.Accepts).holds η → (hostSat (gated init next (ok x)).Accepts).holds (link η σ)

/-- The composite has a decisive event over some preview1 host model. -/
def ObsResponsive {S : Type} (init : S) (next : S → WEv → S) (D : S → WEv → Prop)
    {X : Set FnName} (σ : Silmaril.Games.Strategy (nsig P1.imports) (nsig X)) : Prop :=
  ∃ (Y : Silmaril.Games.Sig.{0}) (η : Host Y P1.imports), (hostSat P1.th.Accepts).holds η ∧
    ∃ p ∈ link η σ, Decides init next D (htrace p)

end Silmaril.Wasi.Versions.Net
