module

public import Silmaril.Servers.Core.Defs
public import Mathlib.Data.Set.Image

/-!
# Transports: ports, sockets and their traces, shared by stream and datagram protocols

A narrow, protocol-neutral vocabulary for what a server does at its sockets, used by the
TCP readings of HTTP (`Silmaril.Servers.Tcp`) and meant for the UDP/QUIC ones. It describes
what an application observes through a **socket API**: the reliable byte stream of TCP
(RFC 9293 §2.2) or the datagrams of UDP (RFC 768). It is *not* a packet-level model: nothing
here refines `Silmaril.Net.Tcp.Transfer` or `Silmaril.Net.Udp`, and no theorem relates the two.

## Events and traces

`TEv Addr` is one socket event of a server, `Addr` being the type of peer addresses (left
abstract; `Silmaril.Net.Ip.Addr` is one choice):

| event | stream transport (TCP) | datagram transport (UDP) |
| --- | --- | --- |
| `bind p` | listen on port `p` | bind port `p` |
| `open_ p c a` | connection `c` accepted on `p` from `a` | flow `c` (the pair `p`, `a`) first seen |
| `recv c bs` | octets read on `c` (chunking is not meaningful) | one datagram received on flow `c` |
| `send c bs` | octets written on `c` | one datagram sent on flow `c` |
| `eof c` | the peer closed its direction (RECEIVE reported end of stream) | not used |
| `close c` | the server closed its direction (CLOSE) | the server forgot the flow |
| `reset c` | the connection was reset (abortive close) | not used |
| `fail p` | binding `p` failed (initialization failure) | the same |

A trace (`TTrace Addr`) lists them in order; a model (`TModel Addr`) is a set of traces, and
**refinement is trace inclusion** (`TModel.Refines`, implementation first), as in the server
core. The kind of transport (`Kind`) says how a flow's payload is read: concatenated octets
(`streamIn`, `streamOut`) or the list of datagrams (`unitsIn`, `unitsOut`).

## Partial observation maps

A higher-level reading of a transport trace (HTTP requests and responses out of octets) is
partial: octets may hold an incomplete or malformed message. `PMap α β := α → Option β` is
such a reading, with:

* `PMap.image f M`: what the reading sees of a model (defined points only);
* `PMap.pull f φ`: a sentence about readings, read on the source (true where undefined).

The satisfaction law holds for every universal sentence (`Thms.PMap.sat_pull_iff`), and the image
is monotone (`Thms.PMap.image_mono`), so refinement goes to the reading. This is a
**partial observation map**, not a comorphism: there is no translation of models backwards,
existential (may) properties are not reflected when the reading is undefined
(`Thms.PMap.not_may_reflect`), and undefined points are where errors live. `PMap.Total f M`
states that a model never leaves the reading's domain.

## Stream readings expose what is left over

`Parse Msg` is the result of reading a stream: the complete messages, the octets after the
last of them (`rest`) and whether reading stopped at an error (`err`). Every reading of
octets here returns all three; none silently drops a leftover or a malformed tail.

## Protocol selection is an assumption

`Select` records how a server decides which application protocol a connection speaks
(HTTP/1.1 by default, HTTP/2 by prior knowledge with its preface, `h2c` upgrade, ALPN under
TLS). Theorems about one protocol take the selection as a hypothesis; no theorem claims that
a server speaks every protocol or that versions are compatible.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Transport

/-- The kind of a transport: a byte stream or datagrams. -/
inductive Kind where
  | stream
  | datagram
  deriving DecidableEq, Repr

/-- A port number. -/
abbrev Port : Type := Nat

/-- A connection (stream) or flow (datagram), in order of first appearance. -/
abbrev Conn : Type := Nat

/-- **A socket event** of a server. -/
inductive TEv (Addr : Type) where
  | bind (p : Port)
  | open_ (p : Port) (c : Conn) (a : Addr)
  | recv (c : Conn) (bs : List UInt8)
  | send (c : Conn) (bs : List UInt8)
  | eof (c : Conn)
  | close (c : Conn)
  | reset (c : Conn)
  | fail (p : Port)
  deriving DecidableEq, Repr

/-- **A transport trace.** -/
abbrev TTrace (Addr : Type) : Type := List (TEv Addr)

/-- **A transport model**: the traces a server can be observed doing at its sockets. -/
abbrev TModel (Addr : Type) : Type := Set (TTrace Addr)

/-- Refinement, implementation first: trace inclusion. -/
def TModel.Refines {Addr : Type} (I S : TModel Addr) : Prop := I ⊆ S

variable {Addr : Type}

/-- The datagrams (or chunks) received on `c`, in order. -/
def unitsIn (c : Conn) : TTrace Addr → List (List UInt8)
  | [] => []
  | .recv c' bs :: t => if c' = c then bs :: unitsIn c t else unitsIn c t
  | _ :: t => unitsIn c t

/-- The datagrams (or chunks) sent on `c`, in order. -/
def unitsOut (c : Conn) : TTrace Addr → List (List UInt8)
  | [] => []
  | .send c' bs :: t => if c' = c then bs :: unitsOut c t else unitsOut c t
  | _ :: t => unitsOut c t

/-- The octets received on `c` (a stream reading: chunk boundaries are forgotten). -/
def streamIn (c : Conn) (t : TTrace Addr) : List UInt8 := (unitsIn c t).flatten

/-- The octets sent on `c`. -/
def streamOut (c : Conn) (t : TTrace Addr) : List UInt8 := (unitsOut c t).flatten

/-- The connections opened on port `p`, in order. -/
def opened (p : Port) : TTrace Addr → List Conn
  | [] => []
  | .open_ p' c _ :: t => if p' = p then c :: opened p t else opened p t
  | _ :: t => opened p t

/-- The peer closed its direction of `c`. -/
def peerClosed (c : Conn) (t : TTrace Addr) : Prop := TEv.eof c ∈ t

/-- `c` was reset. -/
def wasReset (c : Conn) (t : TTrace Addr) : Prop := TEv.reset c ∈ t

/-! ## Partial observation maps -/

/-- **A partial observation map.** -/
abbrev PMap (α β : Type) : Type := α → Option β

namespace PMap

variable {α β γ : Type}

/-- What the reading sees of a set of sources. -/
def image (f : PMap α β) (M : Set α) : Set β := {b | ∃ a ∈ M, f a = some b}

/-- A property of readings, read on sources (true where the reading is undefined). -/
def pull (f : PMap α β) (φ : β → Prop) : α → Prop := fun a => ∀ b, f a = some b → φ b

/-- The model stays in the reading's domain. -/
def Total (f : PMap α β) (M : Set α) : Prop := ∀ a ∈ M, (f a).isSome

/-- Composition of partial maps. -/
def comp (g : PMap β γ) (f : PMap α β) : PMap α γ := fun a => (f a).bind g

end PMap

/-! ## Stream readings -/

/-- **The result of reading a stream**: complete messages, leftover octets, and whether the
reading stopped at an error (rather than at the end of complete messages). -/
structure Parse (Msg : Type) where
  msgs : List Msg
  rest : List UInt8
  err : Bool
  deriving Repr

/-- A parse that consumed everything without error. -/
def Parse.Clean {Msg : Type} (p : Parse Msg) : Prop := p.rest = [] ∧ p.err = false

/-! ## Protocol selection -/

/-- **How a connection's application protocol is selected** (an explicit assumption). -/
inductive Select where
  /-- HTTP/1.1, no negotiation. -/
  | http1
  /-- HTTP/2 by prior knowledge over cleartext: the client starts with the preface (RFC 9113
  §3.3). -/
  | h2PriorKnowledge
  /-- Cleartext, by the first octets: the HTTP/2 preface selects HTTP/2, anything else
  HTTP/1.1. -/
  | sniffPreface
  /-- Under TLS, by the ALPN protocol id negotiated in the handshake (RFC 7301), assumed given
  by the TLS layer. -/
  | alpn (ids : List (List UInt8))
  deriving DecidableEq, Repr

end Silmaril.Servers.Transport
