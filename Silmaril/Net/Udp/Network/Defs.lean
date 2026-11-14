module

public import Silmaril.Net.Udp.Service.Defs
public import Mathlib.Data.Set.Defs

/-!
# UDP: sockets over a packet network, with the network's choices explicit

`Silmaril.Net.Udp.Service` states the UDP service as a trace predicate (`Service`, the loose
channel). This module gives the *operational* reading underneath it and separates two levels
that are easy to conflate:

* **The socket API** (`Obs`): what an application sees at its sockets. `send m` (a `sendto`
  the host accepted), `sendErr m e` (a `sendto` the host refused), `recv a m` (a `recvfrom` on
  the socket bound at `a` returning `m`, with its source and destination) and `err a e` (an
  asynchronous error reported on the socket at `a`). These are the observations.
* **The packet network stack** (`Act`, `Step`): the host's port table and the datagrams in the
  network (`State.flight`, a multiset as a list). Besides the observations, the network takes
  internal steps, each one an explicit *choice* of the environment: `lose m` (a copy in flight
  is dropped), `dup m` (a copy in flight is duplicated) and `wire p` (an IP packet arrives that no
  local sender emitted). Reordering is the choice of which datagram in flight `recv` takes.
  Nothing forces delivery: the network may lose everything (a safety specification, as RFC 768
  says "delivery and duplicate protection are not guaranteed").

The host configuration (`Config`) fixes which local endpoints have a bound socket (`bound`) and
whether off-path packets can arrive (`offPath`). With `offPath = false` the only packets that
arrive from the wire are ones that do not decode as UDP (`Msg.ofPacket p = none`: another
protocol, a truncated header, a bad checksum, RFC 768 "Checksum"), and they are discarded
without effect. With `offPath = true` any packet may arrive, so a datagram may be received that
nobody sent: UDP has no authentication, a source address is just a field, and a corrupted
datagram whose 16-bit checksum still passes is indistinguishable from an injected one.

The host's rules (`Step`):

* `send m` only for a well-formed message (`Msg.WF`: one address family, length below 2^16)
  from a bound socket; a message that is not well formed is refused with `tooBig` (EMSGSIZE);
  the host may refuse any send with `noBufs` (ENOBUFS, a host choice, RFC 1122 §4.1.3.3 lets
  UDP report such errors and loses nothing by not sending).
* `recv a m` takes a copy of `m` out of the network, at the socket bound at `m`'s destination
  (`a = m.dst`): **port isolation** is this rule, the demultiplexing of RFC 768 "User Interface".
* `err a .refused` may be reported on any bound socket at any time: ICMP port-unreachable
  messages (RFC 1122 §4.1.3.3) are themselves unauthenticated (RFC 5927), so the model does not
  tie them to a cause.

`Network.Thms` characterizes the observable traces exactly (`traces_iff`,
`traces_offPath_iff`), proves port isolation as noninterference (`isolation`), and connects to
`Udp.Service` (`traces_service`).

**Not modelled.** Binding and closing as events (the port table is fixed), multicast and
broadcast, IP fragmentation and PMTU, socket buffers and their sizes, connected UDP sockets
(`connect` filters by peer: a client-side refinement of `recv`), ECN, the IPv6 flow label and
scope identifiers (endpoints are an IP address and a port), timing.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Net.Udp

open Silmaril.Net.Ip Silmaril.Net.Channel

/-- The source endpoint of a message. -/
def Msg.src (m : Msg) : Endpoint := ⟨m.srcIp, m.srcPort⟩

/-- The destination endpoint of a message. -/
def Msg.dst (m : Msg) : Endpoint := ⟨m.dstIp, m.dstPort⟩

/-- The message from `s` to `d` with data `data`. -/
def Msg.mk' (s d : Endpoint) (data : List UInt8) : Msg := ⟨s.ip, d.ip, s.port, d.port, data⟩

instance (m : Msg) : Decidable m.WF := inferInstanceAs (Decidable (_ ∧ _))

namespace Network

/-- Errors reported at the socket API. -/
inductive Err where
  /-- EMSGSIZE: the message cannot be carried in one datagram. -/
  | tooBig
  /-- ENOBUFS: the host had no room (a host choice). -/
  | noBufs
  /-- ECONNREFUSED: an ICMP port unreachable was reported (unauthenticated). -/
  | refused
  deriving DecidableEq, Repr

/-- **Socket API observations.** -/
inductive Obs where
  /-- A `sendto` at `m.src` that the host accepted. -/
  | send (m : Msg)
  /-- A `sendto` at `m.src` that the host refused with `e`; nothing entered the network. -/
  | sendErr (m : Msg) (e : Err)
  /-- A `recvfrom` on the socket bound at `a` returned `m` (its data, source and destination). -/
  | recv (a : Endpoint) (m : Msg)
  /-- An asynchronous error reported on the socket bound at `a`. -/
  | err (a : Endpoint) (e : Err)
  deriving DecidableEq, Repr

/-- **The host configuration**: the bound sockets, and whether off-path packets arrive. -/
structure Config where
  bound : Endpoint → Bool
  offPath : Bool

/-- **Network actions**: an observation, or an internal choice of the network. -/
inductive Act where
  | obs (o : Obs)
  /-- The network drops one copy of `m`. -/
  | lose (m : Msg)
  /-- The network duplicates one copy of `m`. -/
  | dup (m : Msg)
  /-- The IP packet `p` arrives from the wire, emitted by no local sender. -/
  | wire (p : Packet)
  deriving DecidableEq, Repr

/-- The state of the network: the datagrams in flight (a multiset). -/
structure State where
  flight : List Msg := []
  deriving DecidableEq, Repr

/-- **The host and network rules.** -/
inductive Step (C : Config) : State → Act → State → Prop where
  | send {s : State} (m : Msg) : m.WF → C.bound m.src = true →
      Step C s (.obs (.send m)) ⟨s.flight ++ [m]⟩
  | tooBig {s : State} (m : Msg) : ¬ m.WF → Step C s (.obs (.sendErr m .tooBig)) s
  | noBufs {s : State} (m : Msg) : Step C s (.obs (.sendErr m .noBufs)) s
  | recv {s : State} (m : Msg) : m ∈ s.flight → C.bound m.dst = true →
      Step C s (.obs (.recv m.dst m)) ⟨s.flight.erase m⟩
  | refused {s : State} (a : Endpoint) : C.bound a = true → Step C s (.obs (.err a .refused)) s
  | lose {s : State} (m : Msg) : m ∈ s.flight → Step C s (.lose m) ⟨s.flight.erase m⟩
  | dup {s : State} (m : Msg) : m ∈ s.flight → Step C s (.dup m) ⟨s.flight ++ [m]⟩
  | wire {s : State} (p : Packet) : (C.offPath = true ∨ Msg.ofPacket p = none) →
      Step C s (.wire p) ⟨s.flight ++ (Msg.ofPacket p).toList⟩

/-- Runs. -/
inductive Steps (C : Config) : State → List Act → State → Prop where
  | refl (s : State) : Steps C s [] s
  | cons {s s' s'' : State} {a : Act} {as : List Act} :
      Step C s a s' → Steps C s' as s'' → Steps C s (a :: as) s''

/-- The observation of an action, if it is one. -/
def Act.obs? : Act → Option Obs
  | .obs o => some o
  | _ => none

/-- The observations of a run. -/
def obsOf (as : List Act) : List Obs := as.filterMap Act.obs?

/-- **The observable traces** of a host and its network, from an empty network. -/
def traces (C : Config) : Set (List Obs) :=
  {t | ∃ as s', Steps C {} as s' ∧ obsOf as = t}

/-! ## The trace specification -/

/-- The per-event host rules: sends are well formed and from bound sockets, `tooBig` only for
messages that are not, receives are of well-formed messages at the bound socket of their
destination, asynchronous errors are `refused` on bound sockets. -/
def Local (C : Config) : Obs → Prop
  | .send m => m.WF ∧ C.bound m.src = true
  | .sendErr m e => e = .noBufs ∨ (e = .tooBig ∧ ¬ m.WF)
  | .recv a m => a = m.dst ∧ C.bound a = true ∧ m.WF
  | .err a e => e = .refused ∧ C.bound a = true

/-- The channel event of an observation: sends and receives of datagrams. -/
def Obs.chan : Obs → Option (Ev Msg)
  | .send m => some (.send m)
  | .recv _ m => some (.recv m)
  | _ => none

/-- The channel trace of an observation trace. -/
def toChan (t : List Obs) : List (Ev Msg) := t.filterMap Obs.chan

/-- **The specification without off-path packets**: the host rules, and the loose channel. -/
def Spec (C : Config) (t : List Obs) : Prop := (∀ o ∈ t, Local C o) ∧ Loose (toChan t)

/-- The messages received on the socket bound at `a`. -/
def recvAt (a : Endpoint) : List Obs → List Msg
  | [] => []
  | .recv b m :: t => if b = a then m :: recvAt a t else recvAt a t
  | _ :: t => recvAt a t

/-- Whether an observation is about the endpoint `a`: datagrams to other endpoints are not. -/
def Obs.about (a : Endpoint) : Obs → Bool
  | .send m => m.dst == a
  | .recv _ m => m.dst == a
  | _ => true

/-- The trace with the datagrams addressed to endpoints other than `a` removed. -/
def onlyTo (a : Endpoint) (t : List Obs) : List Obs := t.filter (Obs.about a)

end Network

end Silmaril.Net.Udp
