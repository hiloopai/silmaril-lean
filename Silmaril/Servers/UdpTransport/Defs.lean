module

public import Silmaril.Servers.Transport.Defs
public import Silmaril.Net.Udp.Network.Defs

/-!
# UDP sockets read as transport traces

The bridge between the UDP socket semantics of `Silmaril.Net.Udp.Network` (observations
`Obs`, below `Servers`) and the protocol-neutral transport vocabulary of
`Silmaril.Servers.Transport` (`TEv`, `TTrace`, `TModel`). Peer addresses are endpoints,
`Addr := Net.Ip.Endpoint`.

`read a t` is what the server whose socket is bound at `a` does in the observation trace `t`:

* it starts with `bind p`, `p` the port of `a` (`Net.Ip.Port` read with `.toNat`, as
  `Transport.Port` is `Nat`);
* one **flow per peer**, numbered in order of first appearance: the first datagram to or from a
  new peer `b` is preceded by `open_ p c b`;
* `recv a m` becomes `recv c m.data` on the flow of `m.src`, and `send m` from `a` becomes
  `send c m.data` on the flow of `m.dst`: **one transport event per datagram**, so datagram
  boundaries are kept by `unitsIn`/`unitsOut`. `streamIn`/`streamOut` forget them and are not
  a reading of UDP;
* errors are kept, as `err c (code e)` (`TEv.err`): a refused send `sendErr m e` on the flow of
  `m.dst`; an asynchronous error `err a e` (an ICMP port unreachable, which names no peer in
  `Obs`) on the flow of the most recent send, as a connected socket reports it. An asynchronous
  error before any send names no flow and is the one observation the reading drops;
* observations at other sockets are not this server's and are ignored.

**The code table** (`code`), the reading's own, uses the Linux errno numbers: `tooBig` is 90
(`EMSGSIZE`), `noBufs` is 105 (`ENOBUFS`), `refused` is 111 (`ECONNREFUSED`).

The reading is total (`reading`, a `PMap` that is always defined), so `Transport.Thms`'s
`may_reflect_of_total` applies to it. `model C a` is the transport model of the socket at `a`
under the host configuration `C`. `UdpTransport.Thms` proves that boundaries are kept
(`unitsIn_flow`), that the reading depends only on the socket's own observations (`read_own`,
port isolation), and that refinement of host configurations carries over (`model_mono`).

Not claimed: anything about QUIC or HTTP/3 over these flows; that would be a further `PMap`
with `Transport.Select` (ALPN `h3`) and is conditional on `Net.Udp.QuicCarrier`'s hypotheses.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.UdpTransport

open Silmaril.Net.Ip Silmaril.Net.Udp Silmaril.Net.Udp.Network Silmaril.Servers.Transport

/-- The reading's error codes (Linux errno numbers). -/
def code : Err → Nat
  | .tooBig => 90
  | .noBufs => 105
  | .refused => 111

/-- What an observation is on one flow: a datagram in, a datagram out, an error. -/
inductive Item where
  | recv (bs : List UInt8)
  | send (bs : List UInt8)
  | err (code : Nat)
  deriving DecidableEq, Repr

/-- The transport event of an item on flow `c`. -/
def Item.ev (c : Conn) : Item → TEv Endpoint
  | .recv bs => .recv c bs
  | .send bs => .send c bs
  | .err e => .err c e

/-- The peer and item of an observation at the socket bound at `a`, given the peer of the most
recent send. -/
def classify (a : Endpoint) (last : Option Endpoint) : Obs → Option (Endpoint × Item)
  | .recv b m => if b = a then some (m.src, .recv m.data) else none
  | .send m => if m.src = a then some (m.dst, .send m.data) else none
  | .sendErr m e => if m.src = a then some (m.dst, .err (code e)) else none
  | .err b e => if b = a then last.map fun p => (p, .err (code e)) else none

/-- The peer of the most recent send, after an observation. -/
def nextLast (a : Endpoint) (last : Option Endpoint) : Obs → Option Endpoint
  | .send m => if m.src = a then some m.dst else last
  | _ => last

/-- The transport events of the socket at `a`, with the peers seen so far (flow `i` is the
peer at position `i`) and the peer of the most recent send. -/
def readFrom (a : Endpoint) : List Endpoint → Option Endpoint → List Obs → TTrace Endpoint
  | _, _, [] => []
  | peers, last, o :: t =>
    match classify a last o with
    | none => readFrom a peers (nextLast a last o) t
    | some (b, it) =>
      if b ∈ peers then it.ev (peers.idxOf b) :: readFrom a peers (nextLast a last o) t
      else .open_ a.port.toNat peers.length b :: it.ev peers.length ::
        readFrom a (peers ++ [b]) (nextLast a last o) t

/-- The peers in order of first appearance, after a trace. -/
def peersFrom (a : Endpoint) : List Endpoint → Option Endpoint → List Obs → List Endpoint
  | peers, _, [] => peers
  | peers, last, o :: t =>
    match classify a last o with
    | none => peersFrom a peers (nextLast a last o) t
    | some (b, _) =>
      if b ∈ peers then peersFrom a peers (nextLast a last o) t
      else peersFrom a (peers ++ [b]) (nextLast a last o) t

/-- **The transport trace of the socket bound at `a`.** -/
def read (a : Endpoint) (t : List Obs) : TTrace Endpoint := .bind a.port.toNat :: readFrom a [] none t

/-- The flow of peer `b` in the reading of `t`. -/
def flowOf (a : Endpoint) (t : List Obs) (b : Endpoint) : Conn := (peersFrom a [] none t).idxOf b

/-- The reading, as a (total) partial observation map. -/
def reading (a : Endpoint) : PMap (List Obs) (TTrace Endpoint) := fun t => some (read a t)

/-- **The transport model of the socket at `a`** under the host configuration `C`. -/
def model (C : Config) (a : Endpoint) : TModel Endpoint := (reading a).image (traces C)

/-- The data of the datagrams the socket at `a` received from `b`, in order. -/
def recvFrom (a b : Endpoint) (t : List Obs) : List (List UInt8) :=
  ((recvAt a t).filter fun m => m.src = b).map Msg.data

/-- Whether an observation is at the socket bound at `a`. -/
def Obs.atSock (a : Endpoint) : Obs → Bool
  | .recv b _ => b = a
  | .send m => m.src = a
  | .sendErr m _ => m.src = a
  | .err b _ => b = a

end Silmaril.Servers.UdpTransport
