# UDP: sockets, the UDP institution and QUIC datagrams over UDP

Modules: `Silmaril.Net.Udp.{Header,Service}` (RFC 768 format and the loose-channel service,
already on main), and in this project `Silmaril.Net.Udp.Network`, `Silmaril.Net.Udp.Institution`,
`Silmaril.Net.Udp.QuicCarrier` and `Silmaril.Net.Udp.Examples`.

## Two levels, kept apart

* **Socket API** (`Network.Obs`): what an application sees, `send`, `sendErr`, `recv a m` (with
  source, destination and the datagram boundary) and asynchronous `err`.
* **Packet network** (`Network.Step`): datagrams in flight, plus explicit environment choices,
  `lose`, `dup` and `wire p` (a packet from the wire). Reordering is which datagram `recv`
  takes. With `Config.offPath = false`, only packets that do not decode as UDP arrive from the
  wire, and they are discarded. With `offPath = true`, anyone can inject a datagram.

`Network.Thms.traces_iff` characterizes the observable traces exactly (inclusion both ways):
the host rules plus the loose channel of `Net.Channel`. `traces_offPath_iff` gives the
characterization with off-path packets, where only the host rules remain. Port isolation is
proved as noninterference (`isolation`, `recvAt_onlyTo`).

## The institution

`Udp.Inst`: signatures name endpoints and payload kinds; sentences are `sendsWF`, `addressed`
(port isolation), `authentic`, `noDup`, `fifo` and `onlyKind`, with negation and conjunction;
models are trace sets over socket observations; reducts reinterpret the symbols. The
satisfaction condition is `sat_map_iff`, and `inst : Sig ⥤ Room` is the institution. The network
model satisfies `sendsWF` and `addressed` everywhere, and `authentic` exactly without off-path
packets. It is proved to **violate** `noDup`, `fifo` and `onlyKind` at every bound endpoint.
Reliability is a sentence that fails, not an assumption.

## QUIC and HTTP/3 over UDP: what is and is not proved

| claim | status |
| --- | --- |
| QUIC DATAGRAM frames over UDP are a run of `Quic.Service`, so no datagram is received more often than sent | proved, *at most*, conditional on the integrity of the run (`QuicCarrier.carrier_sound`, `Hon`) |
| integrity from functional correctness when no off-path packets arrive | proved (`hon_of_replay`) |
| integrity is needed: no protection lets one injected datagram break the service | proved (`none_forgery`) |
| HTTP/3 datagrams (RFC 9297) decoded by the server are a sub-multiset of those sent | proved, conditional on `Hon` (`h3_received_subperm`) |
| *at least* for the carrier (every service run arises from some network behaviour) | not proved |
| QUIC streams over UDP refine `StreamService` (ACK, retransmission, RFC 9002) | **missing**; HTTP/3 keeps `StreamService` as a parameter |
| packets proper, header protection, connection IDs, the TLS handshake, 0-RTT | not modelled |
| DTLS (RFC 9147) | not modelled; it would be another `Protection`, not QUIC's |

Packet protection is a parameter (`QuicCarrier.Protection`), and both cryptographic properties
are named hypotheses: `Correct` (functional) and `Hon` (per-run integrity, the idealized reading
of INT-CTXT). No axiom is added, and no computational claim is made.

## Evidence

`Udp.Examples` keeps three kinds of evidence apart: kernel proofs about concrete traces and
runs; `#guard` computations of the carrier over a network that duplicates, reorders and
injects garbage; and no evidence from real sockets.

## Checking

```sh
lake build --wfail Silmaril.Net.Udp.Network.Thms Silmaril.Net.Udp.Institution.Thms \
  Silmaril.Net.Udp.QuicCarrier.Thms Silmaril.Net.Udp.Examples.Defs
```
