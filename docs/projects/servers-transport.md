# Servers over transports: a shared socket-level vocabulary

`Silmaril.Servers.Transport` is a narrow, protocol-neutral interface. It describes what a
server does at its sockets, so that HTTP over TCP and protocols over UDP/QUIC can share one
notion of ports, connections, traces and refinement. It sits between the server core
(`Silmaril.Servers.Core`: request/response traces) and the wire models of `Silmaril.Net`.

## Scope

It models the **socket API** an application sees:

* for TCP, the reliable in-order byte stream of RFC 9293 §2.2, as specified by
  `Net.Tcp.Service`;
* for UDP, datagrams.

It is **not** a packet-level model. Nothing here refines `Net.Tcp.Transfer` (segments,
retransmission), `Net.Udp` (headers, checksums), QUIC loss recovery or a TLS record layer, and
no theorem relates the two levels. A result stated over `TTrace` assumes the socket layer
behaves as its API says.

## The interface

| name | meaning |
| --- | --- |
| `Kind` | `stream` or `datagram`: how a flow's payload is read |
| `Port`, `Conn` | port numbers; connections (stream) or flows (datagram), by first appearance |
| `TEv Addr` | `bind`, `open_`, `recv`, `send`, `eof`, `close`, `reset`, `fail` (peer addresses abstract) |
| `TTrace`, `TModel`, `TModel.Refines` | traces, trace sets, refinement as inclusion (implementation first) |
| `streamIn`, `streamOut` | the octets of a connection (chunking forgotten) |
| `unitsIn`, `unitsOut` | the datagrams (or chunks) of a flow, boundaries kept |
| `opened p` | the connections or flows opened on port `p` |
| `PMap`, `image`, `pull`, `Total` | partial observation maps (readings that may be undefined) |
| `Parse` | a stream reading's messages, leftover octets and error flag |
| `Select` | the protocol-selection assumption (HTTP/1.1, HTTP/2 prior knowledge, preface sniffing, ALPN) |

**Readings.** A reading from transport traces to server traces is a `PMap`. Three facts are
proved:

* the satisfaction law for universal sentences (`PMap.sat_pull_iff`);
* the image is monotone, so transport refinement gives refinement of the reading
  (`PMap.image_mono`);
* readings compose (`PMap.image_comp`).

**A reading is not a comorphism.** Existential properties are not reflected where the reading
is undefined (`PMap.not_may_reflect`). They are reflected for models that stay in its domain
(`PMap.may_reflect_of_total`).

Proposed use by other transports:

* a UDP or QUIC reading produces the same `TTrace` (datagram kind) and a `PMap` into
  `Servers.Core` traces;
* refinement and must/may statements reuse `TModel.Refines`, `Servers.Observe` and
  `Servers.Hosts`;
* any packet-level relation is stated separately, as an explicit hypothesis.
