# HTTP/3, QUIC, QPACK and WebTransport

This page covers track E of the [HTTP roadmap](http.md). It lists what is modelled and
what is proved. It also states which parts of QUIC are concrete and which are an explicit,
documented assumption. Status words follow [http.md](http.md):

- **Proved**: the theorem is stated in a `Thms` header and depends only on the standard axioms.
- **Checked**: examples are verified with `rfl` or `decide`, kernel-checked, never with `native_decide`.
- **Defined**: definitions exist without theorems.
- **Abstract**: the part is a parameter or structure that other modules assume. It is never an `axiom`.
- **Planned**: nothing exists yet.

Every module imports only Lean core and other `Silmaril.Net` headers. The exception is
`Http3.Machine`, which uses `Silmaril.Automata` and so CSLib and Mathlib. None of them uses
`sorry`, `axiom` or `native_decide`.

## Versions

| Specification | Version modelled | Status of the document (checked 2026-11-13) |
| --- | --- | --- |
| QUIC transport | RFC 9000 | Proposed Standard |
| QUIC datagrams | RFC 9221 | Proposed Standard |
| HTTP/3 | RFC 9114 | Proposed Standard |
| QPACK | RFC 9204 | Proposed Standard |
| HTTP Datagrams and the Capsule Protocol | RFC 9297 | Proposed Standard |
| Extended CONNECT | RFC 8441 (HTTP/2), RFC 9220 (HTTP/3) | Proposed Standard |
| WebTransport over HTTP/3 | **draft-ietf-webtrans-http3-17** | Internet-Draft in WG Last Call; **not an RFC** |
| WebTransport over HTTP/2 | draft-ietf-webtrans-http2-16 | Internet-Draft; only two prohibited capsule codepoints are used |
| WebTransport overview | draft-ietf-webtrans-overview-14 | Internet-Draft; not modelled |

The WebTransport codepoints (`SETTINGS_WT_ENABLED = 0x20b8933b`, stream type `0x54`,
signal `0x41`, the capsules `0x2843`, `0x78ae` and `0x190B4D3D`–`0x190B4D44`, the error codes
and the application error range `0x52e4a40fa8db`–`0x52e5ac983162`) are those of draft -17.
They may change before RFC publication. Earlier drafts' codepoints, for example
`SETTINGS_WEBTRANSPORT_MAX_SESSIONS`, are deliberately not modelled.

## What is QUIC here, and what is assumed

| Layer | Status |
| --- | --- |
| Variable-length integers (§16) | Proved: round trips at every allowed length, bounds, self-delimiting (`Quic.VarInt`) |
| Stream identifiers, stream limits (§2.1, §4.6) | Proved (`Quic.StreamId`) |
| Frame codecs for all RFC 9000 frame types, plus DATAGRAM (§12.4, §19, RFC 9221 §4) | Proved: round trip of each frame and of whole packet payloads. Unknown types are FRAME_ENCODING_ERROR (`Quic.Frame`) |
| Transport error codes (§20.1) | Proved (`Quic.Error`) |
| Sending and receiving stream states, final size (§3.1, §3.2, §3.5, §4.5) | Proved: terminal states, an immutable final size, the three FINAL_SIZE_ERROR cases (`Quic.Stream`) |
| Credit-based flow control (§4.1) | Proved: a sender that respects its credit never causes FLOW_CONTROL_ERROR, even when MAX frames arrive late or reordered (`Quic.Flow`) |
| Stream reassembly (§2.2) | Proved: delivered bytes are a prefix of what was written, whatever the arrival order or duplication. Covered ranges deliver exactly the written bytes (`Quic.Reassembly`) |
| The stream service HTTP/3 uses (§2.4, RFC 9221 §5) | **Abstract**: `Quic.Service.StreamService` is a structure, not an axiom. It covers ordered reliable bytes per stream, FIN, RESET_STREAM and STOP_SENDING with application codes, stream limits and unreliable datagrams. A **proved reference instance** builds it from reassembly over arbitrarily retransmitted segments and a lossy, reordering datagram network |
| Packets, packet number spaces, ACK processing, packetization (§12.2–§13) | Not modelled |
| TLS handshake and packet protection (RFC 9001) | Not modelled; assumed confidential, authenticated and integrity-protected |
| Loss recovery, congestion control (RFC 9002), PMTU (§14) | Not modelled |
| Connection IDs, migration, stateless reset, 0-RTT, Retry, version negotiation, connection close and idle timeout (§5, §8–§10) | Not modelled |
| Liveness | Not modelled: the service is safety-only |

HTTP/3 itself reads typed frames from in-order stream bytes. It never sees QUIC packets.
This model therefore does **not** claim full QUIC support. It models the stream layer
concretely and assumes the rest.

Known gaps in the QUIC layer:

- It is not proved that everything the frame decoder accepts is `Valid`. Only the round
  trips and the specific rejections are proved.
- The stream machines and flow control are not yet joined to the reference service.
- `Frame.allowedIn` (RFC 9000 Table 3) is only checked on examples.

## HTTP/3 (RFC 9114)

| Part | Sections | Status |
| --- | --- | --- |
| Frame layout, bounded reader | §7.1, §10.5 | Proved: raw and typed frame round trips. The reader buffers at most the caller's limit (`Http3.Frame`) |
| DATA, HEADERS, CANCEL_PUSH, SETTINGS, PUSH_PROMISE, GOAWAY, MAX_PUSH_ID | §7.2.1–§7.2.7 | Proved: payload round trips. Checked: H3_FRAME_ERROR for payloads with extra bytes or truncated payloads |
| Reserved HTTP/2 frame types, grease types, unknown types | §7.2.8, §9 | Proved: grease code points are exactly `0x1f·N + 0x21`. Reserved HTTP/2 types are kept for the stream layer to reject |
| SETTINGS parameters, reserved HTTP/2 settings, duplicates, interpretation | §7.2.4, §7.2.4.1 | Proved: payload round trip, grease settings are ignored. Checked: H3_SETTINGS_ERROR cases |
| Error codes, unknown codes treated as H3_NO_ERROR | §8, §8.1 | Defined; checked |
| Stream identifiers, request streams, server-initiated bidirectional streams | §6.1 | Defined; checked |
| Unidirectional stream types, critical-stream uniqueness, push stream rules | §6.2, §6.2.1–§6.2.3 | Proved: at most one control stream per peer; unknown stream types are never connection errors. Checked: duplicate control, QPACK encoder and QPACK decoder streams, pushes from clients, reused push IDs |
| Control stream invariants | §6.2.1, §5.2, §7.2 | Proved: SETTINGS first and only once; no DATA, HEADERS, PUSH_PROMISE or reserved frames; GOAWAY ids do not increase; GOAWAY from a server names a request stream; MAX_PUSH_ID does not decrease; unknown frames are irrelevant; closing the stream is H3_CLOSED_CRITICAL_STREAM (`Http3.Stream`) |
| Request and push stream frame grammar, interim responses, H3_REQUEST_INCOMPLETE | §4.1 | Proved: every message is accepted in any DATA chunking. Every request stream a server accepts is exactly the frames of one message. Unknown frames are ignored. The path from bytes to message is proved |
| The above as finite machines | §4.1, §6.2.1 | Proved: the finite machines match the readers. Decided: no DATA before HEADERS, nothing after the trailers, no PUSH_PROMISE on requests or pushes, the control stream needs SETTINGS (`Http3.Machine`) |
| Field rules, pseudo-header fields, mapping to `Http.Request`/`Response` | §4.2, §4.3 | Proved: canonical requests and responses round trip through field lists. The HTTP/2 validity rules are reused, not restated. Checked: uppercase names, `transfer-encoding`, pseudo-header fields in trailers, `content-length` mismatch (`Http3.Message`) |
| Field section size limit | §4.2.2 | Defined (`withinLimit`, HPACK's `tableSize`); checked |
| Extended CONNECT, `:protocol` | RFC 9220 | Proved (`Http3.ExtendedConnect`) |
| CONNECT method | §4.4 | Reused from the HTTP/2 rules; tunnel semantics planned |
| Server push semantics, push-ID limits on PUSH_PROMISE and CANCEL_PUSH | §4.6, §7.2.3, §7.2.5 | Planned. PUSH_PROMISE is only accepted where §4.1 allows it |
| GOAWAY shutdown semantics (which requests may be retried) | §5.2 | Planned. Only the id ordering is proved |
| Request cancellation, H3_REQUEST_REJECTED | §4.1.1 | Planned |
| 0-RTT settings compatibility | §7.2.4.2 | Partly covered (the H3_DATAGRAM check in `Http3.Datagram`); otherwise planned |
| Joining QPACK decoding to HEADERS on a live connection | §4.2.1 | `requestOfParts` takes the field-section decoder as a parameter. Instantiating it with QPACK's decoder state is planned |

## QPACK (RFC 9204)

| Part | Sections | Status |
| --- | --- | --- |
| Static table (99 entries) | §3.1, App. A | Checked: length and spot checks |
| Dynamic table: size, capacity, eviction, absolute, relative and post-base indexing | §3.2 | Proved: size ≤ capacity ≤ maximum capacity, stable absolute indices, index conversions (`Qpack.Table`) |
| N-bit-prefix string literals | §4.1.2 | Proved: round trip. With an 8-bit prefix it is HPACK's string literal |
| Huffman-coded strings | §4.1.2, RFC 7541 App. B | Planned: rejected, as in HPACK |
| Encoder and decoder instructions | §4.3, §4.4 | Proved: codec round trips; applying encoder instructions keeps the table valid (`Qpack.Instruction`) |
| Required Insert Count, Base | §4.5.1 | Proved: round trips under the RFC's window conditions; checked: the RFC examples |
| Field line representations, section decoding | §4.5.2–§4.5.6 | Proved: codec round trips. A section blocks exactly when its Required Insert Count exceeds the insert count. A Required Insert Count of 0 never blocks. References at or above the Required Insert Count, or to evicted entries, are QPACK_DECOMPRESSION_FAILED (`Qpack.Section`) |
| Blocked streams, Known Received Count, eviction guard, acknowledgments | §2.1.1–§2.1.4, §2.2 | Proved: blocked streams stay within SETTINGS_QPACK_BLOCKED_STREAMS. The Known Received Count only grows and stays ≤ the insert count. Entries that are unacknowledged or still referenced are never evicted. Bad increments are QPACK_DECODER_STREAM_ERROR (`Qpack.State`) |
| RFC examples | App. B.1–B.5 | Checked, on both the encoder and the decoder side |
| Flow-control deadlocks, split instructions, the sample encoder | §2.1.3, App. C | Not modelled |

## Capsules, datagrams and WebTransport

| Part | Source | Status |
| --- | --- | --- |
| Capsule codec and streams, unknown capsules skipped, DATAGRAM capsule | RFC 9297 §3 | Proved (`Http3.Capsule`) |
| HTTP/3 datagrams, Quarter Stream ID, SETTINGS_H3_DATAGRAM | RFC 9297 §2 | Proved (`Http3.Datagram`) |
| Session establishment, SETTINGS_WT_ENABLED and the other requirements, one-session rule | draft -17 §3, §5.1, §5.2 | Proved (`WebTransport.Establish`) |
| Stream headers (uni `0x54`, bidi signal `0x41`), session ids, buffering | draft -17 §4.1–§4.3, §4.6 | Proved (`WebTransport.Stream`) |
| Application error code ↔ HTTP/3 error code mapping | draft -17 §4.4 | Proved: a bijection onto the registered range that avoids grease code points (`WebTransport.ErrorCode`) |
| WT_CLOSE_SESSION, WT_DRAIN_SESSION, WT_MAX_*, WT_*_BLOCKED capsules | draft -17 §5, §6 | Proved: codec round trips and validity (`WebTransport.Capsule`) |
| Session flow control | draft -17 §5.3–§5.6 | Proved, in a lockstep model where capsules are delivered at once: limits only increase and a compliant sender stays within them. Capsules in flight are planned (`WebTransport.Flow`) |
| Session life cycle | draft -17 §6 | Proved: closed is terminal, no new streams after close, FIN means close(0, "") (`WebTransport.Session`) |
| Priorities, WT-Available-Protocols / WT-Protocol, exporters, version negotiation, intermediaries, WebTransport over HTTP/2, the W3C API | | Not modelled |

## Interfaces between tracks

- **QUIC → HTTP/3.** HTTP/3 consumes in-order stream bytes through `Http3.decodeFrames`.
  `Quic.Service.StreamService` is the contract for those bytes; `Quic.Service.reference`
  shows that a reassembling implementation satisfies it.
- **HPACK → QPACK.** QPACK reuses `Hpack.Entry`, `Entry.size`, `fitPrefix`, the prefix
  integers and the string literal.
- **HTTP/2 → HTTP/3 fields.** `Http3.Message` reuses `Http2.validRequest`,
  `validResponse`, `validRegular` and `contentLengthMatches`. A change to those rules
  changes both versions.
- **HTTP semantics.** Both directions use `Silmaril.Net.Http.Request` and `Response`.
  Content codings (`Net/Http/ContentCoding`, [content-coding.md](content-coding.md)) are
  version-independent and apply to `Message.content` after the HTTP/3 stream layer.
  HTTP/3 has no transfer codings (§4.1).
- **TLS, WebSockets and the crypto registry** belong to other tracks. Here TLS is an
  assumption of the QUIC service. WebSockets over HTTP/3 (RFC 9220) would use
  `Http3.ExtendedConnect` with `:protocol = websocket`.

## Plan to full formalization

1. Join QPACK's decoder state to the request-stream reader, so that `requestOfParts` is
   instantiated: blocked streams across the connection, SETTINGS_QPACK_* from `Settings`.
2. Add push-ID bookkeeping (MAX_PUSH_ID versus PUSH_PROMISE and CANCEL_PUSH) and the GOAWAY
   retry semantics of §5.2. Then build one connection model combining the control stream,
   request streams and QPACK streams, and prove that a conforming peer never triggers a
   connection error.
3. Join `Quic.Stream` and `Quic.Flow` to the reference `StreamService`. Prove that
   accepted frames are `Valid`, and prove the RFC 9000 Table 3 rules.
4. Add Huffman decoding for HPACK and QPACK (RFC 7541 Appendix B) with a round-trip proof.
5. Model packets: packet number spaces, ACK ranges and frames allowed per packet type.
   Prove that the packet layer refines the stream service. RFC 9001 and RFC 9002 stay
   assumptions unless the crypto track supplies a TLS model.
6. Follow WebTransport to RFC. Re-pin the codepoints when the draft is published, and add
   the session-flow model with capsules in flight.
7. Differential tests against public HTTP/3 and QPACK corpora (for example the
   qifs QPACK interop files) as `decide` checks.

## Checking

```sh
lake build --wfail +Silmaril.Net.Quic.Service.Thms +Silmaril.Net.Quic.Frame.Thms \
  +Silmaril.Net.Quic.Stream.Thms +Silmaril.Net.Quic.Flow.Thms +Silmaril.Net.Quic.StreamId.Thms \
  +Silmaril.Net.Quic.Error.Thms +Silmaril.Net.Http3.Message.Thms +Silmaril.Net.Http3.Stream.Thms \
  +Silmaril.Net.Http3.Capsule.Thms +Silmaril.Net.Http3.Datagram.Thms \
  +Silmaril.Net.Http3.ExtendedConnect.Thms +Silmaril.Net.Qpack.State.Thms \
  +Silmaril.Net.Qpack.Static.Thms +Silmaril.Net.WebTransport.Session.Thms \
  +Silmaril.Net.WebTransport.Establish.Thms +Silmaril.Net.WebTransport.Flow.Thms
lake build --wfail +Silmaril.Net.Http3.Machine.Thms   # needs the Automata closure (CSLib, Mathlib)
```
