# HTTP: scope, status and roadmap

This page scopes a formalization of HTTP against its standards. It records what is
defined, what is proved, what is only checked on examples, and what remains. "Full HTTP"
covers a family of RFCs. The work is split into tracks so that each pull request can be
reviewed separately. Statuses:

- **Proved** means that a theorem is stated in a `Thms` header and depends only on the standard axioms.
- **Checked** means that the behaviour is evaluated on examples from the RFC by `decide`, `rfl` or `#guard`.
- **Defined** means that definitions exist without theorems.
- **Planned** means that nothing exists yet.

No part of this tree uses `sorry`, `native_decide` or extra axioms.

## Standards in scope

| Standard | Topic | Track |
| --- | --- | --- |
| RFC 9110 | HTTP semantics (messages, fields, methods, status codes, URIs, conditional and range requests, content negotiation, authentication) | A |
| RFC 3986 | URI generic syntax (as used by RFC 9110 §4) | A |
| RFC 9111 | HTTP caching | B |
| RFC 9112 | HTTP/1.1 message syntax, framing and connection management | C |
| RFC 9113 | HTTP/2 framing, streams, flow control, HTTP mapping | D |
| RFC 7541 | HPACK field compression for HTTP/2 | D |
| RFC 9218 | Extensible prioritization (replaces the RFC 7540 priority tree) | D |
| RFC 8441, RFC 9220 | Extended CONNECT (WebSockets over HTTP/2 and HTTP/3) | D, E |
| RFC 9114 | HTTP/3 | E |
| RFC 9204 | QPACK field compression for HTTP/3 | E |
| RFC 9000 | QUIC transport (variable-length integers and the stream abstraction HTTP/3 relies on) | E |

The following are **out of scope**. They are assumptions or interfaces, not formalized
protocols:

- TLS (RFC 8446) and ALPN (RFC 7301). The `https` scheme is assumed to provide a
  confidential, authenticated, reliable and ordered byte stream. Cryptographic content
  belongs to the `Crypto` region.
- The QUIC loss recovery, congestion control and cryptographic handshake (RFC 9001, RFC 9002).
  HTTP/3 is to be modelled over an abstract QUIC stream service.
- Specific content codings (gzip, brotli) and media types. Content coding may later reuse
  `Silmaril.Formats.Compression`.
- Browser behaviour: cookies (RFC 6265), CORS and fetch.

## Modelling assumptions

- Octets are `List UInt8` and numbers are unbounded `Nat`, with validity predicates
  stating field widths (for example, `FrameHeader.Valid`). The definitions are executable
  specifications. Performance is not a goal.
- Transports are reliable, ordered byte streams. The TCP development in `Silmaril.Net.Tcp` is the
  intended model for HTTP/1.1 and HTTP/2. Linking HTTP to it is planned.
- Where an RFC gives a recipient latitude ("MAY", "SHOULD"), the module documents the
  choice it makes. Stricter choices are made for parsers. Examples are CRLF only in
  HTTP/1.1, rejecting `obs-fold` and ignoring frames on closed HTTP/2 streams.
- The new HTTP/2 and HPACK modules depend only on Lean core. They do not import Mathlib.

## Status by track

### A. Semantics (RFC 9110, RFC 3986): `Silmaril.Net.Http`

| Part | Sections | Status |
| --- | --- | --- |
| ABNF core rules, tokens, field values, field sections, combination | 9110 §5.1–§5.3, §5.5, §5.6.2 | Proved: grammar/check equivalences (`Field.Thms`) |
| Messages, control data, validity, HEAD stripping | 9110 §6 | Proved (`Message.Thms`) |
| Methods and their properties (safe, idempotent, cacheable) | 9110 §9 | Proved (`Method.Thms`) |
| Status codes, classes, `allowsContent` | 9110 §15 | Proved (`Status.Thms`) |
| URI pieces: scheme, authority, path, query | 9110 §4, 3986 §3 | Proved: grammar/check equivalences (`Uri.Thms`) |
| Origin servers as relations: safety, idempotence, HEAD vs GET, a resource store | 9110 §3, §9.2, §9.3 | Proved (`Exchange.Thms`) |
| List grammar `#rule`, quoted strings, comments, parameters, dates | 9110 §5.6 | Planned |
| Representation metadata, content negotiation | 9110 §8, §12 | Planned |
| Conditional requests (`If-Match`, `If-None-Match`, …; evaluation order) | 9110 §13 | Planned |
| Range requests | 9110 §14 | Planned |
| Authentication framework | 9110 §11 | Planned |
| Intermediaries, `Via`, `Connection`, `Max-Forwards`, redirects | 9110 §3.7, §7.6, §15.4 | Planned |

### B. Caching (RFC 9111)

Planned. The work covers storing, freshness, validation and invalidation. The target is a
refinement theorem: a cache in front of an origin is observationally equivalent to the origin,
modulo the staleness the response directives allow.

### C. HTTP/1.1 (RFC 9112): `Silmaril.Net.Http1`

| Part | Sections | Status |
| --- | --- | --- |
| Request and status lines, field lines, heads: parser and serializer | 9112 §2–§5 | Proved: round trip, soundness, unambiguity (`Message.Thms`) |
| Message body length rules, whole messages on a persistent connection | 9112 §6 | Proved: round trip, soundness, rules (`Framing.Thms`) |
| Chunked transfer coding, chunk extensions, trailers | 9112 §7.1 | Proved: round trip, soundness, rechunking (`Chunked.Thms`) |
| Connection management, persistence, pipelining, `Connection`, hop-by-hop fields | 9112 §9, 9110 §7.6.1 | Proved: persistence rules, forced closure, pipelined server reads requests in order and nothing after a closing request, pipelined responses with `1xx` read back (`Connection.Thms`, `Pipeline.Thms`) |
| HTTP/1.0 compatibility | 9112 §6.1, App. C.2.2 | Proved: `Transfer-Encoding` in HTTP/1.0 is faulty, `keep-alive` (`Profile.Thms`, `Connection.Thms`); `obs-fold` is rejected, not replaced (a gap for user agents) |
| Other transfer codings, `TE` | 9112 §7.2–§7.4, §10.1 | Proved: coding checks; round trip under the abstract decoder assumption (`Codings.Thms`); `TE` defined and checked |
| Request context: target forms, `Host`, version, `400`/`501`/`505`, RFC 9110 request | 9112 §2.3, §3, 9110 §7.2 | Proved (`Request.Thms`) |
| Smuggling freedom: two conforming recipients agree on message boundaries | 9112 §11.2 | Proved for the framing profiles: compliant recipients never desynchronise, the common noncompliant ones do (`Profile.Thms`) |

The requirement-by-requirement audit, with every gap, is [http1-compliance.md](http1-compliance.md).
The institution of HTTP/1.1 implementations (vanilla, extension-compliant, noncompliant) and
the OpenAPI 3.1.0 service model are in [http1-institution.md](http1-institution.md).

### D. HTTP/2 (RFC 9113, RFC 7541): `Silmaril.Net.Http2`, `Silmaril.Net.Hpack` (this pull request)

| Part | Sections | Status |
| --- | --- | --- |
| HPACK prefix integers, raw string literals | 7541 §5.1, §5.2 | Proved: round trips for every value, flag bits preserved (`Hpack.Integer.Thms`); checked: Appendix C.1 |
| HPACK static and dynamic tables, entry size, eviction, size updates | 7541 §2.3, §4, App. A | Proved: the size invariant is preserved, eviction is the longest fitting prefix, index shifting (`Hpack.Table.Thms`) |
| HPACK representations and field block decoding | 7541 §3, §6 | Proved: representation and block round trips, the table invariant under any input, non-indexing literals leave the table alone (`Hpack.Block.Thms`); checked: Appendix C.2 and C.3 (raw strings) |
| HPACK Huffman code | 7541 §5.2, App. B | Planned (Huffman-coded literals are currently rejected) |
| Frame header, frame size limit, frame type and error registries, client preface | 9113 §3.4, §4, §6, §7 | Proved: header and frame round trips, read frames respect `SETTINGS_MAX_FRAME_SIZE` (`Http2.Frame.Thms`) |
| SETTINGS parameters, payload, validation | 9113 §6.5 | Proved: accepted settings stay within the §6.5.2 constraints (`Http2.Settings.Thms`) |
| Flow-control windows, WINDOW_UPDATE, initial window changes | 9113 §5.2, §6.9 | Proved: conservation, window bounds, a sender never exceeds its credit (`Http2.Settings.Thms`) |
| Stream state machine, stream identifiers | 9113 §5.1, §5.1.1 | Proved: sender/receiver duality, monotone progress, closed is terminal, RST_STREAM, DATA only in the allowed states (`Http2.Stream.Thms`); as a finite machine ([automata.md](automata.md)): every state reachable, closed final, no close without END_STREAM/RST_STREAM (decided); its document `silmaril/machines/http2-stream.toml` is bound to the typed machine |
| Field validity, connection-specific fields, pseudo-header fields, CONNECT, `content-length` | 9113 §8.1–§8.3, §8.5 | Proved: valid regular fields translate to HTTP/1.1 lines without CR/LF/NUL, colon-unambiguous, no framing fields (`Http2.Fields.Thms`); checked: examples |
| Octets → frame → HPACK → validated request | 9113 §4, §6.2, §8.3 | Checked (`Http2.Examples`) |
| Per-frame payload layouts (padding, priority, PUSH_PROMISE, GOAWAY, PING, RST_STREAM) | 9113 §6.1–§6.10 | Planned |
| HEADERS/CONTINUATION sequencing (field blocks are contiguous) | 9113 §4.3, §6.10 | Planned |
| Connection state machine: preface, SETTINGS ack and timeout, GOAWAY, PING, concurrency limits | 9113 §3.4, §5.1.2, §6.5.3, §6.8 | Planned |
| Mapping HTTP/2 messages to `Silmaril.Net.Http.Request`/`Response` | 9113 §8 | Planned |
| Server push semantics | 9113 §8.4 | Planned |
| Prioritization | RFC 9218 | Planned |
| Extended CONNECT | RFC 8441 | Planned |

### E. HTTP/3 (RFC 9114, RFC 9204, RFC 9000)

Planned. The work covers QUIC variable-length integers (RFC 9000 §16), HTTP/3 frames and
stream types (RFC 9114 §6, §7), the QPACK static table, encoder/decoder streams and blocked
streams (RFC 9204), and the mapping to the version-independent messages. QUIC is to be
modelled as an abstract multiplexed stream service, as a parameter and not as an axiom.

### F. Cross-version and security properties

| Property | Status |
| --- | --- |
| HTTP/2 → HTTP/1.1 field translation cannot inject lines or framing fields (RFC 9113 §8.2.1, §10.3) | Proved (field level, `Http2.Fields.Thms`) |
| HPACK decoder memory is bounded by the advertised table size (RFC 7541 §7.3) | Proved (`Hpack.Block.Thms`: `decodeBlock_valid`) |
| Frame buffering is bounded by `SETTINGS_MAX_FRAME_SIZE` (RFC 9113 §4.2) | Proved (`readFrame_sound`) |
| Flow control: data sent ≤ initial window + credit (RFC 9113 §5.2) | Proved (`runFlow_dataSent_le`) |
| Never-indexed literals do not enter the dynamic table (RFC 7541 §7.1.3) | Proved (`processRep_literal_noindex`) |
| Smuggling freedom across HTTP/1.1 recipients (CL/TE desync) | Proved at the framing level (`compliant_no_desync`, `desync_clte`, `desync_tete`) |
| End-to-end: HTTP/2 → HTTP/1.1 translation preserves message boundaries and semantics | Planned |
| Resource exhaustion: integer octet bounds, CONTINUATION floods, rapid reset (RST_STREAM rate) | Partly defined (`decodeIntBounded`); planned |
| Each version's messages refine the RFC 9110 semantics; translations commute | Planned |

## Plan to full formalization

The milestones are ordered by dependency. Each one is one or more reviewable pull requests.

1. **HTTP/2 wire completeness.** Add the HPACK Huffman code with a round-trip proof
   against Appendix B and all frame payload layouts with their round trips. Add
   HEADERS/CONTINUATION reassembly and the connection-level state machine (preface,
   SETTINGS, PING, GOAWAY, concurrency).
2. **HTTP/2 semantics.** Map validated header sections and DATA to `Http.Request`/`Response`,
   and prove the mapping inverse to a serializer. Combine the stream machine with flow
   control into one connection model, and prove that a conforming peer never triggers a
   connection error.
3. **Semantics completion (RFC 9110).** Cover the `#rule` list grammar, parameters, dates,
   conditional and range requests, content negotiation, authentication and intermediaries.
4. **HTTP/1.1 completion.** Connection management, pipelining, the HTTP/1.0 rules and
   framing-level smuggling freedom are done ([http1-compliance.md](http1-compliance.md)).
   Remaining: the gaps listed there (lenient head lexing as a profile, `obs-fold` replacement
   for user agents, sender-side checks of generated responses, `IP-literal` hosts, limits).
5. **Cross-version translation.** Define the HTTP/2 ↔ HTTP/1.1 gateway and prove that it
   preserves the RFC 9110 message, using the field-level lemmas of this pull request and the
   HTTP/1.1 parser round trips.
6. **HTTP/3 and QPACK** over an abstract QUIC stream interface, reusing the HPACK table
   development (QPACK shares its entry size and eviction rules).
7. **Caching (RFC 9111)** as a refinement of origin semantics.
8. **Validation against implementations.** Run differential tests of the executable parsers
   against public test suites (for example h2spec) and the RFC examples, kept as `#guard`
   checks.

## Checking

```sh
lake build Silmaril   # the whole library, CI runs it with --wfail
```

The HTTP/2 and HPACK modules import only Lean core, so they can be checked alone without
a Mathlib build:

```sh
lake build --wfail +Silmaril.Net.Http2.Examples.Defs +Silmaril.Net.Http2.Stream.Thms \
  +Silmaril.Net.Http2.Settings.Thms +Silmaril.Net.Hpack.Integer.Thms
```
