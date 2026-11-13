# HTTP/1.1 compliance: a requirement-by-requirement checklist

This page audits `Silmaril.Net.Http1` against RFC 9112 (HTTP/1.1) and against the parts of
RFC 9110 (HTTP semantics) that an HTTP/1.1 recipient applies to each message. It extends track C of
[http.md](http.md). Each requirement has one status:

- **Proved**: a theorem in a `Thms` header, using only the standard axioms.
- **Checked**: `#guard` checks on concrete octets in `Silmaril.Net.Http1.ComplianceExamples`
  or `Silmaril.Net.Http1.Examples`. The executable definitions are evaluated; no theorem
  covers them.
- **Defined**: an executable definition exists, without a theorem or check of the stated property.
- **Abstract**: modelled as a parameter or assumption, so another development has to
  discharge it (named in the row).
- **Gap**: the model does not meet the requirement, or meets it only partly; the row says how.
- **Planned**: nothing exists yet.

The HTTP/1.1 formalization is **not complete**. Every row below that is not Proved or
Checked is open work. The modules are listed in the last section.

## Message syntax and parsing (RFC 9112 §2–§5)

| § | Requirement | Status | Where |
| --- | --- | --- | --- |
| 2.1 | `HTTP-message = start-line CRLF *( field-line CRLF ) CRLF [ message-body ]` | Proved | `parseRequestHead_encode`, `parseRequestHead_sound` (`Message.Thms`) |
| 2.2 | Parse as octets, not as a character encoding | Proved | all parsers are on `UInt8` |
| 2.2 | Bare `LF` as a line terminator MAY be accepted | Checked (choice: rejected) | `ComplianceExamples` |
| 2.2 | A server SHOULD ignore at least one empty line before the request line | Gap | the caller has to strip leading `CRLF`s; `serve` rejects them with `400` |
| 2.2 | Whitespace between the start line and the first field: reject, or consume those lines | Checked (choice: rejected) | `ComplianceExamples` |
| 2.2 | A `CR` not followed by `LF` in a protocol element is invalid | Proved | the head grammar (`Grammar.fieldLine`, `Grammar.requestLine`) |
| 2.3 | `HTTP-version` grammar, case-sensitive `HTTP` | Proved | `Grammar.version`, round trips |
| 2.3 | A request with a major version other than 1 is answered `505` | Proved, Checked | `checkRequest_ok` (`Accepted.major`), `RequestError.status_mem` |
| 2.3 | An intermediary sends its own version when forwarding | Planned | no intermediary model yet |
| 3 | `request-line = method SP request-target SP HTTP-version` | Proved | `Grammar.requestLine`, round trips |
| 3 | An invalid request line is answered `400` | Checked | `serve` stops with `rejected 400` |
| 3 | Request-line length: a recipient SHOULD support at least 8000 octets; `414`/`501` above a limit | Gap | no length limit: every length is accepted, and resource limits are not modelled |
| 3.1 | `method = token`, case-sensitive | Proved | grammar; `Http.Method.ofToken` |
| 3.2 | No whitespace inside `request-target` | Proved | grammar (`VCHAR` only) |
| 3.2 | `400` for an HTTP/1.1 request without `Host`, with several `Host` lines or with an invalid `Host` value | Proved, Checked | `checkRequest_host11`, `Accepted.host` |
| 3.2.1 | `origin-form = absolute-path [ "?" query ]` | Proved (classification), Checked | `targetForm`, `Accepted.form` |
| 3.2.2 | `absolute-form`; a recipient uses the target's authority, not `Host` | Defined, Checked | `absoluteParts`, `targetUri`. Gap: only hierarchical `scheme://authority…` targets |
| 3.2.3 | `authority-form` only for CONNECT | Proved | `checkRequest_connect` |
| 3.2.4 | `asterisk-form` only for OPTIONS | Proved | `Accepted.fits` with `formFits` |
| 3.2 | Hosts as `IP-literal` (RFC 3986 §3.2.2) | Gap | `reg-name`/IPv4 text only (`Http.Uri.isHttpAuthority`) |
| 3.3 | Reconstructing the target URI from the scheme, `Host` and the target | Defined, Checked | `targetUri` |
| 4 | `status-line = HTTP-version SP status-code SP [ reason-phrase ]` | Proved | `Grammar.statusLine`, round trips |
| 4 | A client SHOULD ignore the reason phrase | Proved | no definition reads `reason` |
| 5 | `field-line = field-name ":" OWS field-value OWS` | Proved | `Grammar.fieldLine_G_iff` |
| 5.1 | Whitespace between field name and colon: a server MUST reject with `400` | Checked | `ComplianceExamples` |
| 5.2 | `obs-fold` in a request: reject or replace with `SP` | Checked (choice: rejected) | `ComplianceExamples` |
| 5.2 | A user agent MUST replace `obs-fold` in a response with `SP` | Gap | the response parser rejects `obs-fold` instead of replacing it |
| RFC 9110 §5.5 | Field values with `CR`, `LF` or `NUL` are invalid | Proved | parser soundness (`FieldLine.Valid`) |
| RFC 9110 §5.1–§5.5 | The HTTP/1.1 and RFC 9110 field validity checks are the same | Proved | `FieldLine.toLine_isValid` (`Request.Thms`) |

## Message body and framing (RFC 9112 §6–§7)

| § | Requirement | Status | Where |
| --- | --- | --- | --- |
| 6.1 | A recipient MUST be able to parse `chunked` | Proved | `parseChunked_encode`, `parseChunked_sound` |
| 6.1 | `chunked` is applied at most once and is final in a request | Proved | `checkCodings_ok_final`, `checkRequest_ok` (`Accepted.codings`) |
| 6.1 | A transfer coding the server does not understand: `501` | Proved (status), Checked | `RequestError.unknownCoding`, `ComplianceExamples` |
| 6.1 | HTTP/1.0 message with `Transfer-Encoding`: faulty framing, close after processing | Proved | `rfcRequestFraming`, `framingForcesClose_http10` |
| 6.1 | A server MUST NOT send `Transfer-Encoding` in `1xx`/`204` responses, or to an HTTP/1.0 request | Planned | no validator for generated responses yet |
| 6.2 | `Content-Length` grammar; identical repeated values MAY be one value | Proved | `contentLength?`, `Profile` (`dupCl = strict`) |
| 6.2 | A sender MUST NOT send `Content-Length` together with `Transfer-Encoding` | Planned | sender-side checks are not modelled |
| 6.3 | Rules 1–2: no body for `HEAD`, `1xx`, `204`, `304`; `2xx` to CONNECT is a tunnel | Proved | `responseBodyLength_HEAD`, `responseBodyLength_noContent` |
| 6.3 | Rule 3: `Transfer-Encoding` overrides `Content-Length`; MAY reject; MUST close the connection afterwards | Proved | `bodyLengthOfFields_chunked`, `Profile.reject`/`teWins`, `checkRequest_clte`, `serve_clte_closes` |
| 6.3 | Rule 4: request whose final coding is not `chunked`: `400`; response: read until close | Proved | `Framing.Thms`, `frame_compliant` |
| 6.3 | Rule 5: invalid `Content-Length` is an unrecoverable error | Proved | `frame_compliant`, `compliant_iff_safe` |
| 6.3 | Rules 6–8: valid `Content-Length`; request without either has no body; response until close | Proved | `requestBodyLength_framed`, `Framing.Thms` |
| 6.3 | A server MAY reject a request with content but no `Content-Length` (`411`) | Planned | not modelled as an option |
| 6.3, 8 | Fewer octets than `Content-Length` before the input ends: incomplete message | Defined | `parseBody` fails with `eof`; client cache handling is planned |
| 7.1 | `chunked-body` grammar; chunk size of any magnitude | Proved | `Chunked.Thms` |
| 7.1.1 | Chunk extensions: grammar; unknown extensions ignored | Proved | `isChunkExt_iff_abnf` |
| 7.1.2 | Trailer fields: not merged when their definition forbids it (RFC 9110 §6.5.1) | Proved | `fieldValues_mergeTrailers`, `requestBodyLength_mergeTrailers` |
| 7.1.3 | Decoding `chunked` gives the concatenated chunk data | Proved | `parseChunked_rechunk` |
| 7.2 | `compress`, `deflate`, `gzip`; `x-compress`/`x-gzip` equivalent | Proved for `gzip`, `deflate`; Gap for `compress` | `Decoders` parameter, `decodeTransfer_encodeTransfer`; instantiated by `Silmaril.Net.Http1.CodingLib` (`lib_roundTrip`). No LZW decoder |
| 7.3 | Transfer coding registry | Defined | `registeredCodings` |
| 7.4, 10.1 | `TE`: `trailers`, codings with weights; `chunked` always acceptable | Defined, Checked | `teOffers`, `teTrailers`, `teAccepts` |
| 7.4 | The sender of `TE` also sends the `TE` connection option | Defined | `declaresHopByHop` (no theorem) |

## Connection management (RFC 9112 §9)

| § | Requirement | Status | Where |
| --- | --- | --- | --- |
| 9.1 | Connections are reliable, ordered byte streams | Abstract | the input is one `ByteArray`; linking to `Silmaril.Net.Tcp` is planned |
| 9.2 | Responses are associated with requests in order | Proved | `readResponses_encode` |
| 9.3 | Persistence: `close` → close; HTTP/1.1 → persist; HTTP/1.0 with `keep-alive` (not at a proxy) → persist | Proved | `persists_close`, `persists_http11`, `persists_http10` |
| 9.3 | A close-delimited response ends the connection | Proved | `keepOpen_closeDelimited` |
| 9.3.1 | A user agent MUST NOT automatically retry a non-idempotent request | Defined, Proved (instances) | `mayAutoRetry`, `mayAutoRetry_POST` |
| 9.3.2 | Pipelining: a server answers pipelined requests in order | Proved | `serve_pipeline` |
| 9.3.2 | A client MUST be able to read responses to pipelined requests in order | Proved | `readResponses_encode` |
| 9.4 | Concurrency limits | Planned | informational |
| 9.5 | Timeouts and failures | Abstract | no time model |
| 9.6 | `close`: the server closes after the response, and processes no further requests | Proved | `keepOpen_close`, `serve_closes` |
| 9.6 | A client that sent `close` sends no further requests | Planned | no client connection model |
| 9.6 | Lingering close and TCP reset | Abstract | transport behaviour |
| 9.7, 9.8 | TLS initiation and closure | Abstract | owned by the TLS track |
| RFC 9110 §7.6.1 | Remove the `Connection` field, the fields it names, and `Proxy-Connection`, `Keep-Alive`, `TE`, `Transfer-Encoding`, `Upgrade` before forwarding | Proved | `stripHopByHop_mem`, `stripHopByHop_transferCodings`, `stripHopByHop_connectionOptions` |
| RFC 9110 §7.8 | `101` switches protocols; HTTP/1.1 stops on that connection | Defined | `switches`; `keepOpen` is false after `101`. The new protocol (WebSockets) belongs to its track |
| RFC 9110 §15.2 | A client reads one or more `1xx` responses before the final one | Proved | `readResponse_encode` |

## Security (RFC 9112 §11)

| § | Requirement | Status | Where |
| --- | --- | --- | --- |
| 11.1 | Response splitting: no `CR`/`LF` in field values | Proved | head soundness; HTTP/2 translation in `Http2.Fields.Thms` |
| 11.2 | Request smuggling: two compliant recipients never disagree on message boundaries | Proved | `parseRequestWith_compliant_agree`, `compliant_no_desync` |
| 11.2 | The common noncompliant framings desynchronise with a compliant one | Proved | `desync_clte`, `desync_tete`, `compliant_iff_safe` |
| 11.2 | A request behind a closing request is never processed | Proved | `serve_closes` |
| 11.3, 11.4 | Message integrity and confidentiality | Abstract | TLS track |

## Noncompliance and extension surfaces

`Silmaril.Net.Http1.Profile` gives each recipient's framing choices as a value. The compliant
values are the latitude RFC 9112 allows. The others are what deployed implementations do.

| Knob | Compliant | Noncompliant (attack) | Witness |
| --- | --- | --- | --- |
| `clTe` | `reject`, `teWins` | `clWins` (CL.TE) | `desync_clte` |
| `dupCl` | `strict` | `first`, `last` | `violationWitnesses` |
| `teMatch` | `final` | `substring` (`xchunked`), `caseSensitive` (`Chunked`) (TE.TE) | `desync_tete` |
| `http10Te` | `false` | `true` | `violationWitnesses` |
| `ignoreTe` | `false` | `true` | `desync_tete` |

`compliant_iff_safe` shows the table is exact for this profile type: a profile accepts only
the reference framing (or rejects) **iff** it is compliant. Of the 108 profiles, 2 are
compliant.

The rest of the extension surface is explicit: transfer codings the server implements
(`ServerConfig.implements`, with decoders as a parameter), `TE`, chunk extensions (kept raw),
upgrade tokens, and extension methods and fields (any `token`). The HTTP/1.1 institution and
the OpenAPI service model build on these surfaces: see [http1-institution.md](http1-institution.md).

Line-level leniency (bare `LF`, `obs-fold`, whitespace before `:`, leading empty lines) is not
yet a profile knob: the head grammar is strict and rejects all of these (Checked). Modelling a
lenient head lexer, and proving that its disagreement with the strict one is exactly these
cases, is planned.

## Modules

| Module | Content |
| --- | --- |
| `Silmaril.Net.Http1.Fields` | the shared field API: case-insensitive lookup, `#rule` list elements, `fieldHasToken` (used by the WebSocket/CONNECT track, #157) |
| `Silmaril.Net.Http1.Codings` | transfer-coding check, `TE`, decoders as a parameter |
| `Silmaril.Net.Http1.Connection` | connection options, persistence, forced closure, hop-by-hop fields |
| `Silmaril.Net.Http1.Profile` | recipient profiles, reference framing, smuggling theorems and witnesses |
| `Silmaril.Net.Http1.Request` | target forms, `Host`, request checks, context, RFC 9110 request, trailers |
| `Silmaril.Net.Http1.Pipeline` | the pipelined server loop, interim and pipelined responses, retries |
| `Silmaril.Net.Http1.ComplianceExamples` | `#guard` checks on RFC examples and smuggling probes |

```sh
lake build --wfail Silmaril.Net.Http1.Pipeline.Thms Silmaril.Net.Http1.Profile.Thms \
  Silmaril.Net.Http1.Request.Thms Silmaril.Net.Http1.Connection.Thms \
  Silmaril.Net.Http1.Codings.Thms Silmaril.Net.Http1.ComplianceExamples.Defs \
  Silmaril.Net.Http1.Fields.Thms
```
