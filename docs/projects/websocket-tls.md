# WebSockets, upgrades, tunnels and TLS on the wire

This page covers the part of the HTTP formalization ([http.md](http.md)) that changes what a
connection carries. That includes direct TLS (`https`), HTTP Upgrade and its historical TLS
form, CONNECT tunnels, extended CONNECT, and the WebSocket protocol. It also covers the
registry map from TLS and HTTP identifiers to cryptographic algorithms. The cryptography itself
(audit and roadmap) is in [crypto.md](crypto.md).

The statuses mean the same as in [http.md](http.md):

- **Proved**: a theorem in a `Thms` header, using only the standard axioms.
- **Checked**: evaluated on published examples by `decide`, `rfl` or `#guard`.
- **Assumed**: an explicit hypothesis or a named `Assumption` value. It is never a Lean axiom.
- **Planned**: nothing exists yet.

No module here uses `sorry`, `native_decide` or `axiom`.

## Modules

| Module | Content |
| --- | --- |
| `Silmaril.Net.WebSocket.Frame` | RFC 6455 §5 framing: the codec, masking, opcodes, control-frame limits, masking direction, Close bodies |
| `Silmaril.Net.WebSocket.Message` | §5.4–§5.6 fragmentation, the receiver (reassembly, interleaved control frames, UTF-8, failure codes), fragmenting senders |
| `Silmaril.Net.WebSocket.Close` | the connection lifecycle and closing handshake (§4, §5.5.1, §7) as a finite machine (`Silmaril.Automata`) |
| `Silmaril.Net.WebSocket.Handshake` | the §4 opening handshake over `Silmaril.Net.Http1` heads: the server's reading, `Sec-WebSocket-Accept`, the response, the client's checks |
| `Silmaril.Net.WebSocket.Examples` | end to end: octets, then the HTTP/1.1 parser, then the handshake, the serializer, the client check, and frames |
| `Silmaril.Net.Tunnel.Upgrade` | RFC 9110 §7.8 Upgrade and 101/426, the upgrade-token registry, RFC 2817, and the HTTP/2 prohibition |
| `Silmaril.Net.Tunnel.Connect` | CONNECT (RFC 9110 §9.3.6), its HTTP/2 form (RFC 9113 §8.5), and extended CONNECT (RFC 8441, RFC 9220) |
| `Silmaril.Net.Tunnel.Transport` | connection setups (direct TLS, cleartext, h2c, RFC 2817, CONNECT tunnels) under an active network attacker |
| `Silmaril.Net.Tls.Record` | the RFC 8446 §5.1 record header, and telling TLS apart from cleartext HTTP by the first octet |
| `Silmaril.Net.Tls.Registry` | cipher suites, named groups, signature schemes and ALPN IDs mapped to `Silmaril.Crypto.Catalog` algorithms and assumptions, plus the RFC 9113 §9.2 rules |
| `Silmaril.Crypto.SHA1` | FIPS 180-4 SHA-1, which `Sec-WebSocket-Accept` needs |
| `Silmaril.Crypto.Catalog` | algorithms, parameters, separate evidence fields (recognized, implemented, vectors, functional, refinement) and named assumptions |

## RFC coverage checklist

### RFC 6455: The WebSocket Protocol

| Section | Requirement | Status |
| --- | --- | --- |
| §5.2 | Frame layout: FIN, RSV1–3, opcode, MASK, 7/16/64-bit length, key, payload | **Proved**: `decode_encode` (round trip), `decode_sound` (whatever is read is a valid frame and exactly its encoding), `encode_injective` |
| §5.2 | "The minimal number of bytes MUST be used to encode the length"; the 64-bit length has its MSB clear | **Proved**: the strict reader rejects both, so encodings are canonical (`decode_sound`). **Checked**: rejection examples |
| §5.2 | RSV bits must be 0 unless an extension is negotiated | **Proved** as receiver behaviour (`Receiver.step`). **Checked**: example |
| §5.2, §11.8 | Opcodes: 0x0/0x1/0x2/0x8/0x9/0xA; reserved opcodes fail the connection | Defined (`isDefinedOpcode`). **Checked** |
| §5.3 | Masking: `octet i XOR key[i mod 4]` | **Proved**: involution (`applyMask_applyMask`), length, offset modulo 4, and masking split pieces at shifted offsets (`applyMask_append`) |
| §5.1, §5.3 | Clients mask every frame and servers mask none; a violation fails the connection | **Proved** for senders that respect `KeysFor` (`run_fragments`). **Checked**: both violations |
| §5.3, §10.3 | The masking key is unpredictable | **Assumed** (randomness of the client; not modelled) |
| §5.4 | Fragmentation: one start frame, continuations, FIN on the last; no interleaving of messages | **Proved**: every fragmentation is delivered as the original message (`run_fragments`). **Checked**: interleaving and stray continuations are rejected |
| §5.4, §5.5 | Control frames may be injected between fragments | **Proved**: removing every acceptable ping or pong changes neither the data messages, nor the state, nor failures (`run_filter_keepalive`) |
| §5.5 | Control frames: payload ≤ 125 octets, not fragmented | **Proved**: such frames are ≤ 131 octets on the wire (`controlOk_length`). Defined as a receiver check |
| §5.5.1, §7.4 | Close body: empty, or a 2-octet code plus a UTF-8 reason; codes that may be sent (1000–1003, 1007–1014, 3000–4999) | **Proved**: the body codec is a bijection on valid bodies (`decodeClose_encodeClose`, `decodeClose_sound`). **Checked**: 1000 accepted, 1005 rejected |
| §5.5.1, §7.1 | Closing handshake: no data after sending Close; Close in response; clean close needs both Close frames | **Proved** by the verified decision procedures: `no_data_after_close_sent`, `clean_close_needs_both`, `conn_closed_final`, `conn_all_reachable` |
| §5.6, §8.1 | Text is UTF-8 (checked on the whole message, so a code point may span fragments); failure code 1007 | Defined (`complete`, `Failure.code`). **Checked**: a code point split across fragments is accepted; a lone continuation octet is rejected |
| §4.1 | The client's request (fields read with `Http1.fieldValues`/`fieldElements`): `GET`, HTTP/1.1, `Host`, `Upgrade: websocket`, `Connection: Upgrade`, a 16-octet base64 key, version 13 | **Proved**: `readOffer_clientRequest` (the server reads back what the client sent) and `readOffer_sound` |
| §4.2.2 | `Sec-WebSocket-Accept = base64(SHA-1(key ++ GUID))` and the 101 response | **Checked** by the kernel: the RFC example key and accept (`accept_rfc6455`), and the SHA-1 vector of §1.3 (`digest_rfc6455`) |
| §4.1 | The client validates the response: 101, tokens, accept, no unoffered extension, subprotocol among those offered | **Proved**: the server's response passes for every offer and selection (`checkResponse_respond`). Soundness: `checkResponse_sound` |
| §4.4 | Unsupported version → 426 with `Sec-WebSocket-Version: 13` | Defined (`versionRejection`). **Checked** |
| §1.2 | The full example exchange | **Checked** end to end (`#guard`): RFC octets, the RFC 9112 parser, `readOffer`, `respond`, the serializer (byte-identical to the RFC's response), the parser, `checkResponse`, and a masked frame |
| §4.2.1, §10.2 | `Origin` checks, cookies, authentication | Out of scope (application policy). Stated as an assumption in `Handshake.Defs` |
| §9, RFC 7692 | Extensions (permessage-deflate uses RSV1) | Planned. It would reuse `Silmaril.Formats.Compression.Deflate`, which the compression track owns |
| §6 | Sending and receiving data at the application API | Partly: `fragments` (send) and `Receiver.run` (receive) |
| §7.1.7, §10.4 | Failing the connection and resource limits | Partly: the per-frame limit `maxPayload`. A per-message limit is planned |

### RFC 8441 and RFC 9220: extended CONNECT

| Section | Requirement | Status |
| --- | --- | --- |
| 8441 §3, 9220 §3 | `SETTINGS_ENABLE_CONNECT_PROTOCOL` (0x08): values 0/1; no 1→0 | **Proved**: `applyEnableConnect_sticky`. Without the setting, nothing is a valid extended CONNECT (`extended_requires_setting`) |
| 8441 §4 | `:protocol`; `:scheme` and `:path` present; `:authority` | Defined (`validExtendedConnect`) over the HTTP/2 track's field checks |
| 8441 §3, 9113 §8.3 | An endpoint without RFC 8441 treats the request as malformed | **Proved**: `extended_not_classic` (it fails `Http2.validRequest`) |
| 8441 §5, 9220 §3 | WebSocket bootstrap: `:protocol = websocket`, no key/accept, 2xx response; RFC 6455 frames on the stream | Defined (`validWebSocketRequest`, `tunnelAccepted`). **Checked**: the RFC 8441 §5.1 example |
| 9220 | The same rules over HTTP/3 field sections | Defined as a function of decoded field lists, independent of the HTTP version. HTTP/3 framing and QPACK belong to the QUIC/H3 track |

### RFC 9110 §7.8, §9.3.6; RFC 2817; RFC 9113 §8.6: upgrades and tunnels

| Section | Requirement | Status |
| --- | --- | --- |
| 9110 §7.8 | Switch only to a protocol the client offered, and only with `Connection: upgrade` | **Proved**: `validSwitch_offered`, `afterAnswer_offered` |
| 9110 §15.5.22 | 426 carries `Upgrade` | Defined (`validUpgradeRequired`) |
| 9113 §8.2.2, §8.6 | HTTP/2 has no `Upgrade` and no 101 | **Proved**: `h2_rejects_upgrade` (through the HTTP/2 track's `validRegular`) |
| 9113 §3.1, 7540 §3.2 | `h2c` upgrade withdrawn | Recorded (`UpgradeToken.current`, `Setup.h2cUpgrade`) |
| 2817 §3.1–§3.3, §4.2 | `Upgrade: TLS/1.0`, optional and mandatory forms | **Proved**: the optional form has a downgrade trace with no TLS (`optional_upgrade_downgrade`), and the form that carries the upgrade on the real request exposes it. The §3.2 `OPTIONS`-first form protects requests (`endToEnd_protects`), but it is not an `https` setup (`tlsUpgrade_not_https`) |
| 9110 §4.2.2, §4.3.3 | `https` requests are sent only over TLS with the origin | **Proved** relative to the TLS assumption: `https_setups_protect`, `protects_iff_endToEnd` |
| 9110 §9.3.6, 9112 §3.2.3 | CONNECT: authority-form target; no `Content-Length`/`Transfer-Encoding` in a 2xx | Defined (`isAuthorityForm`, `connectResponseOk`). **Checked** |
| 9113 §8.5 | HTTP/2 CONNECT: `:method` and `:authority` only | HTTP/2 track (`Http2.validRequest`). **Checked**: it is not an extended CONNECT |
| 9110 §9.3.6 | Tunnelled bytes are end to end and the proxy only relays | **Assumed**: the proxy is in the attacker model. TLS inside the tunnel is the only protection the model credits |

### RFC 8446, RFC 7301, RFC 9113 §9.2: TLS as seen by HTTP

| Section | Requirement | Status |
| --- | --- | --- |
| 8446 §5.1 | Record header: content type, legacy version, length ≤ 2^14 | **Proved**: `decodeHeader_encodeHeader` |
| 8446 §5.1, 9112 §3, 9113 §3.4 | TLS records and cleartext HTTP/1.1 or h2 can be told apart by the first octet | **Proved**: `tls_not_token`, `token_not_tls`, `preface_not_tls` |
| 7301 §3.2 | ALPN: the server selects a protocol both sides offered; `h2c` never in TLS | **Proved**: `selectAlpn_sound` |
| 9113 §9.2, App. A | HTTP/2 over TLS: TLS ≥ 1.2, TLS 1.2 suites off the block list | **Proved**: `h2_tls13_ok`, `h2_rsa_blocked` |
| 8446 §B.4, §4.2.3, §4.2.7 | Suite, group and signature code points mapped to algorithms | **Proved**: the suite map is injective (`ofCode_code`); TLS 1.3 suites are AEAD + HKDF (`tls13_aead`); SHA-1 signatures are excluded in TLS 1.3 (`sha1_not_tls13`) |
| 8446 §4 | Handshake messages, extensions, key schedule, record protection | Planned ([crypto.md](crypto.md), milestones C4–C6) |
| 8446 App. E | Handshake and record security | **Assumed**: `CipherSuite.assumptions` lists the hypotheses of Dowling et al. (2021) as data. Nothing is proved about them |

## Security assumptions, stated once

1. **TLS provides an authenticated, confidential, ordered byte stream** with the peer named by the
   certificate (RFC 8446, RFC 9110 §4.3.4). This holds under the assumptions that
   `Silmaril.Net.Tls.CipherSuite.assumptions` lists: AEAD security, HKDF/HMAC PRF security,
   hash collision resistance, Diffie–Hellman hardness in the group, EUF-CMA signatures, and good
   randomness. These are `Silmaril.Crypto.Catalog.Assumption` values, not axioms. No theorem
   here proves or uses them.
2. **The network is an active attacker** (RFC 3552 §3). It may drop, reorder and rewrite
   cleartext, and it may strip optional upgrades. It cannot read or forge TLS-protected octets
   (assumption 1). Proxies are part of the network.
3. **Randomness**: WebSocket masking keys and `Sec-WebSocket-Key` nonces are unpredictable
   (RFC 6455 §5.3, §10.3). This is not modelled.
4. **SHA-1 in the WebSocket handshake has no security role.** The accept value is not
   authentication, and nothing assumes SHA-1 is collision resistant.

## Shared APIs this track uses or needs

This track only *reads* the other tracks' public definitions:

- From HTTP/1.1: `Http1.RequestHead`, `ResponseHead`, `FieldLine`, `parseRequestHead`,
  `parseResponseHead`, `encResponseHead`.
- From HTTP/2: `Http2.validRequest`, `validSection`, `pseudoValues`, `validRegular`,
  `connectionSpecific`, `breakColon`, `ErrorCode`, `clientPreface`.
- From network byte order: `Net.Wire.beBytes`/`beValue` and their laws (`beValue_beBytes`,
  `beBytes_beValue`, `beValue_lt`; #162).
- From HPACK: `Hpack.Entry`.
- From HTTP semantics: `Http.Field.isTchar`, `Http.Uri.isRegName`, `isPort`.
- From finite machines: `Automata` (`silmaril_finite`, `DMachine`, `Reach`).
- From encodings: `Base64` (`encodeChars`, `decodeChars`).
- From cryptography: `Crypto.Padding`, `Crypto.Word`.

Field lookup, the list syntax and token tests are the HTTP/1.1 track's shared API
`Silmaril.Net.Http1.Fields` (#156; this pull request is stacked on it): `fieldValues`,
`fieldElements`, `fieldHasToken`, `flatMap_listElements_tokens`, with `Http1.ascii` for names.
The handshake defines no lookup of its own. HTTP/2 and HTTP/3 lookup in `Tunnel.Connect` stays
separate: it matches exact lower-case names (RFC 9113 §8.2.1).

Remaining follow-ups with the other tracks:

| Need | Plan | Owner |
| --- | --- | --- |
| HTTP/3 field sections | Already `List Hpack.Entry` in #159, so `Tunnel.Connect` applies to RFC 9220 unchanged | done |
| `SETTINGS_ENABLE_CONNECT_PROTOCOL` | `Http3.settingEnableConnectProtocol` (#159) and `Tunnel.settingEnableConnectProtocol` are both 0x08. Whichever lands second defines its constant as the other's | QUIC/H3 track and this track |
| Two `validExtendedConnect`s | `Tunnel` (this PR) and `Http3.ExtendedConnect` (#159) differ: this one needs exactly one `:authority` and a non-empty `:path` for every scheme. After both merge, prove `Tunnel.validExtendedConnect → Http3.validExtendedConnect` or make one canonical | both tracks |
| permessage-deflate (RFC 7692) | Call `Formats.Compression.SyncFlush.inflateMessage` (#160) on messages with RSV1, once the extension is negotiated | compression track (#160), then this track |
| Taking over the connection after 101 | #156's `keepOpen`/`switches` hand the connection to `Tunnel.Upgrade`; `stripHopByHop` removes `Upgrade`/`Connection` before forwarding | HTTP/1.1 track |

## Architecture gaps found

- `Net` is not a region in `regions.toml`, although `Silmaril/Net/**` exists and other trees
  call it "region `Net`". These modules follow the header/proof layout. They import `Automata`, as
  `Net.Http2.Stream` already does. They are also the first `Net` modules to import `Crypto`
  (SHA-1 and the catalogue) and `Encoding` (base64). Declaring the region and its `deps` is a deliberate `regions.toml` change for its own
  commit. It is not part of this pull request.
- `Encoding` is not a region either, and `Silmaril/Proofs/Crypto` has no glob in
  `lakefile.toml`. The new SHA-1 module therefore keeps its short proofs inline in `Thms`.
- `List.splitOn` does not reduce in the kernel (it is not structural), so the field-list
  helpers use structural splits. `decide +kernel` then checks the handshake examples.
- The HTTP/2 track's `Settings.apply` ignores identifier 0x08. Extended CONNECT tracks the setting
  separately (`applyEnableConnect`). Folding it into `Http2.Settings` belongs to that track.

## Checking

```sh
lake build --wfail Silmaril.Net.WebSocket.Frame.Thms Silmaril.Net.WebSocket.Message.Thms \
  Silmaril.Net.WebSocket.Close.Thms Silmaril.Net.WebSocket.Handshake.Thms \
  Silmaril.Net.WebSocket.Examples.Defs Silmaril.Net.Tunnel.Upgrade.Thms \
  Silmaril.Net.Tunnel.Connect.Thms Silmaril.Net.Tunnel.Transport.Thms \
  Silmaril.Net.Tls.Record.Thms Silmaril.Net.Tls.Registry.Thms \
  Silmaril.Crypto.SHA1.Thms Silmaril.Crypto.Catalog.Thms
```

## Plan

1. **WebSocket completion.** Per-message size limits, permessage-deflate (RFC 7692) over the
   compression track's DEFLATE, and the lifecycle machine as a `silmaril/machines` document
   bound to `connMachine`.
2. **WebSocket over HTTP/2 streams.** Connect `validWebSocketRequest` to the HTTP/2 stream machine.
   DATA payloads on the stream carry `WebSocket.Frame` octets, and the stream's END_STREAM
   matches the closing handshake.
3. **TLS handshake syntax.** ClientHello/ServerHello with `supported_versions`, `key_share`,
   `signature_algorithms` and ALPN, as codecs with round-trip proofs. Then negotiation as a
   function, with `selectAlpn` and `Registry` as its parameters.
4. **The TLS 1.3 state machine** (RFC 8446 Appendix A) as a finite machine, with decided
   properties: no application data before Finished, and Finished checked before any
   application data.
5. **Cryptography**: the milestones C1–C6 of [crypto.md](crypto.md). The protocol modules above
   take the primitives as parameters, so they need no change when the primitives are
   implemented.
