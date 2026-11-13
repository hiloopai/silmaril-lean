# Cryptography: audit, catalogue and roadmap

This page records the cryptography in the repository as of this change, what protocol
registries ask for, and a plan towards formalizing the common algorithms. It distinguishes
three kinds of results that should never be conflated:

1. **Functional correctness**: an executable specification agrees with published vectors or
   with another artefact, such as machine code. This is what the library can prove today.
2. **Protocol properties that hold for any primitive**: framing, negotiation and state
   machines, stated over primitives as parameters
   ([websocket-tls.md](websocket-tls.md)).
3. **Computational security**: indistinguishability and unforgeability under reductions. The
   library has no framework for these, and **no module claims one**. Assumptions are named as
   `Silmaril.Crypto.Catalog.Assumption` data, never as axioms.

## Audit of existing cryptography

| Artefact | Where | Guarantee | Notes |
| --- | --- | --- | --- |
| SHA-256 reference | `Silmaril/Crypto/SHA256.lean` (`SHA256.digest`), `Crypto/SHA256/Defs.lean` (`Crypto.sha256`) | 7 FIPS 180-4/CAVP vectors (`decide +kernel`, including two-block messages); `hash_block_length`; `digest_length` | Uses Mathlib (through `Word`, `Padding`) |
| SHA-256 BitVec kernel | `Crypto/SHA256/Kernel.lean`, `Equiv.lean`, `Schedule.lean`, `Rounds.lean` | `processBlock_eq_compressBlock`: the list form and the `BitVec 32` form agree on every state and block | |
| SHA-256 x86-64 | `Crypto/X86/Sha256O2*.lean` | Proved refinement: the clang `-O2` compression function (459 octets) meets a System V contract whose postcondition is `processBlock` (`sha256_compress_O2`, `Post.compressed_reference`) | The only implementation-level crypto proof. Padding and driver I/O are not covered (`docs/Sha256CompressionProcess.md`) |
| SHA-256 programs | `Apps/Sha256sum`, `Process/CLI/Sha256`, `Process/LPS/Problems/*Sha256*`, `Cli/Spec/Sha256sum` | I/O behaviour specifications and process totality | Use `SHA256.digest` as the reference |
| MD padding | `Crypto/Padding.lean` | `paddingMD_block_multiple`, `paddingMD_prefix`, `paddingMD_injective` (for lengths < 2^61 octets), `paddingMD_not_prefix_free`; SHA-512 padding | Shared by SHA-1 (new) and SHA-256 |
| Words | `Crypto/Word.lean` | Rotation inverses, byte round trips (32/64-bit, BE/LE), XOR algebra | |
| MD5 | `Raw/Semantics/CPort/Crypto/MD5.lean` | 7 RFC 1321 vectors | Raw, so not an API. The interface is `Semantics/CPort/Crypto/MD5/Defs.lean` |
| CRC32C, CRC-32, Adler-32, IP checksum | `Crypto/CRC32C.lean`, `Formats/Compression/Checksum`, `Net/Ip/Checksum` | Check values; x86 refinements of zlib's checksums (`X86/Ladder/ZlibChecksums`) | **Not cryptographic**. Listed in the catalogue so that they are never mistaken for MACs |
| **SHA-1 (new)** | `Crypto/SHA1/{Defs,Thms}.lean` | 3 FIPS vectors and the RFC 6455 §1.3 vector (`decide +kernel`); `hash_block_length` | Needed for `Sec-WebSocket-Accept`. Explicitly not a security function |
| **Catalogue (new)** | `Crypto/Catalog/{Defs,Thms}.lean` | Levels tied to executable functions (`implemented_iff`, `proved_iff`); vectors re-checked through the catalogue (`vectors_ok`) | |

There is no HMAC, HKDF, AES, ChaCha20, Poly1305, GCM, X25519/X448, NIST curves, ECDSA, EdDSA,
RSA, ML-KEM, ML-DSA, SHA-384/512 or SHA-3 implementation. `Crypto/SHA256.lean`'s docstring names
`Silmaril.Crypto.HMAC`, `TestVectors.ECDSA` and a `SHA1.lean`, but none of these exist on main:
the docstring is stale and should be corrected by the owner of that file. No crypto file uses
`sorry`, `native_decide` or `axiom`.

## Registry identifiers mapped to algorithms and levels

`Silmaril.Net.Tls.Registry` maps code points to `Silmaril.Crypto.Catalog` algorithms.
`Algorithm.level` computes the level from the catalogue's data (*advertised*, then
*recognized*, *implemented*, *proved*). The theorems `implemented_iff` and `proved_iff` keep
these levels tied to the functions that actually exist.

| Identifier | Algorithms and parameters | Level today |
| --- | --- | --- |
| TLS 1.3 `0x1301` `TLS_AES_128_GCM_SHA256` | AEAD AES-128-GCM (16-octet tag, 12-octet nonce); HKDF-SHA-256 | recognized; SHA-256 **proved** |
| TLS 1.3 `0x1302` `TLS_AES_256_GCM_SHA384` | AES-256-GCM; HKDF-SHA-384 | recognized |
| TLS 1.3 `0x1303` `TLS_CHACHA20_POLY1305_SHA256` | ChaCha20-Poly1305 (RFC 8439); HKDF-SHA-256 | recognized; SHA-256 **proved** |
| TLS 1.3 `0x1304`/`0x1305` | AES-128-CCM with 16/8-octet tags; HKDF-SHA-256 | recognized |
| TLS 1.2 `0xC02B`/`0xC02F`/`0xC02C`/`0xC030`/`0xCCA8`/`0xCCA9` | ECDHE + ECDSA/RSA; AES-GCM or ChaCha20-Poly1305; PRF with HMAC-SHA-256/384 | recognized |
| TLS 1.2 `0x002F`/`0x0035`/`0x009C` | static RSA; AES-CBC + HMAC-SHA-1 or AES-GCM | recognized; on the RFC 9113 App. A block list (`h2_rsa_blocked`) |
| Groups `0x0017`–`0x0019`, `0x001D`, `0x001E`, `0x0100`–`0x0102`, `0x11EC` | P-256/384/521, X25519, X448, ffdhe2048/3072/4096, X25519MLKEM768 | recognized |
| Signature schemes `0x0401`…`0x0808`, `0x0201`, `0x0203` | RSA PKCS#1 v1.5, RSA-PSS (rsae), ECDSA with P-curves, Ed25519, Ed448, and the SHA-1 legacy schemes | recognized; SHA-1 schemes excluded from TLS 1.3 (`sha1_not_tls13`) |
| ALPN `http/1.1`, `h2`, `h3`, `h2c` | no algorithm; `h2c` never over TLS | proved selection rules (`selectAlpn_sound`) |
| WebSocket `Sec-WebSocket-Accept` | SHA-1 + base64 (RFC 4648) | SHA-1 **implemented** (vectors), base64 **proved** (round trip, `Silmaril.Base64`) |
| HTTP `Repr-Digest`/`Content-Digest` (RFC 9530) `sha-256`, `sha-512` | SHA-256, SHA-512 | not yet mapped (C2) |

**Composition assumptions.** `CipherSuite.assumptions suite group sig` lists, for a session, the
assumptions under which the TLS 1.3 analyses apply (Dowling et al., J. Cryptology 2021;
RFC 8446 Appendix E): HKDF/HMAC as PRF and extractor, collision resistance, AEAD security,
DH hardness in the group (absent exactly for static RSA, `assumptions_dh_free_iff_rsa`, which
is the lack of forward secrecy), EUF-CMA signatures, and good randomness.

## Roadmap to full formalization of the common algorithms

**Current priority** (after gzip, which another task owns): DER and X.509, then Diffie–Hellman
foundations, ordered by what TLS 1.3 needs. The detailed plan is in #163
(`docs/projects/asn1-x509-dh.md`): milestones X0–X3, D1–D4, S1–S2 and K1. It refines C4–C5
below. Milestone X0, the DER core with its distinguished-encoding proofs, is that pull request.

Each milestone is a separate pull request with its own vectors. The milestones are ordered by
dependency. *Done* means kernel-checked published vectors plus the stated theorems.

| Milestone | Scope | Done when | Depends on |
| --- | --- | --- | --- |
| **C1. Hash family** | SHA-224/384/512 (sharing `paddingSHA512`), SHA-3/SHAKE (FIPS 202) | NIST CAVP short/long vectors by `decide +kernel`; `hash_block_length` analogues; level `implemented` in the catalogue | `Word`, `Padding` |
| **C2. MACs and KDFs** | HMAC (RFC 2104) generic over a hash, HKDF (RFC 5869), the TLS 1.3 `HKDF-Expand-Label` and `Derive-Secret` (RFC 8446 §7.1), the TLS 1.2 PRF (RFC 5246 §5) | RFC 4231 HMAC vectors, RFC 5869 HKDF vectors, RFC 8448 key-schedule traces; theorem: HMAC block-size padding and key hashing as in RFC 2104 | C1 |
| **C3. AEAD** | ChaCha20, Poly1305 and the AEAD (RFC 8439), AES-128/256 (FIPS 197), GCM (SP 800-38D), CCM (SP 800-38C), the RFC 5116 interface | RFC 8439 §2 vectors, FIPS 197 App. C, the GCM spec vectors; theorem: `open (seal m) = some m` for every key, nonce and AD (functional round trip), and tag mismatch is rejected | `Word` |
| **C4. Key exchange** | X25519/X448 (RFC 7748) over Mathlib's `ZMod p`, P-256/384 ECDH (SP 800-56A), ffdhe (RFC 7919), ML-KEM-768 (FIPS 203), the X25519MLKEM768 combiner | RFC 7748 §5.2/§6.1 vectors, CAVP ECDH vectors, FIPS 203 KATs; theorems: the Montgomery ladder computes scalar multiplication on the curve (Mathlib `WeierstrassCurve`/Montgomery form), and ML-KEM decapsulation inverts encapsulation for valid keys (correctness, not security) | Mathlib number theory |
| **C5. Signatures** | Ed25519/Ed448 (RFC 8032), ECDSA (FIPS 186-5), RSA PKCS#1 v1.5 and PSS (RFC 8017) verification, ML-DSA (FIPS 204) | RFC 8032 §7 vectors, Wycheproof sets kept as data with a `#guard` runner; theorem: verification accepts what signing produces (functional) | C1, C4 |
| **C6. TLS 1.3 key schedule and record layer** | `Silmaril.Net.Tls` handshake codecs, the key schedule over C2, record protection over C3, nonce construction (RFC 8446 §5.3) | RFC 8448 example handshakes replayed byte for byte; theorems: the per-record nonce is unique within a key (the AEAD's precondition), sequence numbers never wrap within a key's lifetime | C2, C3, C4, C5 |
| **C7. Implementation refinement** | Extend the SHA-256 x86 pattern (`Crypto/X86`) to ChaCha20 and Poly1305 from a pinned library build | A contract theorem like `sha256_compress_O2` for each kernel | C3 |
| **C8. Security framework (research)** | A probabilistic game framework (distributions over Mathlib's `PMF`, oracle computations), then reductions for HMAC-PRF, the HKDF extractor and the AEAD generic composition | Each reduction is a theorem with explicit advantage bounds, and assumptions remain hypotheses. Until this exists, no security claim appears in the library | Mathlib probability |

Implementation guidance carried over from the SHA-256 work:

- List-based specifications using `UInt32`/`UInt64`, with `decide +kernel` vectors.
- A `BitVec` kernel form with an equivalence theorem where machine-level work is planned.
- Primitives stay in `Silmaril/Crypto`. Protocols take them as parameters (`hashImpl`-style
  lookups or explicit function arguments), so protocol theorems never depend on a primitive's
  internals.
- `Proofs/Crypto` needs a glob in `lakefile.toml` before longer proofs can move out of `Thms`
  headers.
