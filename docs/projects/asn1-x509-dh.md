# DER, X.509 and Diffie–Hellman: foundations and plan

This page plans certificate handling and key agreement, as TLS 1.3 needs them. It records what
exists and what each next step depends on. It keeps four kinds of work apart:

1. **Encoding**: ASN.1 values in DER. These are parsing and serialization theorems.
2. **Certificate semantics**: X.509 fields, extensions and RFC 5280 path validation. These are
   decision procedures over parsed data, with correctness theorems against RFC 5280's rules.
3. **Functional cryptography**: arithmetic in finite fields and on curves, and signature
   verification as functions. Theorems here are correctness (for example, both parties of a DH
   exchange compute the same secret), checked against published vectors.
4. **Computational security**: hardness of DH, unforgeability of signatures. This is not
   formalized. These properties are named assumptions (`Silmaril.Crypto.Catalog.Assumption`
   in #157), never axioms.

Finite-field DH (FFDH, RFC 7919 groups) and elliptic-curve DH (ECDH: X25519/X448 per RFC 7748,
P-256/P-384 per SP 800-56A) share only the protocol shape. Their arithmetic, encodings and
validation rules are different, so they are separate milestones.

## Audit (before this work)

- **ASN.1/DER: none.** `regions.toml` lists ASN.1 under `Formats`, but no module existed.
  `Silmaril.Formats.PER` is about partial equivalence relations, not ASN.1 PER.
- **X.509: none.**
- **Modular arithmetic for cryptography: none.** Mathlib provides `ZMod`, `Nat.ModEq`,
  `Nat.pow_mod` and primality tools. `Silmaril` has no `powMod`, Montgomery ladder or curve
  code.
- **DH: none.** The TLS registry map in #157 recognizes the groups (`ffdhe2048`…,
  `x25519`, `secp256r1`, `X25519MLKEM768`) by code point only.
- **Unsigned big-endian codecs.** Fixed-width `Net.Wire.beBytes`/`beValue` (#162) and the new
  minimal-width `Der.natBytes`/`natValue` (this pull request). The `Formats` region cannot
  import `Net`, so the minimal codec lives here. If the bytes-standards proposal
  (moria-lean#2033) settles a lower home, both should move there.

## What TLS 1.3 needs, in order

A TLS 1.3 client that authenticates a server performs these steps (RFC 8446 §4):

1. **Key exchange.** X25519 is the common default. P-256 is also mandatory to implement
   (RFC 8446 §9.1). `X25519MLKEM768` is increasingly the deployed default. FFDHE is rare.
2. **Certificate parsing.** DER, then X.509 structure, then SubjectPublicKeyInfo.
3. **CertificateVerify and chain signatures.** ECDSA P-256/P-384 with SHA-256/384, and RSA-PSS
   and RSA PKCS#1 v1.5 (in certificates) with SHA-256/384. Signatures arrive as DER (ECDSA's
   `r, s` per RFC 3279) and keys as DER (RSA per RFC 8017 Appendix A, EC points in BIT
   STRINGs).
4. **Path validation** (RFC 5280 §6). Names, validity periods, basicConstraints, keyUsage, and
   then hostname matching (RFC 9525).
5. **Key schedule.** HKDF with SHA-256/384 (crypto.md milestones C1–C2).

DER is therefore on the critical path of steps 2–4, and of every signature format. The plan
orders it first.

## Milestones

| # | Milestone | Content | Done when | Depends on |
| --- | --- | --- | --- | --- |
| **X0** | DER core (this pull request) | Minimal unsigned octets, low-tag identifiers, definite minimal lengths, TLV items, non-negative INTEGER | Round trip **and** uniqueness (`decode_sound`) proved; X.690 examples; a real certificate parsed by the kernel | — |
| X1 | DER types | OBJECT IDENTIFIER (base-128 arcs), BIT STRING (unused bits, DER zero padding), BOOLEAN (DER `FF`), NULL, UTCTime/GeneralizedTime (DER profiles), PrintableString/UTF8String/IA5String, negative INTEGERs | A round-trip and uniqueness theorem per type; the RFC 5280 and X.690 examples | X0 |
| X2 | X.509 structure | `Certificate`, `TBSCertificate`, `AlgorithmIdentifier`, `Name`, `Validity`, `SubjectPublicKeyInfo` and extensions (basicConstraints, keyUsage, extKeyUsage, subjectAltName), with an OID registry that maps algorithm OIDs to `Crypto.Catalog` algorithms | Parse and re-encode real roots (ISRG X1/X2, a P-384 and an RSA-4096 root) byte for byte; the signed `tbsCertificate` octets are provably a sub-slice of the input | X1 |
| X3 | Path validation | The RFC 5280 §6.1 algorithm over parsed certificates, with signature verification as a **parameter** (`verify : Algorithm → Key → Bytes → Sig → Bool`), and RFC 9525 name matching | Theorems: an accepted path satisfies every §6.1 check (validity, issuer and subject chaining, basicConstraints/pathLen, keyUsage); test vectors from NIST PKITS / x509-limbo as data | X2 |
| D1 | Modular arithmetic | `powMod` by square-and-multiply, with `powMod b e m = b ^ e % m` proved; modular inverse via extended gcd, proved against Mathlib's `ZMod` | Proofs plus kernel-checked 2048-bit evaluations | Mathlib |
| D2 | FFDH | The RFC 7919 `ffdhe2048`/`3072`/`4096` groups as data; public value checks (`1 < y < p − 1`, RFC 7919 §5.1); TLS key share encoding (left-padded to the size of `p`, RFC 8446 §4.2.8.1) | Agreement theorem `(g^a)^b = (g^b)^a mod p`; padding round trip; the hex constants checked against the RFC text (hash pinned). The primality of `p` stays an assumption: it is stated in the RFC, not proved | D1 |
| D3 | X25519/X448 | The Montgomery ladder over `ZMod p` and RFC 7748 decoding (clamping, masking the top bit) | RFC 7748 §5.2 and §6.1 vectors; agreement theorem: the ladder computes scalar multiplication, so both sides agree (through Mathlib's elliptic-curve group law) | D1, Mathlib |
| D4 | P-256/P-384 ECDH | Weierstrass arithmetic, SEC 1 point encoding and validation (on-curve checks) | CAVP ECDH vectors; on-curve validation theorem | D1 |
| S1 | ECDSA verification | SEC 1 / FIPS 186-5 verify over D4, with signatures in DER (X0) | Wycheproof/CAVP vectors; **functional** theorem only: verification accepts what signing produces | D4, X0, SHA-384 (crypto.md C1) |
| S2 | RSA verification | RSAVP1 via D1, EMSA-PSS and EMSA-PKCS1-v1_5 (RFC 8017), keys in DER | RFC 8017 / Wycheproof vectors; a functional theorem | D1, X0, C1 |
| K1 | ML-KEM-768 and the hybrid | FIPS 203 and the X25519MLKEM768 combiner | FIPS 203 KATs; decapsulation inverts encapsulation (correctness) | C1 (SHA-3), D3 |

Recommended order for TLS 1.3 interoperability: X0, then X1 (both on the critical path for all
certificates), then D1, then D3 (X25519 covers most handshakes), then X2, S1, X3, then S2, D4,
K1, and D2 last (FFDHE is rarely negotiated).

Each milestone is one small pull request: a reusable functional piece with its theorems and
published vectors, not a stub. No milestone claims computational security.
