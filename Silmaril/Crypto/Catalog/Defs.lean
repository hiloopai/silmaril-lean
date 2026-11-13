module

public import Silmaril.Crypto.SHA256
public import Silmaril.Crypto.SHA1.Defs

@[expose] public section

/-!
# A catalogue of cryptographic algorithms and what Silmaril knows about each

Protocol registries (TLS cipher suites, named groups, signature schemes; WebSocket's accept
hash; HTTP digest fields) name cryptographic algorithms. This module lists those algorithms,
with their parameters, and records **how much of each this library has**, on four levels:

| Level | Meaning |
| --- | --- |
| `advertised` | A registry this library models names it (it can appear on the wire). |
| `recognized` | This library parses its identifier and knows its parameters. |
| `implemented` | An executable specification exists in Silmaril (`hashImpl` returns it). |
| `proved` | Beyond test vectors, a functional theorem relates it to another artefact (for SHA-256: the x86-64 `-O2` compression refines the reference, `Silmaril.Crypto.X86.Sha256O2`). |

The level is a function of the data in this module (`Algorithm.level`), and the
`implemented` level is tied to actual functions: `Catalog.Thms.implemented_iff` proves that an
algorithm is at least `implemented` exactly when `hashImpl` returns a function, and
`Catalog.Thms.vectors_ok` re-checks published vectors through `hashImpl` in the kernel.

**Security properties are assumptions, never theorems here.** `Assumption` names the standard
computational assumptions (collision resistance, PRF security, AEAD security, Diffie–Hellman
variants, EUF-CMA, IND-CCA KEMs) as data, so that protocol modules can state which assumptions a
composition needs (`Silmaril.Net.Tls.Registry`). They are not Lean axioms and nothing derives
a security statement from them. Proving reductions needs a probabilistic game framework that
this repository does not have; see docs/projects/crypto.md for the plan.
-/

namespace Silmaril.Crypto.Catalog

/-- Hash functions. -/
inductive HashAlg where
  | md5 | sha1 | sha224 | sha256 | sha384 | sha512 | sha3_256 | shake128 | shake256
  deriving DecidableEq, Repr

/-- AEAD algorithms (RFC 5116 registry) and their key sizes. -/
inductive AeadAlg where
  | aesGcm (keyBits : Nat)
  /-- AES-CCM with an 8- or 16-octet tag. -/
  | aesCcm (keyBits : Nat) (tagLen : Nat)
  | chacha20Poly1305
  deriving DecidableEq, Repr

/-- Key exchange groups and KEMs. -/
inductive Group where
  | x25519 | x448 | secp256r1 | secp384r1 | secp521r1
  /-- Finite-field groups of RFC 7919. -/
  | ffdhe (bits : Nat)
  | mlkem768
  /-- The hybrid X25519 + ML-KEM-768 group (`X25519MLKEM768`). -/
  | x25519mlkem768
  deriving DecidableEq, Repr

/-- Signature algorithms. -/
inductive SigAlg where
  | rsaPkcs1 (h : HashAlg)
  | rsaPss (h : HashAlg)
  | ecdsa (curve : Group) (h : HashAlg)
  | ed25519 | ed448
  | mldsa (level : Nat)
  deriving DecidableEq, Repr

/-- Any algorithm in the catalogue. -/
inductive Algorithm where
  | hash (h : HashAlg)
  | hmac (h : HashAlg)
  | hkdf (h : HashAlg)
  | aead (a : AeadAlg)
  /-- Legacy CBC encryption with HMAC (TLS 1.2 only). -/
  | cbcHmac (keyBits : Nat) (h : HashAlg)
  | kex (g : Group)
  | sig (s : SigAlg)
  /-- Non-cryptographic checksums, listed so that they are not mistaken for MACs. -/
  | crc32c | crc32 | adler32
  deriving DecidableEq, Repr

/-- How much of an algorithm this library has. -/
inductive Level where
  | advertised | recognized | implemented | proved
  deriving DecidableEq, Repr, Ord

/-- The executable hash specifications in Silmaril (the reference digests). MD5 exists only
in a `Raw` tree (`Silmaril.Raw.Semantics.CPort.Crypto.MD5`), which is not an API, so it is not
listed. -/
def hashImpl : HashAlg → Option (List UInt8 → List UInt8)
  | .sha256 => some Silmaril.Crypto.SHA256.digest
  | .sha1 => some Silmaril.Crypto.SHA1.digest
  | _ => none

/-- Digest lengths in octets (FIPS 180-4, FIPS 202, RFC 1321). SHAKE has none. -/
def HashAlg.digestLen : HashAlg → Option Nat
  | .md5 => some 16 | .sha1 => some 20 | .sha224 => some 28 | .sha256 => some 32
  | .sha384 => some 48 | .sha512 => some 64 | .sha3_256 => some 32
  | .shake128 | .shake256 => none

/-- Algorithms with a functional theorem beyond vectors: SHA-256 (the BitVec kernel
compression equals the reference, `SHA256.processBlock_eq_compressBlock`, and the x86-64 `-O2`
compression refines it, `Crypto.X86.Sha256O2`). -/
def hasFunctionalProof : Algorithm → Bool
  | .hash .sha256 => true
  | _ => false

/-- The level of an algorithm in this library. Every algorithm in the catalogue is at least
`recognized` when a modelled registry maps a code point to it; algorithms are `advertised`
only through a registry entry this library does not parse (none yet). -/
def Algorithm.level : Algorithm → Level
  | .hash h =>
    if hasFunctionalProof (.hash h) then .proved
    else if (hashImpl h).isSome then .implemented else .recognized
  | _ => .recognized

/-! ## Assumptions -/

/-- Standard computational assumptions, as names. They are data, not axioms. -/
inductive Assumption where
  /-- Collision resistance of a hash. -/
  | collisionResistant (h : HashAlg)
  /-- HMAC with this hash is a PRF (and a dual PRF where the TLS 1.3 key schedule needs it). -/
  | hmacPrf (h : HashAlg)
  /-- HKDF-Extract is a randomness extractor / PRF on its inputs. -/
  | hkdfSecure (h : HashAlg)
  /-- The AEAD is IND-CPA and INT-CTXT secure for the record layer's nonce discipline. -/
  | aeadSecure (a : AeadAlg)
  /-- Diffie–Hellman (in the forms the key schedule needs, e.g. PRF-ODH) is hard in the group. -/
  | dhHard (g : Group)
  /-- The KEM is IND-CCA secure. -/
  | kemIndCca (g : Group)
  /-- The signature is EUF-CMA secure. -/
  | eufCma (s : SigAlg)
  /-- Nonces or keys come from a secure random source (outside every model here). -/
  | goodRandomness
  deriving DecidableEq, Repr

/-! ## Published vectors -/

/-- A published hash test vector. -/
structure Vector where
  alg : HashAlg
  input : List UInt8
  digest : List UInt8
  /-- Where it is published. -/
  source : String

/-- The octets of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- Vectors checked through `hashImpl` (`Catalog.Thms.vectors_ok`). -/
def vectors : List Vector :=
  [⟨.sha256, ascii "abc",
    [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22,
     0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00,
     0x15, 0xad], "FIPS 180-4 Appendix B.1"⟩,
   ⟨.sha1, ascii "abc",
    [0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, 0xba, 0x3e, 0x25, 0x71, 0x78, 0x50, 0xc2,
     0x6c, 0x9c, 0xd0, 0xd8, 0x9d], "FIPS 180-4 example"⟩]

end Silmaril.Crypto.Catalog
