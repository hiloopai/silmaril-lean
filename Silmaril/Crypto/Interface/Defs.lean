module

@[expose] public section

/-!
# Typed interfaces for cryptographic primitives

Each kind of primitive is a structure that holds its **parameters** (lengths), its
**functions**, and nothing else. Each kind also has a separate `Correct` predicate: the
*functional* law that every honest use must satisfy (decryption inverts encryption, both parties
of a key agreement compute the same secret, verification accepts honest signatures).

| Kind | Structure | Inputs kept apart | Functional law |
| --- | --- | --- | --- |
| Hash | `HashFn` | message | `digest_length` (part of the structure) |
| MAC | `MacFn` | key, message, tag | `MacFn.Correct`: `verify k m (tag k m)` |
| KDF | `KdfFn` | input keying material, salt, info, output length | `KdfFn.Correct`: the output has the requested length |
| Block cipher | `BlockCipher` | key, block | `BlockCipher.Correct`: `decrypt k ∘ encrypt k = id` on blocks |
| AEAD (RFC 5116) | `Aead` | key, nonce, associated data, plaintext, ciphertext with tag | `Aead.Correct`: `decrypt k n a (encrypt k n a p) = some p` |
| Key agreement | `KeyAgreement` | private key, public value, shared secret | `KeyAgreement.Correct`: both sides agree |
| Signature | `Signature` | signing key, verification key, message, signature | `Signature.Correct`: `verify (pub sk) m (sign sk m) = true` |

**What is not here: security.** Collision resistance, PRF security, IND-CCA, EUF-CMA and DH
hardness are computational properties of *families* of functions against bounded adversaries.
Stating them needs a probabilistic game framework that this library does not have. They are
therefore not fields of these structures and not Lean axioms. Protocol modules name the
assumptions they rely on as data (`Silmaril.Crypto.Catalog.Assumption`). A `Correct` proof says
nothing about security.

**Evidence is not one level.** For a given instance, three different things can be known:

1. **vectors**: published known-answer tests reproduced by the kernel;
2. **functional theorems**: `Correct`, round trips, or agreement with another specification;
3. **implementation refinement**: machine code proved to compute the specification (for
   example, the x86-64 SHA-256 compression in `Silmaril.Crypto.X86.Sha256O2`).

None of these implies the others, and none implies security. Registries and catalogues should
record them separately.

**Registries are adapters.** Protocol identifiers (TLS code points, JOSE/COSE names, HTTP digest
names) map *to* instances of these structures in protocol modules. The structures know nothing
about any registry.

Octets are `List UInt8` throughout, which is the convention of the existing references
(`Silmaril.Crypto.SHA256`).
-/

namespace Silmaril.Crypto

/-- A hash function with a fixed digest length and the block length that HMAC needs. -/
structure HashFn where
  /-- Digest length in octets. -/
  digestLen : Nat
  /-- Input block length in octets (64 for SHA-256, 128 for SHA-512). -/
  blockLen : Nat
  hash : List UInt8 → List UInt8
  digest_length : ∀ m, (hash m).length = digestLen

/-- A message authentication code. -/
structure MacFn where
  keyLen : Option Nat
  tagLen : Nat
  tag : (key msg : List UInt8) → List UInt8
  /-- Verification; the default compares tags. -/
  verify : (key msg tag : List UInt8) → Bool := fun k m t => tag k m == t

/-- A MAC is correct when every honest tag verifies and has the stated length. -/
def MacFn.Correct (M : MacFn) : Prop :=
  ∀ k m, M.verify k m (M.tag k m) = true ∧ (M.tag k m).length = M.tagLen

/-- A key derivation function: input keying material, salt, context information and the
requested output length. -/
structure KdfFn where
  derive : (ikm salt info : List UInt8) → (len : Nat) → Option (List UInt8)

/-- A KDF is correct when every successful derivation has the requested length. -/
def KdfFn.Correct (K : KdfFn) : Prop :=
  ∀ ikm salt info len out, K.derive ikm salt info len = some out → out.length = len

/-- A block cipher on `blockLen`-octet blocks. -/
structure BlockCipher where
  keyLen : Nat
  blockLen : Nat
  encrypt : (key block : List UInt8) → List UInt8
  decrypt : (key block : List UInt8) → List UInt8

/-- Decryption inverts encryption on keys and blocks of the right lengths. -/
def BlockCipher.Correct (C : BlockCipher) : Prop :=
  ∀ k b, k.length = C.keyLen → b.length = C.blockLen → C.decrypt k (C.encrypt k b) = b

/-- Authenticated encryption with associated data (RFC 5116 §2). -/
structure Aead where
  keyLen : Nat
  nonceLen : Nat
  tagLen : Nat
  /-- Authenticated encryption: the ciphertext with its tag appended. -/
  encrypt : (key nonce ad plaintext : List UInt8) → List UInt8
  /-- Authenticated decryption: `none` when authentication fails. -/
  decrypt : (key nonce ad ciphertext : List UInt8) → Option (List UInt8)

/-- Decrypting what was encrypted with the same key, nonce and associated data returns the
plaintext (RFC 5116 §2.2). Instances with a plaintext length limit (AES-GCM: 2^36 − 31 octets)
state a bounded variant. -/
def Aead.Correct (A : Aead) : Prop :=
  ∀ k n a p, k.length = A.keyLen → n.length = A.nonceLen →
    A.decrypt k n a (A.encrypt k n a p) = some p

/-- A key agreement scheme (Diffie–Hellman style). Public values may be rejected
(`none`), for example when they are not on the curve or not in the subgroup. -/
structure KeyAgreement where
  Priv : Type
  Pub : Type
  Shared : Type
  pub : Priv → Pub
  shared : Priv → Pub → Option Shared

/-- Both parties compute the same secret from honest public values. -/
def KeyAgreement.Correct (K : KeyAgreement) : Prop :=
  ∀ a b, K.shared a (K.pub b) = K.shared b (K.pub a) ∧ (K.shared a (K.pub b)).isSome

/-- A signature scheme. Signing takes explicit randomness `rnd` (ignored by deterministic
schemes such as Ed25519 or RFC 6979 ECDSA). -/
structure Signature where
  SignKey : Type
  VerifyKey : Type
  Rand : Type
  pub : SignKey → VerifyKey
  sign : SignKey → Rand → List UInt8 → List UInt8
  verify : VerifyKey → List UInt8 → List UInt8 → Bool

/-- Honest signatures verify. -/
def Signature.Correct (S : Signature) : Prop :=
  ∀ sk r m, S.verify (S.pub sk) m (S.sign sk r m) = true

end Silmaril.Crypto
