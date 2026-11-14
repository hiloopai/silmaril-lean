module

public import Silmaril.Crypto.Catalog.Defs

@[expose] public section

/-!
# TLS and HTTP-adjacent registries mapped to algorithms (RFC 8446, RFC 5246, RFC 7301, RFC 6455)

Identifiers that appear on the wire, mapped to the algorithms of `Silmaril.Crypto.Catalog`
with their parameters, and to the assumptions a composition needs:

* **TLS cipher suites** (IANA "TLS Cipher Suites"; RFC 8446 §B.4 for TLS 1.3, RFC 5288,
  RFC 5289, RFC 7905 for the TLS 1.2 suites listed): `CipherSuite`, `CipherSuite.ofCode`,
  `CipherSuite.components`. A TLS 1.3 suite fixes only the AEAD and the HKDF hash; key exchange
  and authentication are negotiated separately (RFC 8446 §4.2.7, §4.2.3). A TLS 1.2 suite
  also fixes the key exchange and the signature family.
* **Named groups** (RFC 8446 §4.2.7, RFC 7919, and the hybrid `X25519MLKEM768` code point
  0x11EC registered from draft-ietf-tls-ecdhe-mlkem): `NamedGroup`.
* **Signature schemes** (RFC 8446 §4.2.3): `SignatureScheme`, including the legacy SHA-1
  schemes that RFC 8446 forbids in TLS 1.3 signatures and RFC 9155 deprecates for TLS 1.2.
* **ALPN protocol IDs** (RFC 7301, IANA "TLS Application-Layer Protocol Negotiation (ALPN)
  Protocol IDs"): `AlpnId`, and the server selection of RFC 7301 §3.2 (`selectAlpn`).
* **WebSocket** (RFC 6455 §4.2.2): the accept value uses SHA-1 and base64 (not a security
  function, `Silmaril.Net.WebSocket.Handshake`).

For each suite, `CipherSuite.assumptions` lists the computational assumptions (as
`Silmaril.Crypto.Catalog.Assumption` data) under which the published analyses of the TLS 1.3
handshake and record layer give their guarantees (Dowling, Fischlin, Günther, Stebila, *A
Cryptographic Analysis of the TLS 1.3 Handshake Protocol*, J. Cryptology 2021; RFC 8446
Appendix E). No security theorem is stated: these are the hypotheses a future reduction would
discharge or take, nothing more.

**HTTP/2 over TLS** (RFC 9113 §9.2): TLS 1.2 or later, and with TLS 1.2 only ephemeral key
exchange and AEAD suites outside the Appendix A block list: `h2Acceptable`.
-/

namespace Silmaril.Net.Tls

open Silmaril.Crypto.Catalog

/-- TLS protocol versions (RFC 8446 §4.2.1 `supported_versions` values). -/
inductive TlsVersion where
  | tls10 | tls11 | tls12 | tls13
  deriving DecidableEq, Repr

def TlsVersion.code : TlsVersion → Nat
  | .tls10 => 0x0301 | .tls11 => 0x0302 | .tls12 => 0x0303 | .tls13 => 0x0304

/-! ## Cipher suites -/

/-- The cipher suites this library recognizes. -/
inductive CipherSuite where
  -- TLS 1.3 (RFC 8446 §B.4)
  | tls13_aes_128_gcm_sha256 | tls13_aes_256_gcm_sha384 | tls13_chacha20_poly1305_sha256
  | tls13_aes_128_ccm_sha256 | tls13_aes_128_ccm_8_sha256
  -- TLS 1.2 ECDHE AEAD suites (RFC 5289, RFC 7905)
  | ecdhe_ecdsa_aes_128_gcm_sha256 | ecdhe_rsa_aes_128_gcm_sha256
  | ecdhe_ecdsa_aes_256_gcm_sha384 | ecdhe_rsa_aes_256_gcm_sha384
  | ecdhe_rsa_chacha20_poly1305_sha256 | ecdhe_ecdsa_chacha20_poly1305_sha256
  -- TLS 1.2 legacy suites (on the RFC 9113 Appendix A block list)
  | rsa_aes_128_cbc_sha | rsa_aes_256_cbc_sha | rsa_aes_128_gcm_sha256
  deriving DecidableEq, Repr

namespace CipherSuite

def code : CipherSuite → Nat
  | tls13_aes_128_gcm_sha256 => 0x1301 | tls13_aes_256_gcm_sha384 => 0x1302
  | tls13_chacha20_poly1305_sha256 => 0x1303 | tls13_aes_128_ccm_sha256 => 0x1304
  | tls13_aes_128_ccm_8_sha256 => 0x1305
  | ecdhe_ecdsa_aes_128_gcm_sha256 => 0xC02B | ecdhe_rsa_aes_128_gcm_sha256 => 0xC02F
  | ecdhe_ecdsa_aes_256_gcm_sha384 => 0xC02C | ecdhe_rsa_aes_256_gcm_sha384 => 0xC030
  | ecdhe_rsa_chacha20_poly1305_sha256 => 0xCCA8
  | ecdhe_ecdsa_chacha20_poly1305_sha256 => 0xCCA9
  | rsa_aes_128_cbc_sha => 0x002F | rsa_aes_256_cbc_sha => 0x0035
  | rsa_aes_128_gcm_sha256 => 0x009C

def all : List CipherSuite :=
  [tls13_aes_128_gcm_sha256, tls13_aes_256_gcm_sha384, tls13_chacha20_poly1305_sha256,
   tls13_aes_128_ccm_sha256, tls13_aes_128_ccm_8_sha256, ecdhe_ecdsa_aes_128_gcm_sha256,
   ecdhe_rsa_aes_128_gcm_sha256, ecdhe_ecdsa_aes_256_gcm_sha384, ecdhe_rsa_aes_256_gcm_sha384,
   ecdhe_rsa_chacha20_poly1305_sha256, ecdhe_ecdsa_chacha20_poly1305_sha256,
   rsa_aes_128_cbc_sha, rsa_aes_256_cbc_sha, rsa_aes_128_gcm_sha256]

/-- The suite of a code point; `none` for one this library does not recognize. -/
def ofCode (n : Nat) : Option CipherSuite := all.find? (·.code == n)

/-- The TLS versions a suite is defined for. -/
def tls13 : CipherSuite → Bool
  | tls13_aes_128_gcm_sha256 | tls13_aes_256_gcm_sha384 | tls13_chacha20_poly1305_sha256
  | tls13_aes_128_ccm_sha256 | tls13_aes_128_ccm_8_sha256 => true
  | _ => false

/-- How the suite authenticates the server (TLS 1.2), if it fixes it. -/
inductive KeyExchange where
  /-- Negotiated separately (TLS 1.3). -/
  | negotiated
  | ecdheEcdsa | ecdheRsa
  /-- Static RSA key transport: no forward secrecy. -/
  | rsa
  deriving DecidableEq, Repr

/-- The parts of a suite. -/
structure Components where
  /-- Record protection. -/
  record : Algorithm
  /-- Key derivation (HKDF in TLS 1.3, the TLS 1.2 PRF's HMAC hash). -/
  kdf : Algorithm
  keyExchange : KeyExchange
  deriving DecidableEq, Repr

def components : CipherSuite → Components
  | tls13_aes_128_gcm_sha256 => ⟨.aead (.aesGcm 128), .hkdf .sha256, .negotiated⟩
  | tls13_aes_256_gcm_sha384 => ⟨.aead (.aesGcm 256), .hkdf .sha384, .negotiated⟩
  | tls13_chacha20_poly1305_sha256 => ⟨.aead .chacha20Poly1305, .hkdf .sha256, .negotiated⟩
  | tls13_aes_128_ccm_sha256 => ⟨.aead (.aesCcm 128 16), .hkdf .sha256, .negotiated⟩
  | tls13_aes_128_ccm_8_sha256 => ⟨.aead (.aesCcm 128 8), .hkdf .sha256, .negotiated⟩
  | ecdhe_ecdsa_aes_128_gcm_sha256 => ⟨.aead (.aesGcm 128), .hmac .sha256, .ecdheEcdsa⟩
  | ecdhe_rsa_aes_128_gcm_sha256 => ⟨.aead (.aesGcm 128), .hmac .sha256, .ecdheRsa⟩
  | ecdhe_ecdsa_aes_256_gcm_sha384 => ⟨.aead (.aesGcm 256), .hmac .sha384, .ecdheEcdsa⟩
  | ecdhe_rsa_aes_256_gcm_sha384 => ⟨.aead (.aesGcm 256), .hmac .sha384, .ecdheRsa⟩
  | ecdhe_rsa_chacha20_poly1305_sha256 => ⟨.aead .chacha20Poly1305, .hmac .sha256, .ecdheRsa⟩
  | ecdhe_ecdsa_chacha20_poly1305_sha256 =>
    ⟨.aead .chacha20Poly1305, .hmac .sha256, .ecdheEcdsa⟩
  | rsa_aes_128_cbc_sha => ⟨.cbcHmac 128 .sha1, .hmac .sha256, .rsa⟩
  | rsa_aes_256_cbc_sha => ⟨.cbcHmac 256 .sha1, .hmac .sha256, .rsa⟩
  | rsa_aes_128_gcm_sha256 => ⟨.aead (.aesGcm 128), .hmac .sha256, .rsa⟩

/-- RFC 9113 Appendix A: suites an HTTP/2 endpoint MAY treat as `INADEQUATE_SECURITY`
under TLS 1.2 (non-ephemeral key exchange or non-AEAD record protection). Of the suites
here: the three static-RSA suites. -/
def h2Blocked (s : CipherSuite) : Bool := s.components.keyExchange == .rsa ||
  match s.components.record with
  | .aead _ => false
  | _ => true

/-- The assumptions under which published analyses give confidentiality and authentication
for a session with this suite, key exchange group `g` and signature scheme `sig`
(TLS 1.3: Dowling et al. 2021; RFC 8446 Appendix E). Data only. -/
def assumptions (s : CipherSuite) (g : Group) (sig : SigAlg) : List Assumption :=
  let c := s.components
  let hashOf : Algorithm → List HashAlg
    | .hkdf h | .hmac h => [h]
    | _ => []
  let aeadOf : Algorithm → List AeadAlg
    | .aead a => [a]
    | _ => []
  (hashOf c.kdf).flatMap (fun h => [.hkdfSecure h, .hmacPrf h, .collisionResistant h]) ++
    (aeadOf c.record).map .aeadSecure ++
    (if c.keyExchange == .rsa then [] else [.dhHard g]) ++ [.eufCma sig, .goodRandomness]

end CipherSuite

/-! ## Named groups and signature schemes -/

/-- RFC 8446 §4.2.7 `NamedGroup` code points (and RFC 7919, and 0x11EC). -/
def NamedGroup.ofCode : Nat → Option Group
  | 0x0017 => some .secp256r1 | 0x0018 => some .secp384r1 | 0x0019 => some .secp521r1
  | 0x001D => some .x25519 | 0x001E => some .x448
  | 0x0100 => some (.ffdhe 2048) | 0x0101 => some (.ffdhe 3072) | 0x0102 => some (.ffdhe 4096)
  | 0x11EC => some .x25519mlkem768
  | _ => none

/-- RFC 8446 §4.2.3 `SignatureScheme` code points. -/
def SignatureScheme.ofCode : Nat → Option SigAlg
  | 0x0401 => some (.rsaPkcs1 .sha256) | 0x0501 => some (.rsaPkcs1 .sha384)
  | 0x0601 => some (.rsaPkcs1 .sha512)
  | 0x0403 => some (.ecdsa .secp256r1 .sha256) | 0x0503 => some (.ecdsa .secp384r1 .sha384)
  | 0x0603 => some (.ecdsa .secp521r1 .sha512)
  | 0x0804 => some (.rsaPss .sha256) | 0x0805 => some (.rsaPss .sha384)
  | 0x0806 => some (.rsaPss .sha512)
  | 0x0807 => some .ed25519 | 0x0808 => some .ed448
  | 0x0201 => some (.rsaPkcs1 .sha1) | 0x0203 => some (.ecdsa .secp256r1 .sha1)
  | _ => none

/-- The hash a signature scheme uses, if it has a separate one. -/
def sigHash? : SigAlg → Option HashAlg
  | .rsaPkcs1 h | .rsaPss h | .ecdsa _ h => some h
  | _ => none

/-- RFC 8446 §4.2.3: RSASSA-PKCS1-v1_5 and SHA-1 schemes "MUST NOT be used" for TLS 1.3
handshake signatures (PKCS#1 v1.5 only in certificates). -/
def allowedInTls13Handshake : SigAlg → Bool
  | .rsaPkcs1 _ => false
  | s => sigHash? s != some .sha1

/-! ## ALPN (RFC 7301) -/

/-- ALPN protocol IDs relevant to HTTP and WebSockets (octet strings on the wire). -/
inductive AlpnId where
  | http10 | http11 | h2 | h3
  /-- `h2c`: reserved, names HTTP/2 over cleartext TCP; never negotiated in TLS (RFC 9113 §3.1). -/
  | h2c
  | other (id : List UInt8)
  deriving DecidableEq, Repr

def AlpnId.bytes : AlpnId → List UInt8
  | .http10 => ascii "http/1.0" | .http11 => ascii "http/1.1" | .h2 => ascii "h2"
  | .h3 => ascii "h3" | .h2c => ascii "h2c" | .other b => b

/-- RFC 7301 §3.2: the server selects, in its own preference order, the first protocol the
client offered; `none` sends the `no_application_protocol` alert (120). `h2c` is never
selected over TLS. -/
def selectAlpn (server client : List AlpnId) : Option AlpnId :=
  server.find? fun p => p != .h2c && client.contains p

/-- RFC 9113 §9.2: HTTP/2 over TLS needs TLS 1.2 or later, and under TLS 1.2 a suite off the
block list. -/
def h2Acceptable (v : TlsVersion) (s : CipherSuite) : Bool :=
  match v with
  | .tls13 => s.tls13
  | .tls12 => !s.tls13 && !s.h2Blocked
  | _ => false

end Silmaril.Net.Tls
