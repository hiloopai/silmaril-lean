module

public import Silmaril.Crypto.Interface.Defs
public import Silmaril.Crypto.HashFns.Defs

@[expose] public section

/-!
# HMAC (RFC 2104, FIPS 198-1), generic over a `HashFn`

    HMAC(K, text) = H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))

`K₀` is the key reduced to exactly `H.blockLen` octets (RFC 2104 §2, FIPS 198-1 §4). A longer
key is hashed first, and a shorter one is right-padded with zeros.

* `hmac H key msg`, and `HashFn.hmacMac H : MacFn`, the MAC interface instance (tags of
  `H.digestLen` octets, verification by comparison).
* `hmacSHA256 = hmac HashFn.sha256`.

FIPS 198-1 §5 truncation is `List.take t` on the result. Key-length recommendations
(FIPS 198-1 §3: at least `L/2` octets) are the caller's policy, not enforced here.

Ported from the hiloopai/silmaril development (`Silmaril/Crypto/HMAC.lean`, written for that
project), generalized from a block size and a bare function to a `HashFn`.

No security property is stated. HMAC's PRF security (Bellare 2006) is a named assumption
(`Catalog.Assumption.hmacPrf`), not a theorem.
-/

namespace Silmaril.Crypto

def hmacIpad : UInt8 := 0x36
def hmacOpad : UInt8 := 0x5c

/-- RFC 2104 §2 steps 1–3: the key reduced to exactly `H.blockLen` octets. -/
def hmacKey (H : HashFn) (key : List UInt8) : List UInt8 :=
  let k := if key.length > H.blockLen then H.hash key else key
  k ++ List.replicate (H.blockLen - k.length) 0

/-- HMAC with the hash `H`. -/
def hmac (H : HashFn) (key msg : List UInt8) : List UInt8 :=
  let k0 := hmacKey H key
  H.hash (k0.map (· ^^^ hmacOpad) ++ H.hash (k0.map (· ^^^ hmacIpad) ++ msg))

/-- HMAC as a MAC (`MacFn`). -/
def HashFn.hmacMac (H : HashFn) : MacFn where
  keyLen := none
  tagLen := H.digestLen
  tag := hmac H

/-- HMAC-SHA-256. -/
abbrev hmacSHA256 (key msg : List UInt8) : List UInt8 := hmac HashFn.sha256 key msg

end Silmaril.Crypto
