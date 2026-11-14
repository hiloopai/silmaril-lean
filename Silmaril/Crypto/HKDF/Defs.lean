module

public import Silmaril.Crypto.HMAC.Defs

@[expose] public section

/-!
# HKDF (RFC 5869), generic over a `HashFn`

* `hkdfExtract H salt ikm = HMAC-Hash(salt, IKM)`. An empty salt is `HashLen` zero octets
  (RFC 5869 §2.2).
* `hkdfExpand H prk info L`: `T(1) ‖ T(2) ‖ …`, cut to `L` octets, where
  `T(i) = HMAC-Hash(PRK, T(i-1) ‖ info ‖ i)` and `T(0)` is empty (§2.3). `L > 255·HashLen` is
  rejected (`none`).
* `hkdf H salt ikm info L`, and `HashFn.hkdfKdf H : KdfFn`.

TLS 1.3 builds its key schedule on these (`HKDF-Expand-Label`, RFC 8446 §7.1), and
`Silmaril.Net.Tls` will instantiate them. No security property is stated: HKDF's extractor and
PRF properties are named assumptions (`Catalog.Assumption.hkdfSecure`).
-/

namespace Silmaril.Crypto

/-- HKDF-Extract (RFC 5869 §2.2). -/
def hkdfExtract (H : HashFn) (salt ikm : List UInt8) : List UInt8 :=
  hmac H (if salt.isEmpty then List.replicate H.digestLen 0 else salt) ikm

/-- `n` blocks `T(i), T(i+1), …`, after the previous block `t`. -/
def hkdfBlocks (H : HashFn) (prk info : List UInt8) : Nat → List UInt8 → Nat → List UInt8
  | 0, _, _ => []
  | n + 1, t, i =>
    let t' := hmac H prk (t ++ info ++ [i.toUInt8])
    t' ++ hkdfBlocks H prk info n t' (i + 1)

/-- HKDF-Expand (RFC 5869 §2.3). -/
def hkdfExpand (H : HashFn) (prk info : List UInt8) (len : Nat) : Option (List UInt8) :=
  if len ≤ 255 * H.digestLen then
    some ((hkdfBlocks H prk info ((len + H.digestLen - 1) / H.digestLen) [] 1).take len)
  else none

/-- HKDF (RFC 5869 §2). -/
def hkdf (H : HashFn) (salt ikm info : List UInt8) (len : Nat) : Option (List UInt8) :=
  hkdfExpand H (hkdfExtract H salt ikm) info len

/-- HKDF as a `KdfFn`. -/
def HashFn.hkdfKdf (H : HashFn) : KdfFn where
  derive ikm salt info len := hkdf H salt ikm info len

end Silmaril.Crypto
