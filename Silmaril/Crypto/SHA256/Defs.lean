module

public import Silmaril.Crypto.SHA256
public import Silmaril.Crypto.SHA256.Equiv

/-!
# SHA-256 (FIPS 180-4): Silmaril's reference is public silmaril-lean's

* `sha256`: the digest (32 bytes), `= Silmaril.Crypto.SHA256.digest` by definition;
* `sha256_eq_silmaril`, `sha256_length`.

The list-based compression equals the `BitVec 32` kernel compression for every state and block:
`Silmaril.Crypto.SHA256.processBlock_eq_compressBlock` (re-exported from
`Silmaril.Crypto.SHA256.Equiv`).

Test vectors (FIPS 180-4 Appendix B and NIST CAVP) are the public theorems
`Silmaril.Crypto.SHA256.digest_abc`, `digest_empty`, `digest_448`, `digest_896`,
`digest_cavp_440`.
-/

@[expose] public section

namespace Silmaril.Crypto

/-- SHA-256 (FIPS 180-4 §6.2): Silmaril's reference digest, which is silmaril-lean's. -/
abbrev sha256 (msg : List UInt8) : List UInt8 := Silmaril.Crypto.SHA256.digest msg

theorem sha256_eq_silmaril : sha256 = Silmaril.Crypto.SHA256.digest := rfl

theorem sha256_length (msg : List UInt8) : (sha256 msg).length = 32 :=
  Silmaril.Crypto.SHA256.digest_length msg

end Silmaril.Crypto
