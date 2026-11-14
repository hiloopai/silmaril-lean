module

public import Silmaril.Crypto.Interface.Defs
public import Silmaril.Crypto.SHA256
public import Silmaril.Crypto.SHA1.Defs

@[expose] public section

/-!
# Hash functions as `HashFn` instances

The reference digests packaged with their lengths, for generic constructions (HMAC, HKDF):

* `HashFn.sha256`: `Silmaril.Crypto.SHA256.digest`, 32-octet digests and 64-octet blocks
  (FIPS 180-4 §1).

* `HashFn.sha1`: `Silmaril.Crypto.SHA1.digest`, 20-octet digests and 64-octet blocks (used by the
  WebSocket handshake; no security role, see `SHA1.Defs`).

Other digests join here as they arrive (SHA-384/512 as planned in docs/projects/crypto.md).
-/

namespace Silmaril.Crypto

/-- SHA-256 (FIPS 180-4). -/
def HashFn.sha256 : HashFn where
  digestLen := 32
  blockLen := 64
  hash := SHA256.digest
  digest_length := SHA256.digest_length

/-- SHA-1 (FIPS 180-4 §6.1). -/
def HashFn.sha1 : HashFn where
  digestLen := 20
  blockLen := 64
  hash := SHA1.digest
  digest_length _ := rfl

end Silmaril.Crypto
