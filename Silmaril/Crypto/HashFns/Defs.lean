module

public import Silmaril.Crypto.Interface.Defs
public import Silmaril.Crypto.SHA256

@[expose] public section

/-!
# Hash functions as `HashFn` instances

The reference digests packaged with their lengths, for generic constructions (HMAC, HKDF):

* `HashFn.sha256`: `Silmaril.Crypto.SHA256.digest`, 32-octet digests and 64-octet blocks
  (FIPS 180-4 §1).

Other digests join here as they arrive (SHA-1 with the WebSocket work, SHA-384/512 as planned in
docs/projects/crypto.md).
-/

namespace Silmaril.Crypto

/-- SHA-256 (FIPS 180-4). -/
def HashFn.sha256 : HashFn where
  digestLen := 32
  blockLen := 64
  hash := SHA256.digest
  digest_length := SHA256.digest_length

end Silmaril.Crypto
