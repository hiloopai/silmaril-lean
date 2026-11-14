module

public import Silmaril.Crypto.Padding
public import Silmaril.Crypto.Word

/-!
# SHA-1 (FIPS 180-4 §6.1)

A list-based reference for SHA-1, sharing the Merkle–Damgård padding (`paddingMD`, §5.1.1)
and the word helpers (`ofBytesBE32`, `toBytesBE32`, `rotl32`) with SHA-256
(`Silmaril.Crypto.SHA256`):

* §4.1.1 functions `Ch`, `Parity`, `Maj` and the constants `K` (§4.2.1);
* §6.1.2 message schedule `W 0 … W 79` and the eighty rounds;
* §5.3.1 initial hash value, §6.1.2 multi-block iteration and the 20-octet digest.

**Status and security.** SHA-1 is implemented here because RFC 6455 §4.2.2 uses it to compute
`Sec-WebSocket-Accept` (`Silmaril.Net.WebSocket.Handshake`), where it serves no security
purpose: the accept value only shows that the server read the handshake. SHA-1 is **not**
collision resistant (practical chosen-prefix collisions are known), NIST SP 800-131A Rev. 2
disallows it for digital signature generation, and RFC 9155 deprecates it in TLS 1.2
signatures. Nothing in this module states or assumes a security property of SHA-1.

Checked (`decide +kernel`, `Silmaril.Crypto.SHA1.Thms`): FIPS 180-4 / NIST CAVP vectors and the
RFC 6455 handshake example.
-/

@[expose] public section

namespace Silmaril.Crypto.SHA1

/-- The working variables `a`–`e` (§6.1.2). -/
abbrev State := UInt32 × UInt32 × UInt32 × UInt32 × UInt32

/-! ### Functions and constants (§4.1.1, §4.2.1) -/

def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)
def Parity (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `f t` (§4.1.1). -/
def f (t : Nat) (x y z : UInt32) : UInt32 :=
  if t < 20 then Ch x y z else if t < 40 then Parity x y z
  else if t < 60 then Maj x y z else Parity x y z

/-- `K t` (§4.2.1). -/
def K (t : Nat) : UInt32 :=
  if t < 20 then 0x5a827999 else if t < 40 then 0x6ed9eba1
  else if t < 60 then 0x8f1bbcdc else 0xca62c1d6

/-- The initial hash value (§5.3.1). -/
def H0 : State := (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0)

/-! ### Message schedule (§6.1.2 step 1) -/

/-- The sixteen words of a block, big-endian (§5.2.1). -/
def parseBlock : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest => ofBytesBE32 b0 b1 b2 b3 :: parseBlock rest
  | _ => []

/-- One word of the recurrence `W t = ROTL¹(W(t-3) ⊕ W(t-8) ⊕ W(t-14) ⊕ W(t-16))`, where
`acc[i]` is `W (t-1-i)`. -/
def nextWord (acc : List UInt32) : UInt32 :=
  rotl32 (acc.getD 2 0 ^^^ acc.getD 7 0 ^^^ acc.getD 13 0 ^^^ acc.getD 15 0) 1

/-- Extend a reversed schedule by `n` words. -/
def expand : Nat → List UInt32 → List UInt32
  | 0, acc => acc
  | n + 1, acc => expand n (nextWord acc :: acc)

/-- `W 0 … W 79` for a block of sixteen words (shorter blocks are zero-extended). -/
def schedule (M : List UInt32) : List UInt32 :=
  (expand 64 ((M ++ List.replicate 16 0).take 16).reverse).reverse

/-! ### Compression (§6.1.2 steps 2–4) -/

/-- Round `t` with schedule word `w`. -/
def round (st : State) (tw : Nat × UInt32) : State :=
  let (t, w) := tw
  let (a, b, c, d, e) := st
  let T := rotl32 a 5 + f t b c d + e + K t + w
  (T, a, rotl32 b 30, c, d)

/-- Compress one block into the hash state. -/
def processBlock (st : State) (block : List UInt32) : State :=
  let (a', b', c', d', e') := ((List.range 80).zip (schedule block)).foldl round st
  let (a, b, c, d, e) := st
  (a' + a, b' + b, c' + c, d' + d, e' + e)

/-- The hash state after every block of the padded message (§6.1.2). -/
def hash (msg : List UInt8) : State :=
  let padded := paddingMD msg
  (List.range (padded.length / 64)).foldl
    (fun st i => processBlock st (parseBlock ((padded.drop (64 * i)).take 64))) H0

/-- The four octets of a word, big-endian. -/
def wordBytes (x : UInt32) : List UInt8 :=
  let (b0, b1, b2, b3) := toBytesBE32 x
  [b0, b1, b2, b3]

/-- SHA-1 (FIPS 180-4 §6.1): the 160-bit digest as 20 octets. -/
def digest (msg : List UInt8) : List UInt8 :=
  let (h0, h1, h2, h3, h4) := hash msg
  wordBytes h0 ++ wordBytes h1 ++ wordBytes h2 ++ wordBytes h3 ++ wordBytes h4

end Silmaril.Crypto.SHA1

namespace Silmaril.Crypto

/-- SHA-1 (FIPS 180-4 §6.1). -/
abbrev sha1 (msg : List UInt8) : List UInt8 := SHA1.digest msg

end Silmaril.Crypto
