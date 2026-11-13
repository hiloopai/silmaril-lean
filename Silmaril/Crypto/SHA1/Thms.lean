module

public import Silmaril.Crypto.SHA1.Defs

/-!
# SHA-1: theorems and test vectors

PROVED:

* `digest_length`: the digest is 20 octets.
* `hash_block_length`: every block that `hash` cuts out of the padded message is the
  sixteen-word block §5.2.1 requires (through `paddingMD_block_multiple`, shared with SHA-256).

CHECKED by the kernel (`decide +kernel`), against published values, not values read back from
this implementation:

* FIPS 180-4 examples / NIST CAVP: `SHA1("abc")`, `SHA1("")` and the 448-bit message
  `abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq` (two padded blocks);
* RFC 6455 §1.3: the SHA-1 of the example key concatenated with the WebSocket GUID.

No security property of SHA-1 is stated (see `SHA1.Defs`).
-/

@[expose] public section

namespace Silmaril.Crypto.SHA1

/-- The octets of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

theorem digest_length (msg : List UInt8) : (digest msg).length = 20 := rfl

theorem parseBlock_length : ∀ l : List UInt8, (parseBlock l).length = l.length / 4
  | [] | [_] | [_, _] | [_, _, _] => by simp [parseBlock]
  | _ :: _ :: _ :: _ :: rest => by
    simp only [parseBlock, List.length_cons, parseBlock_length rest]
    omega

theorem hash_block_length (msg : List UInt8) (i : Nat)
    (hi : i < (paddingMD msg).length / 64) :
    (parseBlock (((paddingMD msg).drop (64 * i)).take 64)).length = 16 := by
  obtain ⟨k, hk⟩ := paddingMD_block_multiple msg
  rw [hk] at hi
  rw [parseBlock_length, List.length_take, List.length_drop, hk]
  omega

/-- FIPS 180-4 example: `SHA1("abc")`. -/
theorem digest_abc :
    digest (ascii "abc") =
      [0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a, 0xba, 0x3e,
       0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c, 0x9c, 0xd0, 0xd8, 0x9d] := by
  decide +kernel

/-- NIST CAVP `SHA1ShortMsg.rsp`, `Len = 0`: `SHA1("")`. -/
theorem digest_empty :
    digest [] =
      [0xda, 0x39, 0xa3, 0xee, 0x5e, 0x6b, 0x4b, 0x0d, 0x32, 0x55,
       0xbf, 0xef, 0x95, 0x60, 0x18, 0x90, 0xaf, 0xd8, 0x07, 0x09] := by
  decide +kernel

/-- FIPS 180-4 example: the 448-bit message, which pads to two blocks. -/
theorem digest_448 :
    digest (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      [0x84, 0x98, 0x3e, 0x44, 0x1c, 0x3b, 0xd2, 0x6e, 0xba, 0xae,
       0x4a, 0xa1, 0xf9, 0x51, 0x29, 0xe5, 0xe5, 0x46, 0x70, 0xf1] := by
  decide +kernel

/-- RFC 6455 §1.3: "the SHA-1 hash … of this string is 0xb3 0x7a 0x4f 0x2c 0xc0 0x62 0x4f 0x16
0x90 0xf6 0x46 0x06 0xcf 0x38 0x59 0x45 0xb2 0xbe 0xc4 0xea". -/
theorem digest_rfc6455 :
    digest (ascii "dGhlIHNhbXBsZSBub25jZQ==258EAFA5-E914-47DA-95CA-C5AB0DC85B11") =
      [0xb3, 0x7a, 0x4f, 0x2c, 0xc0, 0x62, 0x4f, 0x16, 0x90, 0xf6,
       0x46, 0x06, 0xcf, 0x38, 0x59, 0x45, 0xb2, 0xbe, 0xc4, 0xea] := by
  decide +kernel

end Silmaril.Crypto.SHA1
