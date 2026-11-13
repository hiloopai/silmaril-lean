module

public import Silmaril.Crypto.Padding
public import Silmaril.Crypto.Word

/-!
# MD5 (RFC 1321)

The MD5 message-digest algorithm, byte-oriented: the message API is
`List UInt8`, so only messages whose bit length is a multiple of 8 can be
hashed, whereas RFC 1321 §3.1 admits an arbitrary bit length.

MD5 is **cryptographically broken** (practical collisions); it is here only to
decode legacy formats, never as a security primitive.

References:
- RFC 1321 §3.1 (padding, delegated to `paddingMD_LE`)
- RFC 1321 §3.3 (the four-word initial state)
- RFC 1321 §3.4 (the four rounds)
- RFC 1321 §3.5 (little-endian output)

## Theorems

- `digest_length`: the digest is 16 bytes.
- `parseBlock_length`: a 64-byte block parses to 16 words.
- `digest_rfc1321_1` … `_7`: all seven RFC 1321 Appendix A.5 known answers,
  checked by the Lean kernel.
-/

set_option maxRecDepth 100000

@[expose] public section

open Silmaril.Crypto

namespace Silmaril.Crypto.MD5

/-- §3.4 step 4: Auxiliary functions -/
def md5F (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)
def md5G (x y z : UInt32) : UInt32 := (x &&& z) ^^^ (y &&& (~~~ z))
def md5H (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
def md5I (x y z : UInt32) : UInt32 := y ^^^ (x ||| (~~~ z))

/-- Round step: a = b + ((a + f(b,c,d) + X[k] + T[i]) <<< s) -/
def md5Round (f : UInt32 → UInt32 → UInt32 → UInt32) (a b c d xk s Ti : UInt32) : UInt32 :=
  b + rotl32 (a + f b c d + xk + Ti) s.toNat

/-- Parse a byte list into little-endian 32-bit words, four bytes at a time.
A trailing run of fewer than four bytes is dropped; callers must pass a length
that is a multiple of four (`hash` always passes exactly 64 bytes).  See
`parseBlock_length`. -/
def parseBlock (bs : List UInt8) : List UInt32 :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => ofBytesLE32 b0 b1 b2 b3 :: parseBlock rest
  | _ => []

/-- §3.4: process one 512-bit block through all 64 rounds.

`X` must hold at least 16 words: the lookups below are `getElem!`, which returns
`0` rather than failing on a short array.  `hash` always passes the 16 words
produced by `parseBlock` from a 64-byte block. -/
def processBlock (aa bb cc dd : UInt32) (X : Array UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := aa; let b := bb; let c := cc; let d := dd
  -- Round 1
  let a := md5Round md5F a b c d (X[0]!)  7  0xd76aa478; let d := md5Round md5F d a b c (X[1]!) 12  0xe8c7b756
  let c := md5Round md5F c d a b (X[2]!) 17 0x242070db; let b := md5Round md5F b c d a (X[3]!) 22 0xc1bdceee
  let a := md5Round md5F a b c d (X[4]!)  7  0xf57c0faf; let d := md5Round md5F d a b c (X[5]!) 12  0x4787c62a
  let c := md5Round md5F c d a b (X[6]!) 17 0xa8304613; let b := md5Round md5F b c d a (X[7]!) 22 0xfd469501
  let a := md5Round md5F a b c d (X[8]!)  7  0x698098d8; let d := md5Round md5F d a b c (X[9]!) 12  0x8b44f7af
  let c := md5Round md5F c d a b (X[10]!) 17 0xffff5bb1; let b := md5Round md5F b c d a (X[11]!) 22 0x895cd7be
  let a := md5Round md5F a b c d (X[12]!)  7  0x6b901122; let d := md5Round md5F d a b c (X[13]!) 12 0xfd987193
  let c := md5Round md5F c d a b (X[14]!) 17 0xa679438e; let b := md5Round md5F b c d a (X[15]!) 22 0x49b40821
  -- Round 2
  let a := md5Round md5G a b c d (X[1]!)  5 0xf61e2562; let d := md5Round md5G d a b c (X[6]!)  9  0xc040b340
  let c := md5Round md5G c d a b (X[11]!) 14 0x265e5a51; let b := md5Round md5G b c d a (X[0]!) 20 0xe9b6c7aa
  let a := md5Round md5G a b c d (X[5]!)  5 0xd62f105d; let d := md5Round md5G d a b c (X[10]!) 9  0x02441453
  let c := md5Round md5G c d a b (X[15]!) 14 0xd8a1e681; let b := md5Round md5G b c d a (X[4]!) 20 0xe7d3fbc8
  let a := md5Round md5G a b c d (X[9]!)  5 0x21e1cde6; let d := md5Round md5G d a b c (X[14]!) 9  0xc33707d6
  let c := md5Round md5G c d a b (X[3]!) 14 0xf4d50d87; let b := md5Round md5G b c d a (X[8]!) 20 0x455a14ed
  let a := md5Round md5G a b c d (X[13]!)  5 0xa9e3e905; let d := md5Round md5G d a b c (X[2]!) 9  0xfcefa3f8
  let c := md5Round md5G c d a b (X[7]!) 14 0x676f02d9; let b := md5Round md5G b c d a (X[12]!) 20 0x8d2a4c8a
  -- Round 3
  let a := md5Round md5H a b c d (X[5]!)  4 0xfffa3942; let d := md5Round md5H d a b c (X[8]!) 11 0x8771f681
  let c := md5Round md5H c d a b (X[11]!) 16 0x6d9d6122; let b := md5Round md5H b c d a (X[14]!) 23 0xfde5380c
  let a := md5Round md5H a b c d (X[1]!)  4 0xa4beea44; let d := md5Round md5H d a b c (X[4]!) 11 0x4bdecfa9
  let c := md5Round md5H c d a b (X[7]!) 16 0xf6bb4b60; let b := md5Round md5H b c d a (X[10]!) 23 0xbebfbc70
  let a := md5Round md5H a b c d (X[13]!)  4 0x289b7ec6; let d := md5Round md5H d a b c (X[0]!) 11 0xeaa127fa
  let c := md5Round md5H c d a b (X[3]!) 16 0xd4ef3085; let b := md5Round md5H b c d a (X[6]!) 23 0x04881d05
  let a := md5Round md5H a b c d (X[9]!)  4 0xd9d4d039; let d := md5Round md5H d a b c (X[12]!) 11 0xe6db99e5
  let c := md5Round md5H c d a b (X[15]!) 16 0x1fa27cf8; let b := md5Round md5H b c d a (X[2]!) 23 0xc4ac5665
  -- Round 4
  let a := md5Round md5I a b c d (X[0]!)  6 0xf4292244; let d := md5Round md5I d a b c (X[7]!) 10 0x432aff97
  let c := md5Round md5I c d a b (X[14]!) 15 0xab9423a7; let b := md5Round md5I b c d a (X[5]!) 21 0xfc93a039
  let a := md5Round md5I a b c d (X[12]!)  6 0x655b59c3; let d := md5Round md5I d a b c (X[3]!) 10 0x8f0ccc92
  let c := md5Round md5I c d a b (X[10]!) 15 0xffeff47d; let b := md5Round md5I b c d a (X[1]!) 21 0x85845dd1
  let a := md5Round md5I a b c d (X[8]!)  6 0x6fa87e4f; let d := md5Round md5I d a b c (X[15]!) 10 0xfe2ce6e0
  let c := md5Round md5I c d a b (X[6]!) 15 0xa3014314; let b := md5Round md5I b c d a (X[13]!) 21 0x4e0811a1
  let a := md5Round md5I a b c d (X[4]!)  6 0xf7537e82; let d := md5Round md5I d a b c (X[11]!) 10 0xbd3af235
  let c := md5Round md5I c d a b (X[2]!) 15 0x2ad7d2bb; let b := md5Round md5I b c d a (X[9]!) 21 0xeb86d391
  (aa + a, bb + b, cc + c, dd + d)

/-- §3.3: the MD5 initial state (little-endian word constants). -/
def initial : UInt32 × UInt32 × UInt32 × UInt32 :=
  (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)

/-- MD5 hash of a message as four 32-bit words. -/
def hash (msg : List UInt8) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let padded := paddingMD_LE msg
  let numBlocks := padded.length / 64
  let blocks : List (Array UInt32) := List.ofFn fun (i : Fin numBlocks) =>
    let off := 64 * i.val
    let blk := List.take 64 (List.drop off padded)
    (parseBlock blk).toArray
  let (a, b, c, d) := initial
  blocks.foldl (fun (s : UInt32 × UInt32 × UInt32 × UInt32) blk =>
    let (sa, sb, sc, sd) := s
    processBlock sa sb sc sd blk
  ) (a, b, c, d)

/-- MD5 digest as 16 little-endian bytes. -/
def digest (msg : List UInt8) : List UInt8 :=
  let (a, b, c, d) := hash msg
  let (b0,b1,b2,b3) := toBytesLE32 a
  let (b4,b5,b6,b7) := toBytesLE32 b
  let (b8,b9,b10,b11) := toBytesLE32 c
  let (b12,b13,b14,b15) := toBytesLE32 d
  [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15]

theorem digest_length (msg : List UInt8) : (digest msg).length = 16 := rfl

/-- `parseBlock` consumes whole 4-byte groups; a 64-byte block yields 16 words. -/
theorem parseBlock_length (bs : List UInt8) : (parseBlock bs).length = bs.length / 4 := by
  fun_induction parseBlock bs
  case case1 ih =>
    simp only [List.length_cons]
    omega
  case case2 t hcon =>
    rcases t with _ | ⟨b0, t⟩
    · simp
    rcases t with _ | ⟨b1, t⟩
    · simp
    rcases t with _ | ⟨b2, t⟩
    · simp
    rcases t with _ | ⟨b3, t⟩
    · simp
    exact absurd rfl (hcon b0 b1 b2 b3 t)

/-! ### Known-answer theorems

These pin all 64 round constants, the four shift tables, the X-index
permutation, the initial state and the little-endian output order to RFC 1321.
They are discharged by the Lean kernel, without compiled evaluation.
-/

/-- RFC 1321 Appendix A.5: MD5 of the empty string. -/
theorem digest_rfc1321_1 :
    digest [] =
    [0xd4, 0x1d, 0x8c, 0xd9, 0x8f, 0x00, 0xb2, 0x04, 0xe9, 0x80, 0x09, 0x98,
      0xec, 0xf8, 0x42, 0x7e] := by
  decide +kernel

/-- RFC 1321 Appendix A.5: MD5 of "a". -/
theorem digest_rfc1321_2 :
    digest [0x61] =
    [0x0c, 0xc1, 0x75, 0xb9, 0xc0, 0xf1, 0xb6, 0xa8, 0x31, 0xc3, 0x99, 0xe2,
      0x69, 0x77, 0x26, 0x61] := by
  decide +kernel

/-- RFC 1321 Appendix A.5: MD5 of "abc". -/
theorem digest_rfc1321_3 :
    digest [0x61, 0x62, 0x63] =
    [0x90, 0x01, 0x50, 0x98, 0x3c, 0xd2, 0x4f, 0xb0, 0xd6, 0x96, 0x3f, 0x7d,
      0x28, 0xe1, 0x7f, 0x72] := by
  decide +kernel

/-- RFC 1321 Appendix A.5: MD5 of "message digest". -/
theorem digest_rfc1321_4 :
    digest [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x20, 0x64, 0x69, 0x67, 0x65,
      0x73, 0x74] =
    [0xf9, 0x6b, 0x69, 0x7d, 0x7c, 0xb7, 0x93, 0x8d, 0x52, 0x5a, 0x2f, 0x31,
      0xaa, 0xf1, 0x61, 0xd0] := by
  decide +kernel

/-- RFC 1321 Appendix A.5: MD5 of the lowercase alphabet. -/
theorem digest_rfc1321_5 :
    digest [0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c,
      0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,
      0x79, 0x7a] =
    [0xc3, 0xfc, 0xd3, 0xd7, 0x61, 0x92, 0xe4, 0x00, 0x7d, 0xfb, 0x49, 0x6c,
      0xca, 0x67, 0xe1, 0x3b] := by
  decide +kernel

/-- RFC 1321 Appendix A.5: MD5 of the 62-character alphanumeric string (two blocks). -/
theorem digest_rfc1321_6 :
    digest [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c,
      0x4d, 0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,
      0x59, 0x5a, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a,
      0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76,
      0x77, 0x78, 0x79, 0x7a, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
      0x38, 0x39] =
    [0xd1, 0x74, 0xab, 0x98, 0xd2, 0x77, 0xd9, 0xf5, 0xa5, 0x61, 0x1c, 0x2c,
      0x9f, 0x41, 0x9d, 0x9f] := by
  decide +kernel

/-- RFC 1321 Appendix A.5: MD5 of the 80-digit string (two blocks). -/
theorem digest_rfc1321_7 :
    digest [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x31, 0x32,
      0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x31, 0x32, 0x33, 0x34,
      0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,
      0x37, 0x38, 0x39, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,
      0x39, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30,
      0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x31, 0x32,
      0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30] =
    [0x57, 0xed, 0xf4, 0xa2, 0x2b, 0xe3, 0xc9, 0x55, 0xac, 0x49, 0xda, 0x2e,
      0x21, 0x07, 0xb6, 0x7a] := by
  decide +kernel


end Silmaril.Crypto.MD5
