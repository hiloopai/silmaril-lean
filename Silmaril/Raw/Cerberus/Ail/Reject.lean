module

public import Silmaril.Cerberus.Ail.Codec.Defs
public import Silmaril.Semantics.CPort.Crypto.MD5.Defs

/-! # The frontend's rejects and the input digest

`Reject` is the error of `Frontend.desugar` and `Frontend.typecheck`: Cerberus's
`Errors.error` as the oracle prints it in a `$reject` document, with the stage
(`parse`, `desugar` or `typing`), the location (a `Loc.t`, or the `$loc_regions`
extension of the Silmaril exporter that some typing errors report) and the short message
(`Pp_errors.short_message`).

`fileDigest` is `Cerb_fresh.set_digest`'s `Digest.file`: the MD5 of the bytes of the
input file (the whole `.i`, final newline included). Every symbol the desugaring creates
carries it (`symbol.lem:224-260`). `Silmaril.Crypto.MD5.digest` works on a `List UInt8`
and slices it block by block, which is quadratic; `fileDigest` runs the same
64 steps over the `ByteArray` in machine arithmetic, and the golden check compares it with
Python's `hashlib.md5` on every corpus file.
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail

open Silmaril.Cerberus Silmaril.Crypto

/-- Why Cerberus stopped after parsing: the stage, the location and the short message of
its `Errors.error`. -/
structure Reject where
  stage : String
  loc : Codec.RejectLoc
  message : String

/-- A parse reject, at the Ail levels. -/
def Reject.ofCabs (r : Cabs.Codec.Reject) : Reject := ⟨r.stage, .loc r.loc, r.message⟩

/-- RFC 1321 §3.4: the shift amounts of the 64 steps. -/
def md5Shifts : Array UInt32 :=
  #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- RFC 1321 §3.4: the table `T[i] = ⌊2³² |sin i|⌋`, as `MD5.processBlock` spells it. -/
def md5Table : Array UInt32 :=
  #[0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

abbrev MD5State := UInt32 × UInt32 × UInt32 × UInt32

/-- The little-endian word of `b` at byte `i` (zero past the end). -/
@[inline] def wordLE (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) ||| (b[i + 2]!.toUInt32 <<< 16) |||
    (b[i + 3]!.toUInt32 <<< 24)

/-- RFC 1321 §3.4 on the 64-byte block of `b` at `off`: the 64 steps of `MD5.processBlock`
(`F`, `G`, `H`, `I`, message index `k`, then `a := b + ((a + f + X[k] + T[i]) <<< s)`)
in machine arithmetic. -/
def md5Block (b : ByteArray) (off : Nat) (st : MD5State) : MD5State :=
  let (a0, b0, c0, d0) := st
  let (a, bb, c, d) := (List.range 64).foldl (fun (s : MD5State) i =>
    let (a, b', c, d) := s
    let (f, k) :=
      if i < 16 then ((b' &&& c) ||| (~~~ b' &&& d), i)
      else if i < 32 then ((b' &&& d) ||| (c &&& ~~~ d), (5 * i + 1) % 16)
      else if i < 48 then (b' ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (b' ||| ~~~ d), (7 * i) % 16)
    let x := a + f + md5Table[i]! + wordLE b (off + 4 * k)
    let sh := md5Shifts[i]!
    (d, b' + ((x <<< sh) ||| (x >>> (32 - sh))), b', c)) (a0, b0, c0, d0)
  (a0 + a, b0 + bb, c0 + c, d0 + d)

/-- RFC 1321 §3.1-3.4 over a `ByteArray`: the full blocks in place, then the padded tail
(`0x80`, zeros, the 64-bit little-endian bit length, as `paddingMD_LE`). -/
def md5Words (b : ByteArray) : MD5State :=
  let full := b.size / 64
  let s := (List.range full).foldl (fun s k => md5Block b (64 * k) s) MD5.initial
  let rest := (b.extract (64 * full) b.size).toList
  let lenBits := b.size * 8
  let zeros := (119 - rest.length) % 64
  let tail : ByteArray := ⟨(rest ++ [0x80] ++ List.replicate zeros 0 ++
    (List.range 8).map fun i => UInt8.ofNat (lenBits / 256 ^ i % 256)).toArray⟩
  (List.range (tail.size / 64)).foldl (fun s k => md5Block tail (64 * k) s) s

/-- The MD5 digest of a file's bytes, as Cerberus's symbols carry it. -/
def fileDigest (b : ByteArray) : Digest :=
  let (a, b', c, d) := md5Words b
  let w (x : UInt32) := let (b0, b1, b2, b3) := toBytesLE32 x; [b0, b1, b2, b3]
  ⟨w a ++ w b' ++ w c ++ w d⟩

end Silmaril.Cerberus.Ail
