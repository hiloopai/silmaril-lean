module

public import Silmaril.Formats.Compression.Defs

/-!
# Zstandard frames (RFC 8878): the uncompressed subset

**Partial.** This topic decodes the *container* of Zstandard (RFC 8878 §3.1) and
the blocks that need no entropy decoding; compressed blocks are rejected. It is
the first milestone of the zstd plan in docs/projects/content-coding.md, not a
zstd decoder: real encoders emit compressed blocks almost always.

* `xxh64 seed bytes`: XXH64 (RFC 8878 §3.1.1, used for `Content_Checksum`), the
  64-bit xxHash, written from its published algorithm over `UInt64`;
* `windowSize`: the `Window_Descriptor` formula of §3.1.1.1.2;
* `parseHeader`: the frame header (§3.1.1.1): `Frame_Header_Descriptor` (reserved
  bit must be 0), `Window_Descriptor` (absent with `Single_Segment_Flag`, where
  `Window_Size = Frame_Content_Size`), `Dictionary_ID` (0, 1, 2 or 4 bytes) and
  `Frame_Content_Size` (0, 1, 2 (+256), 4 or 8 bytes), little-endian;
* `decodeBlocks`: `Raw_Block`s (copied) and `RLE_Block`s (one byte repeated
  `Block_Size` times) up to the block with `Last_Block` set, each at most
  `Block_Maximum_Size = min Window_Size 128 KiB` (§3.1.1.2.4).
  `Compressed_Block` (planned) and the reserved type are rejected;
* `frame maxWindow`: one frame (magic `0xFD2FB528`) or one skippable frame (magic
  `0x184D2A50`–`0x184D2A5F`, §3.1.2, whose content is skipped and yields no
  output) as a framework `Decoder`. A frame is rejected when its `Window_Size`
  exceeds `maxWindow` (RFC 9659: 8 MiB for HTTP), when it names a non-zero
  `Dictionary_ID` (dictionaries are planned), when the decoded size disagrees with
  `Frame_Content_Size`, or when the `Content_Checksum` (the low 32 bits of
  `xxh64 0` of the content, little-endian) is wrong;
* `decode maxWindow`: a stream of one or more frames (`Decoder.members`, §3.1).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd

/-! ## XXH64 -/

namespace Xxh64

def p1 : UInt64 := 0x9E3779B185EBCA87
def p2 : UInt64 := 0xC2B2AE3D27D4EB4F
def p3 : UInt64 := 0x165667B19E3779F9
def p4 : UInt64 := 0x85EBCA77C2B2AE63
def p5 : UInt64 := 0x27D4EB2F165667C5

/-- Rotate left by `r` (`0 < r < 64`). -/
def rotl (x : UInt64) (r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64 - r))

/-- A little-endian integer of a byte string. -/
def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- A little-endian 64-bit lane. -/
def lane (bs : List UInt8) : UInt64 := (leNat bs).toUInt64

def round (acc input : UInt64) : UInt64 := rotl (acc + input * p2) 31 * p1

def mergeRound (acc v : UInt64) : UInt64 := (acc ^^^ round 0 v) * p1 + p4

/-- The four accumulators over whole 32-byte stripes; returns them and the tail. -/
def stripes : Nat → UInt64 × UInt64 × UInt64 × UInt64 → List UInt8 →
    (UInt64 × UInt64 × UInt64 × UInt64) × List UInt8
  | 0, v, bs => (v, bs)
  | fuel + 1, (v1, v2, v3, v4), bs =>
    if 32 ≤ bs.length then
      stripes fuel (round v1 (lane (bs.take 8)), round v2 (lane ((bs.drop 8).take 8)),
        round v3 (lane ((bs.drop 16).take 8)), round v4 (lane ((bs.drop 24).take 8))) (bs.drop 32)
    else ((v1, v2, v3, v4), bs)

/-- The tail: 8-byte lanes, then a 4-byte lane, then single bytes. -/
def tail : Nat → UInt64 → List UInt8 → UInt64
  | 0, acc, _ => acc
  | fuel + 1, acc, bs =>
    if 8 ≤ bs.length then
      tail fuel (rotl (acc ^^^ round 0 (lane (bs.take 8))) 27 * p1 + p4) (bs.drop 8)
    else if 4 ≤ bs.length then
      tail fuel (rotl (acc ^^^ lane (bs.take 4) * p1) 23 * p2 + p3) (bs.drop 4)
    else
      match bs with
      | [] => acc
      | b :: rest => tail fuel (rotl (acc ^^^ b.toUInt64 * p5) 11 * p1) rest

def avalanche (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 33)) * p2
  let h := (h ^^^ (h >>> 29)) * p3
  h ^^^ (h >>> 32)

end Xxh64

open Xxh64 in
/-- **XXH64** of `bytes` with `seed`. -/
def xxh64 (seed : UInt64) (bytes : List UInt8) : UInt64 :=
  let n := bytes.length
  let (acc, rest) :=
    if 32 ≤ n then
      let ((v1, v2, v3, v4), rest) :=
        stripes (n / 32) (seed + p1 + p2, seed + p2, seed, seed - p1) bytes
      let acc := rotl v1 1 + rotl v2 7 + rotl v3 12 + rotl v4 18
      (mergeRound (mergeRound (mergeRound (mergeRound acc v1) v2) v3) v4, rest)
    else (seed + p5, bytes)
  avalanche (tail (rest.length + 1) (acc + n.toUInt64) rest)

/-- The 32-bit `Content_Checksum` of a frame's content: the low 32 bits of
`xxh64 0`, little-endian. -/
def contentChecksum (content : List UInt8) : List UInt8 :=
  let h := (xxh64 0 content).toNat
  [h.toUInt8, (h / 256).toUInt8, (h / 65536).toUInt8, (h / 16777216).toUInt8]

/-! ## Frame header -/

/-- The frame magic number `0xFD2FB528`, little-endian. -/
def magic : List UInt8 := [0x28, 0xB5, 0x2F, 0xFD]

/-- `Window_Size` from a `Window_Descriptor` byte (RFC 8878 §3.1.1.1.2). -/
def windowSize (descriptor : UInt8) : Nat :=
  let base := 2 ^ (10 + descriptor.toNat / 8)
  base + base / 8 * (descriptor.toNat % 8)

/-- The decoded frame header. -/
structure Header where
  windowSize : Nat
  singleSegment : Bool
  checksum : Bool
  dictionaryId : Nat
  contentSize : Option Nat
  deriving DecidableEq, Repr

/-- `DID_Field_Size` from `Dictionary_ID_Flag`. -/
def didFieldSize (flag : Nat) : Nat := [0, 1, 2, 4].getD flag 0

/-- `FCS_Field_Size` from `Frame_Content_Size_Flag` and `Single_Segment_Flag`. -/
def fcsFieldSize (flag : Nat) (single : Bool) : Nat :=
  if flag = 0 then (if single then 1 else 0) else [0, 2, 4, 8].getD flag 0

/-- Parse the frame header after the magic number. -/
def parseHeader : List UInt8 → Option (Header × List UInt8)
  | [] => none
  | fhd :: rest =>
    let d := fhd.toNat
    let single := d / 32 % 2 = 1
    if d / 8 % 2 = 1 then none
    else
      let window? : Option (Option UInt8 × List UInt8) :=
        if single then some (none, rest)
        else match rest with
          | w :: r => some (some w, r)
          | [] => none
      match window? with
      | none => none
      | some (wd, r1) =>
        let didSize := didFieldSize (d % 4)
        let fcsSize := fcsFieldSize (d / 64) single
        if r1.length < didSize + fcsSize then none
        else
          let did := Xxh64.leNat (r1.take didSize)
          let r2 := r1.drop didSize
          let fcsRaw := Xxh64.leNat (r2.take fcsSize)
          let fcs : Option Nat :=
            if fcsSize = 0 then none else if fcsSize = 2 then some (fcsRaw + 256) else some fcsRaw
          let window := match wd with
            | some w => windowSize w
            | none => fcs.getD 0
          some (⟨window, single, d / 4 % 2 = 1, did, fcs⟩, r2.drop fcsSize)

/-! ## Blocks -/

/-- `Block_Maximum_Size`: the smaller of `Window_Size` and 128 KiB. -/
def blockMaximum (h : Header) : Nat := min h.windowSize 131072

/-- Decode `Raw_Block`s and `RLE_Block`s, appending to `acc`, until `Last_Block`.
`fuel` bounds the number of blocks (each has a 3-byte header). -/
def decodeBlocks (maxBlock : Nat) : Nat → List UInt8 → List UInt8 →
    Option (List UInt8 × List UInt8)
  | 0, _, _ => none
  | fuel + 1, b0 :: b1 :: b2 :: rest, acc =>
    let hdr := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat
    let last := hdr % 2 = 1
    let btype := hdr / 2 % 4
    let size := hdr / 8
    if maxBlock < size then none
    else if btype = 0 then
      if rest.length < size then none
      else
        let acc' := acc ++ rest.take size
        if last then some (acc', rest.drop size)
        else decodeBlocks maxBlock fuel (rest.drop size) acc'
    else if btype = 1 then
      match rest with
      | [] => none
      | x :: r =>
        let acc' := acc ++ List.replicate size x
        if last then some (acc', r) else decodeBlocks maxBlock fuel r acc'
    else none
  | _ + 1, _, _ => none

/-! ## Frames -/

/-- One Zstandard frame or skippable frame at the front of the input. -/
def frame (maxWindow : Nat) : Decoder := fun bytes =>
  match bytes with
  | 0x28 :: 0xB5 :: 0x2F :: 0xFD :: rest =>
    match parseHeader rest with
    | none => none
    | some (h, r) =>
      if h.dictionaryId ≠ 0 ∨ maxWindow < h.windowSize then none
      else
        match decodeBlocks (blockMaximum h) (r.length + 1) r [] with
        | none => none
        | some (out, r2) =>
          if h.contentSize.any (· ≠ out.length) then none
          else if h.checksum then
            if contentChecksum out = r2.take 4 ∧ 4 ≤ r2.length then some (out, r2.drop 4)
            else none
          else some (out, r2)
  | m :: 0x2A :: 0x4D :: 0x18 :: s0 :: s1 :: s2 :: s3 :: rest =>
    let n := Xxh64.leNat [s0, s1, s2, s3]
    if m.toNat / 16 = 5 ∧ n ≤ rest.length then some ([], rest.drop n) else none
  | _ => none

/-- A Zstandard stream: one or more frames. -/
def decode (maxWindow : Nat) : List UInt8 → Option (List UInt8) := (frame maxWindow).members

/-- A single-segment frame holding `data` (at most 255 bytes, one-byte
`Frame_Content_Size`) as one raw block, with a content checksum: an encoder for
small inputs, used for tests. -/
def rawFrame (data : List UInt8) : List UInt8 :=
  let n := data.length
  let hdr := 1 + 8 * n
  magic ++ [0x24, n.toUInt8, hdr.toUInt8, (hdr / 256).toUInt8, (hdr / 65536).toUInt8] ++ data ++
    contentChecksum data

end Silmaril.Formats.Compression.Zstd
