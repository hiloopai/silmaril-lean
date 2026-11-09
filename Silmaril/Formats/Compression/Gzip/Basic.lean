module

public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Formats.Compression.Deflate.Stored

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# gzip format (RFC 1952)

A gzip file is a series of members, each of which is

```
ID1 ID2 CM FLG MTIME(4) XFL OS  [FEXTRA] [FNAME] [FCOMMENT] [FHCRC]
<DEFLATE stream>  CRC32(4, LE)  ISIZE(4, LE)
```

`gzipDecompress` accepts every member header RFC 1952 §2.3 allows — all five FLG
bits, with the optional fields they introduce skipped and FHCRC checked — and
rejects a member whose reserved FLG bits are set (§2.3.1.2) or whose CRC-32 or
ISIZE disagrees with the decoded data (§2.3.1). Multiple members are decoded and
concatenated (§2.2); trailing bytes that do not form a member are rejected.

`gzipCompress` writes one member whose DEFLATE stream is made of *stored*
blocks: correct and linear-time, but it does not shrink anything. The decoder
accepts stored, fixed-Huffman and dynamic-Huffman DEFLATE blocks.
-/

open Deflate (storedBytes compressStored deflateTake)

def gzipMagic : List UInt8 := [0x1F, 0x8B]

/-- The member header we emit: magic, CM = 8 (deflate), FLG = 0 (no optional
fields), MTIME = 0 (no time stamp), XFL = 0, OS = 255 (unknown). -/
def gzipHeader : ByteArray :=
  ByteArray.mk (gzipMagic ++ [0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF]).toArray

/-- The member trailer: CRC-32 of the uncompressed data, then its length mod 2^32
(RFC 1952 §2.3.1), both little-endian. -/
def gzipTrailer (data : ByteArray) : ByteArray :=
  ByteArray.mk (le32Bytes (crc32 data).toNat ++ le32Bytes data.size).toArray

/-- Compress `data` into a one-member gzip stream. The DEFLATE payload is a
sequence of stored blocks, so the output is slightly *larger* than the input. -/
def gzipCompress (data : ByteArray) : ByteArray :=
  gzipHeader ++ compressStored data ++ gzipTrailer data

/-! ### Header flags (RFC 1952 §2.3.1.2) -/

def gzipFTEXT : UInt8 := 0x01
def gzipFHCRC : UInt8 := 0x02
def gzipFEXTRA : UInt8 := 0x04
def gzipFNAME : UInt8 := 0x08
def gzipFCOMMENT : UInt8 := 0x10
/-- Bits 5, 6 and 7 of FLG are reserved and must be zero. -/
def gzipFRESERVED : UInt8 := 0xE0

/-- Drop a zero-terminated field, returning what follows the terminating zero. -/
def gzipDropZeroTerminated : List UInt8 → Option (List UInt8)
  | [] => none
  | 0 :: rest => some rest
  | _ :: rest => gzipDropZeroTerminated rest

/-- Drop exactly `n` bytes, failing if there are fewer. -/
def gzipDropExact (n : Nat) (bs : List UInt8) : Option (List UInt8) :=
  if n ≤ bs.length then some (bs.drop n) else none

/-- Skip the optional header fields selected by `flg`: FEXTRA (`XLEN` plus that
many bytes), FNAME and FCOMMENT (zero-terminated strings). FHCRC is handled
separately because checking it needs the header bytes that precede it. -/
def gzipSkipOptional (flg : UInt8) (bs : List UInt8) : Option (List UInt8) :=
  let afterExtra : Option (List UInt8) :=
    if flg &&& gzipFEXTRA ≠ 0 then
      match bs with
      | x0 :: x1 :: r => gzipDropExact (x0.toNat + 256 * x1.toNat) r
      | _ => none
    else some bs
  match afterExtra with
  | none => none
  | some bs1 =>
    match (if flg &&& gzipFNAME ≠ 0 then gzipDropZeroTerminated bs1 else some bs1) with
    | none => none
    | some bs2 => if flg &&& gzipFCOMMENT ≠ 0 then gzipDropZeroTerminated bs2 else some bs2

/-- Skip the whole optional-field section of a member header: FEXTRA, FNAME and
FCOMMENT via `gzipSkipOptional`, then FHCRC, whose CRC16 is checked against the
header bytes that precede it (RFC 1952 §2.3.1.2). `member` is the member from its
first byte, `afterFixed` what follows the fixed 10-byte part. -/
def gzipSkipHeaderFields (flg : UInt8) (member afterFixed : List UInt8) : Option (List UInt8) :=
  match gzipSkipOptional flg afterFixed with
  | none => none
  | some afterOpt =>
    if flg &&& gzipFHCRC ≠ 0 then
      match afterOpt with
      | c0 :: c1 :: r =>
        let headerLen := member.length - afterOpt.length
        let crc16 := crc32List ((member.take headerLen).map (λ b => b.toNat)) % 65536
        if c0.toNat + 256 * c1.toNat = crc16 then some r else none
      | _ => none
    else some afterOpt

/-- Check the 8-byte member trailer against the decoded data (RFC 1952 §2.3.1):
CRC-32 then ISIZE, both little-endian. Returns the bytes after the trailer. -/
def gzipCheckTrailer (data afterData : List UInt8) : Option (List UInt8) :=
  match afterData with
  | c0 :: c1 :: c2 :: c3 :: i0 :: i1 :: i2 :: i3 :: rest =>
    if le32Val c0 c1 c2 c3 = (crc32 ⟨data.toArray⟩).toNat ∧
        le32Val i0 i1 i2 i3 = data.length % 4294967296 then
      some rest
    else none
  | _ => none

/-- Decode one gzip member at the front of `bs`: returns the member's data and
the bytes following the member. Fails unless the magic, CM, reserved FLG bits,
FHCRC (when present), CRC-32 and ISIZE are all as RFC 1952 requires. -/
def gzipMember (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match bs with
  | 0x1F :: 0x8B :: cm :: flg :: _mt0 :: _mt1 :: _mt2 :: _mt3 :: _xfl :: _os :: rest =>
    if cm ≠ 8 ∨ flg &&& gzipFRESERVED ≠ 0 then none
    else
      match gzipSkipHeaderFields flg bs rest with
      | none => none
      | some body =>
        match deflateTake body with
        | .error _ => none
        | .ok (data, afterData) =>
          match gzipCheckTrailer data afterData with
          | none => none
          | some rest' => some (data, rest')
  | _ => none

/-- Decode members until the input runs out, concatenating them (RFC 1952 §2.2).
`fuel` bounds the number of members; every member is at least 18 bytes long, so
the length of the input is more than enough. -/
def gzipMembers : Nat → List UInt8 → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | fuel + 1, bs, acc =>
    match gzipMember bs with
    | none => none
    | some (data, []) => some (acc ++ data)
    | some (data, rest) => gzipMembers fuel rest (acc ++ data)

/-- Decompress a gzip stream: one or more members, every trailer verified. -/
def gzipDecompress (bytes : ByteArray) : Option ByteArray :=
  match gzipMembers (bytes.size + 1) bytes.data.toList [] with
  | none => none
  | some out => some ⟨out.toArray⟩

/-! ### Round trip and multi-member decoding -/

/-- `c` is a gzip encoding of `data` exactly when it decodes to `data`. -/
def GzipCompresses (data c : ByteArray) : Prop := gzipDecompress c = some data

end Silmaril.Formats.Compression
