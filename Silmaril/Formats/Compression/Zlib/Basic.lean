module

public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Formats.Compression.Deflate.Stored

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# zlib format (RFC 1950)

A zlib stream is

```
CMF  = CINFO (4 bits) ∣ CM (4 bits, 8 = deflate)
FLG  = FLEVEL (2) ∣ FDICT (1) ∣ FCHECK (5), with (CMF·256 + FLG) ≡ 0 (mod 31)
[DICTID (4 bytes), only when FDICT = 1]
<DEFLATE stream>
ADLER32 (4 bytes, big-endian) of the uncompressed data
```

`zlibCheckHeader` accepts every CMF with CM = 8 and CINFO ≤ 7 (RFC 1950 §2.2 —
`0x08` … `0x78`, i.e. window sizes 256 B … 32 KiB), not just `0x78`: a stream
produced with `deflateInit2(…, windowBits = 9 … 14)` is legal and must decode.
Preset dictionaries (FDICT = 1) are rejected rather than mis-parsed, which is
the honest answer to RFC 1950 §2.3's `Z_NEED_DICT`.

`zlibDecompress` verifies the Adler-32 trailer and rejects a stream whose
trailer does not match the decoded data.

`zlibCompress` writes *stored* DEFLATE blocks: correct and linear-time, but it
does not shrink anything. `zlibDecompress` accepts stored, fixed-Huffman and
dynamic-Huffman DEFLATE blocks.
-/

open Deflate (storedBytes compressStored deflateTake)

/-- Header we emit: CMF = 0x78 (deflate, 32 KiB window), FLG = 0x01
(FLEVEL = 0 "fastest", no preset dictionary, FCHECK making 0x7801 ≡ 0 mod 31). -/
def zlibHeader : List UInt8 := [0x78, 0x01]

/-- zlib trailer: Adler-32 checksum (4 bytes, big-endian). -/
def zlibTrailer (data : ByteArray) : ByteArray :=
  ByteArray.mk (be32Bytes (adler32 data).toNat).toArray

/-- Wrap `data` in a zlib stream. The DEFLATE payload is a sequence of stored
blocks, so the output is slightly *larger* than the input. -/
def zlibCompress (data : ByteArray) : ByteArray :=
  ByteArray.mk zlibHeader.toArray ++ compressStored data ++ zlibTrailer data

/-- Check a zlib header (RFC 1950 §2.2): CM = 8, CINFO ≤ 7, the mod-31 check on
CMF·256 + FLG, and FDICT = 0 (a preset dictionary is not supported). Returns the
bytes after the header. -/
def zlibCheckHeader (bytes : List UInt8) : Option (List UInt8) :=
  match bytes with
  | cmf :: flg :: rest =>
    if cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧ (cmf.toNat * 256 + flg.toNat) % 31 = 0 ∧
        flg &&& 0x20 = 0 then
      some rest
    else none
  | _ => none

/-- Decompress a zlib stream, verifying the Adler-32 trailer. The stream must end
exactly at the four checksum bytes; trailing data is rejected. -/
def zlibDecompress (bytes : ByteArray) : Option ByteArray :=
  match zlibCheckHeader bytes.data.toList with
  | none => none
  | some body =>
    match deflateTake body with
    | .error _ => none
    | .ok (data, afterData) =>
      match afterData with
      | [a0, a1, a2, a3] =>
        if be32Val a0 a1 a2 a3 = (adler32 ⟨data.toArray⟩).toNat then some ⟨data.toArray⟩ else none
      | _ => none

/-! ### Round trip and trailer soundness -/

/-- `c` is a zlib encoding of `data` exactly when it decodes to `data`. -/
def ZlibCompresses (data c : ByteArray) : Prop := zlibDecompress c = some data

end Silmaril.Formats.Compression
