module

public import Silmaril.Formats.Compression.Inflate.Stream.Protocol
public import Silmaril.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Formats.Compression.Deflate.Stored
public import Silmaril.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Formats.Compression.Deflate.LZ77
public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Formats.Compression.Gzip.Basic

/-!
# Prefix checksums and the inflater return protocol

The protocol's previously arbitrary `UpdateCheck`
callback is instantiated by actual incremental Adler-32 and CRC-32 folds.
Their append laws prove that committing exactly the produced bytes updates the
checksum of the logical member prefix. CHECK rebases the pending-byte view, so
the following epilogue cannot hash those same bytes again.

The prefix starts at the member's checksum seed. Dictionary-ID validation and
dictionary installation/reset, gzip header CRC, and the relation between actual
produced memory bytes and `pendingOutput` remain separate obligations. Count
coherence is explicit; it is not a pointer or C execution theorem. A committed
`inf_leave` result is a return snapshot whose pending view is initialized anew
on the next source call, rather than a state to commit repeatedly.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.Checksums

open Silmaril.Formats.Compression
open Protocol

def checksum (kind : ChecksumKind) (bytes : List UInt8) : Nat :=
  match kind with
  | .adler32 => adler32OfList (bytes.map UInt8.toNat)
  | .crc32 => crc32List (bytes.map UInt8.toNat)

/-- Packed Adler accumulators are decoded by division/remainder; CRC seeds
are the complemented public checksum, not the internal running register. -/
def update : UpdateCheck
  | .adler32, seed, bytes =>
    let state := adler32Fold (seed % 65536, seed / 65536) (bytes.map UInt8.toNat)
    state.2 * 65536 + state.1
  | .crc32, seed, bytes =>
    (bytes.map UInt8.toNat).foldl crc32Byte (seed ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-- The stored private and public checksums agree with the committed logical
member prefix. Pending bytes are deliberately outside this committed prefix. -/
def PrefixInvariant (fields : ExitFields) (committed : List UInt8) : Prop :=
  fields.check = checksum (checksumKind fields) committed ∧ fields.publicFields.adler = fields.check

end Silmaril.Formats.Compression.Inflate.Stream.Checksums
