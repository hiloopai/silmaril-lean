module

public import Silmaril.Formats.Compression.Inflate.Stream.Parser
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
# Resumable container byte fields

Finite byte reads and container field checks are
programs in the existing resumable `Parser` language. A rejected field returns
`none`, whereas truncated input uses the parser's EOF marker; its reservoir
interpreter suspends before that marker can be observed. The canonical
observations below agree with the shared mathematical container specifications,
including their untouched suffix. These are parser-model correspondences, not
C, Core or machine-code execution theorems. Preset dictionaries are excluded by
the existing dictionary-free zlib specification.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.ContainerFields

open Silmaril.Formats.Compression

/-- Canonical byte boundary, retaining the logical consumed-bit counter. -/
def alignedReader (input : List UInt8) (totalRead : Nat := 0) : LSBReader :=
  ⟨0, 0, input, totalRead⟩

/-- One byte; parser suspension preserves partial physical refill. -/
def byte : Parser UInt8 :=
  .bits 8 .decodeOverrun fun value => .pure (UInt8.ofNat value)

/-- A fixed number of bytes. `count` describes the field, not an input budget. -/
def bytes : Nat → Parser (List UInt8)
  | 0 => .pure []
  | count + 1 => byte.bind fun first =>
    (bytes count).bind fun rest => .pure (first :: rest)

/-- Read four bytes and interpret them with a byte-field constructor. -/
def quad {α : Type} (field : UInt8 → UInt8 → UInt8 → UInt8 → α) : Parser α :=
  byte.bind fun b0 => byte.bind fun b1 => byte.bind fun b2 => byte.bind fun b3 =>
    .pure (field b0 b1 b2 b3)

def be32 : Parser Nat := quad be32Val
def le32 : Parser Nat := quad le32Val

/-- Dictionary-free RFC 1950 header, with the same predicate as the shared
specification. Semantic rejection is a value rather than a raw-DEFLATE error. -/
def zlibHeader : Parser (Option Unit) :=
  byte.bind fun cmf => byte.bind fun flg =>
    .pure (if cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧
      (cmf.toNat * 256 + flg.toNat) % 31 = 0 ∧ flg &&& 0x20 = 0
      then some () else none)

def zlibTrailerValue (check : Nat) : Parser (Option Unit) :=
  be32.bind fun value =>
    .pure (if value = check then some () else none)

def gzipTrailerValue (check size : Nat) : Parser (Option Unit) :=
  le32.bind fun checksum => le32.bind fun isize =>
    .pure (if checksum = check ∧ isize = size % 4294967296 then some () else none)

def zlibTrailer (data : List UInt8) : Parser (Option Unit) :=
  zlibTrailerValue (adler32 ⟨data.toArray⟩).toNat

def gzipTrailer (data : List UInt8) : Parser (Option Unit) :=
  gzipTrailerValue (crc32 ⟨data.toArray⟩).toNat data.length

/-- Keep the exact reader only on successful validation. Both an incomplete
canonical input and a rejected field have the shared checker's `none` view. -/
def validationReader : Except Deflate.DecompressError (Option Unit × LSBReader) →
    Option LSBReader
  | .ok (some (), reader) => some reader
  | .ok (none, _) | .error _ => none

def observeValidation (result : Except Deflate.DecompressError (Option Unit × LSBReader)) :
    Option (List UInt8) :=
  (validationReader result).map LSBReader.input

end Silmaril.Formats.Compression.Inflate.Stream.ContainerFields
