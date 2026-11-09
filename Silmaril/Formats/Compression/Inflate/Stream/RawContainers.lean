module

public import Silmaril.Formats.Compression.Inflate.Stream.RawRuns
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
# Completed raw controllers and container specifications

These bridges combine an actual completed raw
controller with independent header and trailer observations. They use the
existing zlib and gzip checks, including gzip optional fields and FHCRC.

This is a completion interface, not an incremental wrapper implementation:
header parsing, incremental checksums, DICT, and API return statuses still need
their own execution correspondence. The two version dispatchers are parameters
of the raw execution and share the mathematical container specifications.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawContainers

open Silmaril.Formats.Compression

/-- Complete-header observation, using the existing gzip optional-field and
FHCRC checker. It does not run or assume success of a DEFLATE decoder. -/
def gzipBody (bytes : List UInt8) : Option (List UInt8) :=
  match bytes with
  | 0x1F :: 0x8B :: cm :: flg :: _mt0 :: _mt1 :: _mt2 :: _mt3 :: _xfl :: _os :: rest =>
    if cm ≠ 8 ∨ flg &&& gzipFRESERVED ≠ 0 then none
    else gzipSkipHeaderFields flg bytes rest
  | _ => none

/-! ## Nonvacuity: one stored A, with the trailer supplied only afterward -/

def storedAInput : List UInt8 := [1, 1, 0, 0xfe, 0xff, 65]
def storedACalls : List RawMachine.Call := List.replicate 4 ⟨[], 8, 1⟩
def storedAState : RawState := ⟨⟨0, 0, [], 48⟩, ⟨[65]⟩, [65]⟩

end Silmaril.Formats.Compression.Inflate.Stream.RawContainers
