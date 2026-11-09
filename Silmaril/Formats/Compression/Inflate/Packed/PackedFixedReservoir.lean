module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedLookupSound
public import Silmaril.Formats.Compression.Inflate.Packed.PackedTables
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
public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Formats.Compression.Vectors

/-!
# Fixed packed codes in arbitrary buffered reservoirs

The proofs are kernel-checked finite codebook certificates.
The fixed source tables and the canonical Huffman tables agree for every valid
reservoir with enough already-buffered root bits. High buffered bits, input
bytes and the logical position are arbitrary and are retained in the resulting
canonical-reader normalization. Reserved symbols retain their invalid meaning.

This is a mathematical packed-table refinement. Code-bit refill, dynamic-table
construction, packed memory and execution of C/Core/machine code remain separate.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def fixedLiteralTable : HuffmanTable := Deflate.fixedLitLenTable.getD (HuffmanTable.empty 9)
def fixedDistanceTable : HuffmanTable := Deflate.fixedDistTable.getD (HuffmanTable.empty 5)

def reverseLowBits : Nat → Nat → Nat
  | _, 0 => 0
  | word, count + 1 => word % 2 * 2 ^ count + reverseLowBits (word / 2) count

structure RootCode where
  symbol : Nat
  code : Nat
  length : Nat

def rootEntry (table : Array Entry) (word : Nat) : Entry := (table[word]?).getD default

def literalRootCode (word : Nat) : RootCode :=
  let length := (rootEntry lenfix word).bits.toNat
  let code := reverseLowBits word length
  let symbol := if length = 7 then code + 256
    else if length = 8 then if code < 192 then code - 48 else code + 88
    else code - 256
  ⟨symbol, code, length⟩

def distanceRootCode (word : Nat) : RootCode :=
  let code := reverseLowBits word 5
  ⟨code, code, 5⟩

/-- Finite facts identify the precise canonical code, including reserved
symbols, without quantifying over arbitrary reservoir fields. -/
def RootFacts (kind : Kind) (packed : Array Entry) (canonical : HuffmanTable)
    (interpret : Nat → Meaning) (width word : Nat) (witness : RootCode) : Prop :=
  packed[word]? = some (rootEntry packed word) ∧
    isLink kind (rootEntry packed word) = false ∧
    (rootEntry packed word).bits.toNat = witness.length ∧ witness.length ≤ width ∧
    canonical.encodeSymbol witness.symbol = some (witness.code, witness.length) ∧
    natBits word witness.length = msbBits witness.code witness.length ∧
    meaning kind (rootEntry packed word) = interpret witness.symbol

instance (kind : Kind) (packed : Array Entry) (canonical : HuffmanTable)
    (interpret : Nat → Meaning) (width word : Nat) (witness : RootCode) :
    Decidable (RootFacts kind packed canonical interpret width word witness) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
