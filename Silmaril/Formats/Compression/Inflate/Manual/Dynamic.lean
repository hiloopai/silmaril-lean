module

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

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual

open Silmaril.Formats.Compression

/-!
# A phased mathematical translation of dynamic inflater table construction

A candidate algorithm. This complete-input
model separates TABLE, LENLENS and CODELENS responsibilities: read the counts,
scatter the code-length alphabet, expand repeat codes, then validate/build the
literal/length and distance tables. It uses the shared mathematical Huffman
tables rather than zlib's packed lookup-table representation.

The correspondence theorems compare independently defined phases with the
existing DEFLATE format specification, including every error. They do not
establish C/Ail/Core execution, input-buffer suspension, or `inflate_table`
correctness. Both source versions must separately connect their state and
table representations to these shared phases.
-/

abbrev DynamicResult (α : Type) := Except Deflate.DecompressError α

/-- Validated counts from the three fields at the start of a dynamic block. -/
structure DynamicCounts where
  literals : Nat
  distances : Nat
  codeLengths : Nat
deriving Repr, DecidableEq

/-- TABLE: read HLIT/HDIST/HCLEN and reject unsupported literal/distance counts. -/
def readDynamicCounts (r : LSBReader) : DynamicResult (DynamicCounts × LSBReader) :=
  match r.readBits 5 with
  | none => .error .decodeOverrun
  | some (hlit, r1) =>
    match r1.readBits 5 with
    | none => .error .decodeOverrun
    | some (hdist, r2) =>
      match r2.readBits 4 with
      | none => .error .decodeOverrun
      | some (hclen, r3) =>
        let counts : DynamicCounts := ⟨hlit + 257, hdist + 1, hclen + 4⟩
        if 286 < counts.literals ∨ 30 < counts.distances then .error .badDynamicHuffman
        else .ok (counts, r3)

/-- LENLENS: scatter the three-bit lengths in DEFLATE's permuted alphabet. -/
def scatterCodeLengths : Nat → Nat → List Nat → LSBReader →
    DynamicResult (List Nat × LSBReader)
  | 0, _, lengths, r => .ok (lengths, r)
  | remaining + 1, index, lengths, r =>
    match r.readBits 3 with
    | none => .error .decodeOverrun
    | some (length, next) =>
      let slot := Deflate.codeLengthOrder.getD index 0
      scatterCodeLengths remaining (index + 1) (lengths.set slot length) next

/-- Decode one code-length symbol into the run it appends. A leading repeat
16, unknown symbol or truncated extra-bit field is rejected immediately. -/
def codeLengthRun (previous : List Nat) (symbol : Nat) (r : LSBReader) :
    DynamicResult (List Nat × LSBReader) :=
  if symbol < 16 then .ok ([symbol], r)
  else if symbol = 16 then
    match previous.getLast? with
    | none => .error .badDynamicHuffman
    | some length =>
      match r.readBits 2 with
      | none => .error .decodeOverrun
      | some (extra, next) => .ok (List.replicate (3 + extra) length, next)
  else if symbol = 17 then
    match r.readBits 3 with
    | none => .error .decodeOverrun
    | some (extra, next) => .ok (List.replicate (3 + extra) 0, next)
  else if symbol = 18 then
    match r.readBits 7 with
    | none => .error .decodeOverrun
    | some (extra, next) => .ok (List.replicate (11 + extra) 0, next)
  else .error .badDynamicHuffman

/-- CODELENS: expand the stream into exactly the requested number of lengths.
The explicit fuel matches the specification's bounded complete-input parser. -/
def expandCodeLengths (table : HuffmanTable) (total : Nat) :
    Nat → List Nat → LSBReader → DynamicResult (List Nat × LSBReader)
  | 0, lengths, r =>
    if lengths.length = total then .ok (lengths, r) else .error .badDynamicHuffman
  | fuel + 1, lengths, r =>
    if total ≤ lengths.length then
      if lengths.length = total then .ok (lengths, r) else .error .badDynamicHuffman
    else
      match table.readSymbolLSB r with
      | none => .error .decodeOverrun
      | some (symbol, afterSymbol) =>
        match codeLengthRun lengths symbol afterSymbol with
        | .error error => .error error
        | .ok (run, afterRun) => expandCodeLengths table total fuel (lengths ++ run) afterRun

/-- Require the end-of-block symbol, then validate the expanded literal/distance
lengths and build abstract tables. The empty/one-symbol exceptions are exactly
those of the existing specification. -/
def buildDynamicTables (literalCount : Nat) (lengths : List Nat) (r : LSBReader) :
    DynamicResult (HuffmanTable × HuffmanTable × LSBReader) :=
  let litLens := lengths.take literalCount
  let distLens := lengths.drop literalCount
  if litLens.getD 256 0 = 0 then .error .badDynamicHuffman
  else if !Deflate.validCodeLengths litLens 15 then .error .badDynamicHuffman
  else if !Deflate.validCodeLengths distLens 15 then .error .badDynamicHuffman
  else
    match HuffmanTable.ofLengths litLens 15, HuffmanTable.ofLengths distLens 15 with
    | some literals, some distances => .ok (literals, distances, r)
    | _, _ => .error .badDynamicHuffman

/-- Complete the phases following the already validated TABLE counts. -/
def readDynamicAfterCounts (counts : DynamicCounts) (r : LSBReader) :
    DynamicResult (HuffmanTable × HuffmanTable × LSBReader) :=
  match scatterCodeLengths counts.codeLengths 0 (List.replicate 19 0) r with
  | .error error => .error error
  | .ok (codeLens, r1) =>
    if !isCompleteCode codeLens 7 then .error .badDynamicHuffman
    else
      match HuffmanTable.ofLengths codeLens 7 with
      | none => .error .badDynamicHuffman
      | some codeTable =>
        let total := counts.literals + counts.distances
        match expandCodeLengths codeTable total (total + 1) [] r1 with
        | .error error => .error error
        | .ok (lengths, r2) => buildDynamicTables counts.literals lengths r2

/-- Complete-input candidate for TABLE/LENLENS/CODELENS, factored into the
independent count/scatter/expansion/construction phases above. -/
def readDynamicTables (r : LSBReader) :
    DynamicResult (HuffmanTable × HuffmanTable × LSBReader) :=
  match readDynamicCounts r with
  | .error error => .error error
  | .ok (counts, afterCounts) => readDynamicAfterCounts counts afterCounts

end Silmaril.Formats.Compression.Inflate.Manual
