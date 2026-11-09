module

public import Silmaril.Formats.Compression.Inflate.Stream.Parser
public import Silmaril.Formats.Compression.Inflate.Manual.Symbols
public import Silmaril.Formats.Compression.Inflate.Manual.Dynamic
public import Silmaril.Formats.Compression.Inflate.Manual.Stored

/-!
# Resumable DEFLATE parsing phases

These are explicit read/align programs, rather than
calls to the complete-input decoders. Their reservoir interpreter retains the
program continuation and partially refilled accumulator when input runs out.
The theorems below connect their canonical-reader interpretations to the
previously proved mathematical phases, including every error and reader field.

The Huffman implementation here walks codes one bit at a time. It deliberately
does not claim the concrete prefetch/cursor behavior of zlib's packed table
lookup or fast path. Parser continuations are a compositional intermediate
representation; a source state-machine correspondence remains a separate proof.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.ParserPhases

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate

abbrev P := Parser

/-- Bounded Huffman walk. Prefix and length survive input suspension. -/
def huffmanAux (entries : List CodeEntry) (code length : Nat) : Nat → P Nat
  | 0 => .fail .decodeOverrun
  | fuel + 1 =>
    match lookupEntry entries code length with
    | some symbol => .pure symbol
    | none => .bits 1 .decodeOverrun fun bit =>
      huffmanAux entries (code * 2 + bit) (length + 1) fuel

def huffman (table : HuffmanTable) : P Nat :=
  huffmanAux table.entries 0 0 (table.maxBits + 1)

def matchToken (dist : HuffmanTable) (symbol : Nat) : P Manual.Token :=
  .bits (Deflate.lengthExtraBits.getD (symbol - 257) 0) .decodeOverrun fun extra =>
    (huffman dist).bind fun distanceSymbol =>
      if 30 ≤ distanceSymbol then .fail (.badDistanceCode distanceSymbol)
      else .bits (Deflate.distanceExtraBits.getD distanceSymbol 0) .decodeOverrun fun de =>
        .pure (.matchBytes (Deflate.lengthBase.getD (symbol - 257) 3 + extra)
          (Deflate.distanceBase.getD distanceSymbol 1 + de))

def token (litLen dist : HuffmanTable) : P Manual.Token :=
  (huffman litLen).bind fun symbol =>
    if symbol < 256 then .pure (.literal (UInt8.ofNat symbol))
    else if symbol = 256 then .pure .endBlock
    else if symbol ≤ 285 then matchToken dist symbol
    else .fail .decodeOverrun

/-- STORED header, with both partial 16-bit fields retained by the interpreter. -/
def storedHeader : P Nat :=
  .align (.bits 16 .badStoredLen fun len =>
    .bits 16 .badStoredLen fun nlen =>
      if len = nlen ^^^ 65535 then .pure len else .fail .badStoredLen)

def storedBytes : Nat → List UInt8 → P (List UInt8)
  | 0, output => .pure output
  | count + 1, output => .bits 8 .decodeOverrun fun byte =>
    storedBytes count (output ++ [UInt8.ofNat byte])

def stored : P (List UInt8) :=
  storedHeader.bind fun count => storedBytes count []

def counts : P Manual.DynamicCounts :=
  .bits 5 .decodeOverrun fun hlit =>
    .bits 5 .decodeOverrun fun hdist =>
      .bits 4 .decodeOverrun fun hclen =>
        let c : Manual.DynamicCounts := ⟨hlit + 257, hdist + 1, hclen + 4⟩
        if 286 < c.literals ∨ 30 < c.distances then .fail .badDynamicHuffman
        else .pure c

def scatter : Nat → Nat → List Nat → P (List Nat)
  | 0, _, lengths => .pure lengths
  | remaining + 1, index, lengths => .bits 3 .decodeOverrun fun length =>
    scatter remaining (index + 1) (lengths.set (Deflate.codeLengthOrder.getD index 0) length)

def lengthRun (previous : List Nat) (symbol : Nat) : P (List Nat) :=
  if symbol < 16 then .pure [symbol]
  else if symbol = 16 then
    match previous.getLast? with
    | none => .fail .badDynamicHuffman
    | some length => .bits 2 .decodeOverrun fun extra => .pure (List.replicate (3 + extra) length)
  else if symbol = 17 then
    .bits 3 .decodeOverrun fun extra => .pure (List.replicate (3 + extra) 0)
  else if symbol = 18 then
    .bits 7 .decodeOverrun fun extra => .pure (List.replicate (11 + extra) 0)
  else .fail .badDynamicHuffman

def expand (table : HuffmanTable) (total : Nat) : Nat → List Nat → P (List Nat)
  | 0, lengths =>
    if lengths.length = total then .pure lengths else .fail .badDynamicHuffman
  | fuel + 1, lengths =>
    if total ≤ lengths.length then
      if lengths.length = total then .pure lengths else .fail .badDynamicHuffman
    else (huffman table).bind fun symbol =>
      (lengthRun lengths symbol).bind fun run => expand table total fuel (lengths ++ run)

def build (literalCount : Nat) (lengths : List Nat) : P (HuffmanTable × HuffmanTable) :=
  let litLens := lengths.take literalCount
  let distLens := lengths.drop literalCount
  if litLens.getD 256 0 = 0 then .fail .badDynamicHuffman
  else if !Deflate.validCodeLengths litLens 15 then .fail .badDynamicHuffman
  else if !Deflate.validCodeLengths distLens 15 then .fail .badDynamicHuffman
  else
    match HuffmanTable.ofLengths litLens 15, HuffmanTable.ofLengths distLens 15 with
    | some literals, some distances => .pure (literals, distances)
    | _, _ => .fail .badDynamicHuffman

def afterCounts (c : Manual.DynamicCounts) : P (HuffmanTable × HuffmanTable) :=
  (scatter c.codeLengths 0 (List.replicate 19 0)).bind fun codeLens =>
    if !isCompleteCode codeLens 7 then .fail .badDynamicHuffman
    else
      match HuffmanTable.ofLengths codeLens 7 with
      | none => .fail .badDynamicHuffman
      | some codeTable =>
        let total := c.literals + c.distances
        (expand codeTable total (total + 1) []).bind fun lengths => build c.literals lengths

def dynamicTables : P (HuffmanTable × HuffmanTable) :=
  counts.bind afterCounts

/-- The symbol loop has explicit semantic fuel, independent of how input is
offered to the streaming interpreter. Output-buffer handling is factored into
`TokenOutput`; this view returns the logical output at the block boundary. -/
def symbols (litLen dist : HuffmanTable) : Nat → List UInt8 → P (List UInt8)
  | 0, _ => .fail .decodeOverrun
  | fuel + 1, output =>
    (token litLen dist).bind fun parsed =>
      match parsed with
      | .literal byte => symbols litLen dist fuel (output ++ [byte])
      | .endBlock => .pure output
      | .matchBytes length distance =>
        if distance > output.length then .fail .decodeOverrun
        else symbols litLen dist fuel (Deflate.copyBack distance output length)

/-- Adapt the specification's optional symbol read to explicit parse errors. -/
def symbolResult (result : Option (Nat × LSBReader)) :
    Except Deflate.DecompressError (Nat × LSBReader) :=
  match result with
  | none => .error .decodeOverrun
  | some pair => .ok pair

end Silmaril.Formats.Compression.Inflate.Stream.ParserPhases
