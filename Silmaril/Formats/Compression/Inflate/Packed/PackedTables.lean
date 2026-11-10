module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedData
public import Silmaril.Formats.Compression.Inflate.Manual.Symbols

/-!
# Fixed packed-table correspondence

The `inffixed.h` entry arrays are extracted from the zlib
source. The packed implementation uses array indices and
operation flags independently of the shared bit-at-a-time canonical decoder.
The finite correspondence covers every fixed literal/length root index and
every fixed distance root index, retaining operation meaning and exact reader
position after code bits. Reserved codes are invalid operations, not links.

This first layer compares all fully buffered root words. The generic lookup
also implements one subtable indirection and extra-bit reads; dynamic table
construction, partial-word/refill invariants, the fast path, and C/Core/x86
refinement remain separate proof obligations.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536

def literalLengthMeaning (symbol : Nat) : Meaning :=
  if symbol < 256 then .literal symbol
  else if symbol = 256 then .endBlock
  else if symbol ≤ 285 then
    .baseExtra (Deflate.lengthBase.getD (symbol - 257) 3)
      (Deflate.lengthExtraBits.getD (symbol - 257) 0)
  else .invalid

def distanceMeaning (symbol : Nat) : Meaning :=
  if symbol < 30 then
    .baseExtra (Deflate.distanceBase.getD symbol 1) (Deflate.distanceExtraBits.getD symbol 0)
  else .invalid

structure CodeObservation where
  meaning : Meaning
  buffer : Nat
  count : Nat
  input : List UInt8
  totalRead : Nat
  deriving Repr, DecidableEq

def observe (value : Meaning) (reader : LSBReader) : CodeObservation :=
  ⟨value, reader.buffer, reader.count, reader.input, reader.totalRead⟩

def rootWord (width word : Nat) : Reservoir := ⟨word, width, [], 0⟩

def packedCodeObservation (kind : Kind) (table : Array Entry) (width word : Nat) :
    Option CodeObservation :=
  match lookup kind table width (rootWord width word) with
  | .found entry rest _ => some (observe (meaning kind entry) rest.normalize)
  | _ => none

def canonicalCodeObservation (table : Option HuffmanTable) (symbolMeaning : Nat → Meaning)
    (width word : Nat) : Option CodeObservation := do
  let table ← table
  let (symbol, rest) ← table.readSymbolLSB (rootWord width word).normalize
  pure (observe (symbolMeaning symbol) rest)

def fastDecode (entries : List CodeEntry) (reader : LSBReader)
    (code length : Nat) : Nat → Option (Nat × LSBReader)
  | 0 => none
  | fuel + 1 =>
    match lookupEntryFast entries code length with
    | some symbol => some (symbol, reader)
    | none =>
      match reader.readBit with
      | none => none
      | some (bit, rest) => fastDecode entries rest (code * 2 + if bit then 1 else 0) (length + 1) fuel

def fastCodeObservation (table : Option HuffmanTable) (symbolMeaning : Nat → Meaning)
    (width word : Nat) : Option CodeObservation := do
  let table ← table
  let (symbol, rest) ← fastDecode table.entries (rootWord width word).normalize 0 0 (table.maxBits + 1)
  pure (observe (symbolMeaning symbol) rest)

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
