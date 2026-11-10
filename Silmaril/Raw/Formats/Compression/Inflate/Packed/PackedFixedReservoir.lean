module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedReservoir
public import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedLookupSound
public import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedTables
public import Silmaril.Raw.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Raw.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Gzip.Basic
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamFacts
public import Silmaril.Raw.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Raw.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Raw.Formats.Compression.Vectors

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Packed.PackedFixedReservoir`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The codebook's prefix-free decoding follows the same physical reader
steps as a successful read of the code's bits. Retaining that exact reader
lets normalization compose without reconstructing a reader from its bitlist. -/
theorem decodeAux_eq_readBits_of_codeOK {table : HuffmanTable} {symbol code length : Nat}
    (valid : table.CodeOK symbol code length) :
    ∀ remaining reader value after fuel, remaining ≤ length → remaining + 1 ≤ fuel →
      reader.readBits remaining = some (value, after) →
      natBits value remaining = msbBits code remaining →
      decodeSymbolLSBAux table.entries reader (code >>> remaining) (length - remaining) fuel =
        some (symbol, after) := by
  intro remaining
  induction remaining with
  | zero =>
    intro reader value after fuel _ hf hread _
    obtain ⟨fuel, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at hread
    rcases hread with ⟨rfl, rfl⟩
    simp only [decodeSymbolLSBAux, Nat.shiftRight_zero, Nat.sub_zero, valid.found]
  | succ remaining ih =>
    intro reader value after fuel hle hf hread hbits
    obtain ⟨fuel, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    simp only [LSBReader.readBits] at hread
    cases hb : reader.readBit with
    | none => simp only [hb] at hread; cases hread
    | some pair =>
      rcases pair with ⟨bit, next⟩
      simp only [hb] at hread
      cases ht : next.readBits remaining with
      | none => simp only [ht] at hread; cases hread
      | some pair =>
        rcases pair with ⟨tail, final⟩
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at hread
        rcases hread with ⟨rfl, rfl⟩
        have hlow : natBits ((if bit then 1 else 0) + 2 * tail) (remaining + 1) =
            bit :: natBits tail remaining := by
          cases bit
          · simp [natBits]
          · simp [natBits, show (1 + 2 * tail) / 2 = tail by omega]
        rw [hlow, msbBits, List.cons.injEq] at hbits
        obtain ⟨hbit, htail⟩ := hbits
        have hprefix := valid.prefixFree (length - (remaining + 1)) (by omega)
        rw [show length - (length - (remaining + 1)) = remaining + 1 by omega] at hprefix
        have hcode : (code >>> (remaining + 1)) * 2 + (if bit then 1 else 0) = code >>> remaining := by
          rw [hbit, Nat.shiftRight_succ, Nat.testBit_eq_decide_div_mod_eq,
            ← Nat.shiftRight_eq_div_pow]
          by_cases h : (code >>> remaining) % 2 = 1 <;> simp [h] <;> omega
        simp only [decodeSymbolLSBAux, hprefix, hb, hcode]
        simpa only [show length - (remaining + 1) + 1 = length - remaining by omega] using
          ih next tail final fuel (by omega) (by omega) ht htail

theorem readSymbol_eq_readBits_of_codeOK {table : HuffmanTable} {symbol code length : Nat}
    (valid : table.CodeOK symbol code length) {reader after : LSBReader} {value : Nat}
    (hread : reader.readBits length = some (value, after))
    (hbits : natBits value length = msbBits code length) :
    table.readSymbolLSB reader = some (symbol, after) := by
  have h := decodeAux_eq_readBits_of_codeOK valid length reader value after (table.maxBits + 1)
    (Nat.le_refl _) (by have := valid.le; omega) hread hbits
  have hz : code >>> length = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt valid.lt
  simpa only [HuffmanTable.readSymbolLSB, hz, Nat.sub_self] using h

theorem fixedLiteralTable_present : Deflate.fixedLitLenTable = some fixedLiteralTable := by rfl
theorem fixedDistanceTable_present : Deflate.fixedDistTable = some fixedDistanceTable := by rfl

theorem fixed_literal_root_facts : ∀ index : Fin 512,
    RootFacts .literalLength lenfix fixedLiteralTable literalLengthMeaning 9 index.val
      (literalRootCode index.val) ∧ (literalRootCode index.val).symbol < 288 := by decide +kernel

theorem fixed_distance_root_facts : ∀ index : Fin 32,
    RootFacts .distance distfix fixedDistanceTable distanceMeaning 5 index.val
      (distanceRootCode index.val) ∧ (distanceRootCode index.val).symbol < 32 := by decide +kernel

theorem fixed_literal_codeOK (witness : RootCode) (hs : witness.symbol < 288)
    (encoded : fixedLiteralTable.encodeSymbol witness.symbol = some (witness.code, witness.length)) :
    fixedLiteralTable.CodeOK witness.symbol witness.code witness.length := by
  have hb : witness.symbol < Deflate.fixedLitLenLengths.length := by
    rw [Deflate.fixedLitLenLengths_length]
    exact hs
  have hp : 0 < Deflate.fixedLitLenLengths[witness.symbol] := by
    rw [Deflate.fixedLitLenLengths_getElem]
    split
    · decide
    · split
      · decide
      · split <;> decide
  obtain ⟨code, length, he, valid⟩ :=
    HuffmanTable.ofLengths_symOK fixedLiteralTable_present hb hp
  rw [encoded, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  exact valid

theorem fixed_distance_codeOK (witness : RootCode) (hs : witness.symbol < 32)
    (encoded : fixedDistanceTable.encodeSymbol witness.symbol = some (witness.code, witness.length)) :
    fixedDistanceTable.CodeOK witness.symbol witness.code witness.length := by
  have hb : witness.symbol < Deflate.fixedDistLengths.length := by
    simpa only [Deflate.fixedDistLengths, List.length_replicate] using hs
  have hp : 0 < Deflate.fixedDistLengths[witness.symbol] := by
    simp only [Deflate.fixedDistLengths, List.getElem_replicate]
    decide
  obtain ⟨code, length, he, valid⟩ :=
    HuffmanTable.ofLengths_symOK fixedDistanceTable_present hb hp
  rw [encoded, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  exact valid

/-- Lift a finite root certificate to an arbitrary reservoir and its canonical
reader. The high accumulator bits and following input are never enumerated. -/
theorem rootFacts_refines (kind : Kind) (packed : Array Entry) (canonical : HuffmanTable)
    (interpret : Nat → Meaning) (width : Nat) (witness : RootCode)
    (state : Reservoir) (reader : LSBReader)
    (facts : RootFacts kind packed canonical interpret width (state.lowBits width) witness)
    (valid : canonical.CodeOK witness.symbol witness.code witness.length)
    (normalizes : Reservoir.Normalizes state reader) (enough : width ≤ state.bits) :
    ∃ after,
      lookup kind packed width state =
        .found (rootEntry packed (state.lowBits width)) (state.dropBits witness.length) witness.length ∧
      canonical.readSymbolLSB reader = some (witness.symbol, after) ∧
      Reservoir.Normalizes (state.dropBits witness.length) after ∧
      meaning kind (rootEntry packed (state.lowBits width)) = interpret witness.symbol := by
  rcases facts with ⟨he, hlink, hlength, hwidth, _, hword, hmeaning⟩
  have hbound : witness.length ≤ state.bits := Nat.le_trans hwidth enough
  have hlookup : lookup kind packed width state =
      .found (rootEntry packed (state.lowBits width)) (state.dropBits witness.length) witness.length := by
    simp only [lookup, he, hlength, hbound, ite_true, hlink, Bool.false_eq_true, ite_false]
  obtain ⟨after, hread, hnorm⟩ := lookup_readBits kind packed width state
    (state.dropBits witness.length) _ witness.length reader normalizes hlookup
  have hprefix : natBits (state.lowBits witness.length) witness.length =
      natBits (state.lowBits width) witness.length := by
    symm
    simp only [Reservoir.lowBits]
    rw [← Reservoir.natBits_mod (state.hold % 2 ^ width) witness.length,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hwidth)]
  exact ⟨after, hlookup, readSymbol_eq_readBits_of_codeOK valid hread (hprefix.trans hword),
    hnorm, hmeaning⟩

/-- Fixed literal/length lookup agrees with the canonical Huffman decoder for
any normalized reservoir with at least nine already-buffered bits, including
the reserved symbols 286/287 and their invalid packed operations. -/
theorem fixed_literal_reservoir (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (enough : 9 ≤ state.bits) :
    let word := state.lowBits 9
    let witness := literalRootCode word
    ∃ after,
      lookup .literalLength lenfix 9 state =
        .found (rootEntry lenfix word) (state.dropBits witness.length) witness.length ∧
      fixedLiteralTable.readSymbolLSB reader = some (witness.symbol, after) ∧
      Reservoir.Normalizes (state.dropBits witness.length) after ∧
      meaning .literalLength (rootEntry lenfix word) = literalLengthMeaning witness.symbol := by
  obtain ⟨facts, bound⟩ := fixed_literal_root_facts ⟨state.lowBits 9, Reservoir.lowBits_lt state 9⟩
  exact rootFacts_refines .literalLength lenfix fixedLiteralTable literalLengthMeaning 9
    (literalRootCode (state.lowBits 9)) state reader facts
    (fixed_literal_codeOK _ bound facts.2.2.2.2.1) normalizes enough

/-- Fixed distance lookup has the same arbitrary-reservoir correspondence;
symbols 30/31 remain invalid operations rather than fabricated distances. -/
theorem fixed_distance_reservoir (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (enough : 5 ≤ state.bits) :
    let word := state.lowBits 5
    let witness := distanceRootCode word
    ∃ after,
      lookup .distance distfix 5 state =
        .found (rootEntry distfix word) (state.dropBits witness.length) witness.length ∧
      fixedDistanceTable.readSymbolLSB reader = some (witness.symbol, after) ∧
      Reservoir.Normalizes (state.dropBits witness.length) after ∧
      meaning .distance (rootEntry distfix word) = distanceMeaning witness.symbol := by
  obtain ⟨facts, bound⟩ := fixed_distance_root_facts ⟨state.lowBits 5, Reservoir.lowBits_lt state 5⟩
  exact rootFacts_refines .distance distfix fixedDistanceTable distanceMeaning 5
    (distanceRootCode (state.lowBits 5)) state reader facts
    (fixed_distance_codeOK _ bound facts.2.2.2.2.1) normalizes enough

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
