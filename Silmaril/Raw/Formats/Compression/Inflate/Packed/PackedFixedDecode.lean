module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedDecode
public import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedFixedReservoir

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Packed.PackedFixedDecode`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Compose a source root-code edge with its canonical operation and actual
extra-bit read. This total correspondence needs no assumed successful result. -/
theorem root_decode_buffered_refines (kind : Kind) (packed : Array Entry)
    (canonical : HuffmanTable) (interpret : Nat → Meaning) (width symbol codeBits : Nat)
    (entry : Entry) (state : Reservoir) (reader codeReader : LSBReader)
    (hlookup : lookup kind packed width state =
      .found entry (state.dropBits codeBits) codeBits)
    (hcanonical : canonical.readSymbolLSB reader = some (symbol, codeReader))
    (normalizes : Reservoir.Normalizes (state.dropBits codeBits) codeReader)
    (hmeaning : meaning kind entry = interpret symbol)
    (buffered : codeBits + extraWidth (interpret symbol) ≤ state.bits) :
    DecodeCorrespondence state (canonicalOperation canonical interpret reader)
      (decode kind packed width state) := by
  cases selected : interpret symbol with
  | literal value =>
    simp only [decode, hlookup, hmeaning, selected, DecodeCorrespondence,
      canonicalOperation, hcanonical, finishMeaning, Nat.add_zero]
    exact ⟨codeReader, rfl, normalizes, trivial⟩
  | endBlock =>
    simp only [decode, hlookup, hmeaning, selected, DecodeCorrespondence,
      canonicalOperation, hcanonical, finishMeaning, Nat.add_zero]
    exact ⟨codeReader, rfl, normalizes, trivial⟩
  | invalid =>
    simp only [decode, hlookup, hmeaning, selected, DecodeCorrespondence,
      canonicalOperation, hcanonical, finishMeaning]
    exact ⟨trivial, trivial, normalizes.1⟩
  | baseExtra base extra =>
    have enough : extra ≤ (state.dropBits codeBits).bits := by
      simp only [selected, extraWidth] at buffered
      change extra ≤ state.bits - codeBits
      omega
    have hread : (state.dropBits codeBits).readBits extra =
        .value ((state.dropBits codeBits).lowBits extra)
          ((state.dropBits codeBits).dropBits extra) := by
      simp only [Reservoir.readBits, Reservoir.needBits_ready enough]
    obtain ⟨after, hextra, hnorm⟩ := normalizes.readBits hread
    simp only [decode, hlookup, hmeaning, selected, hread, DecodeCorrespondence,
      canonicalOperation, hcanonical, finishMeaning, hextra, Option.map_some]
    exact ⟨after, rfl, hnorm, dropBits_add state codeBits extra⟩

theorem fixed_literal_buffer_bound : ∀ index : Fin 512,
    (literalRootCode index.val).length +
      extraWidth (literalLengthMeaning (literalRootCode index.val).symbol) ≤ 13 := by decide +kernel

theorem fixed_distance_buffer_bound : ∀ index : Fin 32,
    (distanceRootCode index.val).length +
      extraWidth (distanceMeaning (distanceRootCode index.val).symbol) ≤ 18 := by decide +kernel

/-- Every fixed literal/length operation is complete with thirteen buffered
bits, including extra bits and invalid reserved operations. No refill occurs. -/
theorem fixed_literal_decode (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 13 ≤ state.bits) :
    DecodeCorrespondence state (canonicalOperation fixedLiteralTable literalLengthMeaning reader)
      (decode .literalLength lenfix 9 state) := by
  obtain ⟨codeReader, hlookup, hcode, hnorm, hmeaning⟩ :=
    fixed_literal_reservoir state reader normalizes (by omega)
  have bound := fixed_literal_buffer_bound ⟨state.lowBits 9, Reservoir.lowBits_lt state 9⟩
  exact root_decode_buffered_refines .literalLength lenfix fixedLiteralTable literalLengthMeaning
    9 _ _ _ state reader codeReader hlookup hcode hnorm hmeaning (Nat.le_trans bound buffered)

/-- Every fixed distance operation is complete with eighteen buffered bits,
including the maximum thirteen extra bits. Reserved codes remain failures. -/
theorem fixed_distance_decode (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 18 ≤ state.bits) :
    DecodeCorrespondence state (canonicalOperation fixedDistanceTable distanceMeaning reader)
      (decode .distance distfix 5 state) := by
  obtain ⟨codeReader, hlookup, hcode, hnorm, hmeaning⟩ :=
    fixed_distance_reservoir state reader normalizes (by omega)
  have bound := fixed_distance_buffer_bound ⟨state.lowBits 5, Reservoir.lowBits_lt state 5⟩
  exact root_decode_buffered_refines .distance distfix fixedDistanceTable distanceMeaning
    5 _ _ _ state reader codeReader hlookup hcode hnorm hmeaning (Nat.le_trans bound buffered)

/-- Reserved literal/length symbols286/287 fail immediately after their code;
the high buffered suffix and input are represented by the retained code reader. -/
theorem fixed_literal_reserved (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 9 ≤ state.bits)
    (reserved : 286 ≤ (literalRootCode (state.lowBits 9)).symbol) :
    let witness := literalRootCode (state.lowBits 9)
    ∃ after, fixedLiteralTable.readSymbolLSB reader = some (witness.symbol, after) ∧
      decode .literalLength lenfix 9 state = .invalid (state.dropBits witness.length) witness.length ∧
      canonicalOperation fixedLiteralTable literalLengthMeaning reader = none ∧
      Reservoir.Normalizes (state.dropBits witness.length) after := by
  obtain ⟨after, hlookup, hcode, hnorm, hmeaning⟩ := fixed_literal_reservoir state reader normalizes buffered
  have invalid : literalLengthMeaning (literalRootCode (state.lowBits 9)).symbol = .invalid := by
    simp only [literalLengthMeaning, show ¬ (literalRootCode (state.lowBits 9)).symbol < 256 by omega,
      show (literalRootCode (state.lowBits 9)).symbol ≠ 256 by omega,
      show ¬ (literalRootCode (state.lowBits 9)).symbol ≤ 285 by omega, ite_false]
  exact ⟨after, hcode, by simp only [decode, hlookup, hmeaning, invalid],
    by simp only [canonicalOperation, hcode, invalid, finishMeaning], hnorm⟩

/-- Reserved distance symbols30/31 likewise fail without reading extra bits. -/
theorem fixed_distance_reserved (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 5 ≤ state.bits)
    (reserved : 30 ≤ (distanceRootCode (state.lowBits 5)).symbol) :
    let witness := distanceRootCode (state.lowBits 5)
    ∃ after, fixedDistanceTable.readSymbolLSB reader = some (witness.symbol, after) ∧
      decode .distance distfix 5 state = .invalid (state.dropBits witness.length) witness.length ∧
      canonicalOperation fixedDistanceTable distanceMeaning reader = none ∧
      Reservoir.Normalizes (state.dropBits witness.length) after := by
  obtain ⟨after, hlookup, hcode, hnorm, hmeaning⟩ := fixed_distance_reservoir state reader normalizes buffered
  have invalid : distanceMeaning (distanceRootCode (state.lowBits 5)).symbol = .invalid := by
    simp only [distanceMeaning, show ¬ (distanceRootCode (state.lowBits 5)).symbol < 30 by omega, ite_false]
  exact ⟨after, hcode, by simp only [decode, hlookup, hmeaning, invalid],
    by simp only [canonicalOperation, hcode, invalid, finishMeaning], hnorm⟩

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
