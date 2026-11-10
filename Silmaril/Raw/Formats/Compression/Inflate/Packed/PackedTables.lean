module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedTables
public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedData
public import Silmaril.Raw.Formats.Compression.Inflate.Manual.Symbols

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Packed.PackedTables`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536

private theorem fastDecode_eq (entries : List CodeEntry) (fuel : Nat) (reader : LSBReader)
    (code length : Nat) :
    fastDecode entries reader code length fuel = decodeSymbolLSBAux entries reader code length fuel := by
  induction fuel generalizing reader code length with
  | zero => rfl
  | succ fuel ih =>
    rw [fastDecode, decodeSymbolLSBAux, lookupEntry_eq_lookupEntryFast]
    cases lookupEntryFast entries code length with
    | some _ => rfl
    | none =>
      cases reader.readBit with
      | none => rfl
      | some pair => exact ih pair.2 _ _

private theorem fastCodeObservation_eq (table : Option HuffmanTable) (symbolMeaning : Nat → Meaning)
    (width word : Nat) :
    fastCodeObservation table symbolMeaning width word = canonicalCodeObservation table symbolMeaning width word := by
  cases table with
  | none => rfl
  | some table => simp only [fastCodeObservation, canonicalCodeObservation,
      HuffmanTable.readSymbolLSB, fastDecode_eq]

theorem fixed_sizes : lenfix.size = 512 ∧ distfix.size = 32 := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem fixed_distance_root_correspondence :
    ∀ index : Fin 32, packedCodeObservation .distance distfix 5 index.val =
      canonicalCodeObservation Deflate.fixedDistTable distanceMeaning 5 index.val := by
  have computed : ∀ index : Fin 32, packedCodeObservation .distance distfix 5 index.val =
      fastCodeObservation Deflate.fixedDistTable distanceMeaning 5 index.val := by decide +kernel
  intro index
  exact (computed index).trans (fastCodeObservation_eq _ _ _ _)

set_option maxHeartbeats 8000000 in
theorem fixed_literalLength_root_correspondence :
    ∀ index : Fin 512, packedCodeObservation .literalLength lenfix 9 index.val =
      canonicalCodeObservation Deflate.fixedLitLenTable literalLengthMeaning 9 index.val := by
  have computed : ∀ index : Fin 512, packedCodeObservation .literalLength lenfix 9 index.val =
      fastCodeObservation Deflate.fixedLitLenTable literalLengthMeaning 9 index.val := by decide +kernel
  intro index
  exact (computed index).trans (fastCodeObservation_eq _ _ _ _)

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
