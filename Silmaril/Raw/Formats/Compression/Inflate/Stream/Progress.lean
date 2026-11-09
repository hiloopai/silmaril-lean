module

public import Silmaril.Formats.Compression.Inflate.Stream.Progress
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Blocks

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.Progress`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

/-! Small success and error checks precede the general progress proofs. A final
empty stored block succeeds, and increasing its already adequate fuel preserves
the exact final reader. An end-of-block token succeeds after one bit. -/

theorem empty_input_checked :
    decompressBlocks 1 ⟨0, 0, [], 0⟩ [] = .error .decodeOverrun := rfl

theorem empty_stored_checked :
    decompressBlocks 41 ⟨0, 0, [1, 0, 0, 0xff, 0xff], 0⟩ [] =
      .ok ([], ⟨0, 0, [], 40⟩) := rfl

theorem empty_stored_extra_fuel_checked :
    decompressBlocks 42 ⟨0, 0, [1, 0, 0, 0xff, 0xff], 0⟩ [] =
      .ok ([], ⟨0, 0, [], 40⟩) := rfl

theorem end_token_checked :
    decodeSymbol progressEndTable (HuffmanTable.empty 0) ⟨0, 0, [0], 0⟩ [] =
      .ok ([], ⟨0, 7, [], 1⟩) := rfl

/-- Successful bodies cannot increase the number of unread bits. This includes
the alignment in stored blocks and dynamic-table construction. -/
theorem decompressBlockBody_bitsLeft_le {kind : Nat} {reader rest : LSBReader}
    {output bytes : List UInt8}
    (h : decompressBlockBody kind reader output = .ok (bytes, rest)) :
    rest.bitsLeft ≤ reader.bitsLeft := by
  have hp := (Blocks.body131_eval (reader.bitsLeft + 1) kind output reader
    (Nat.le_refl _)).trans h
  exact Parser.eval_bitsLeft_le (Blocks.body131 (reader.bitsLeft + 1) kind output) hp

/-- The three header bits alone make a successful block transition strict. -/
theorem block_transition_bitsLeft_lt {reader r1 r2 rest : LSBReader}
    {final : Bool} {kind : Nat} {output bytes : List UInt8}
    (hfinal : reader.readBit = some (final, r1))
    (hkind : r1.readBits 2 = some (kind, r2))
    (hbody : decompressBlockBody kind r2 output = .ok (bytes, rest)) :
    rest.bitsLeft < reader.bitsLeft := by
  have h1 := readBit_bitsLeft hfinal
  have h2 := readBits_bitsLeft hkind
  have h3 := decompressBlockBody_bitsLeft_le hbody
  omega

/-- Adequate fuel is observationally irrelevant, for success and every error. -/
theorem decompressBlocks_stable (reader : LSBReader) (output : List UInt8)
    (fuel₁ fuel₂ : Nat) (h₁ : reader.bitsLeft + 1 ≤ fuel₁)
    (h₂ : reader.bitsLeft + 1 ≤ fuel₂) :
    decompressBlocks fuel₁ reader output = decompressBlocks fuel₂ reader output := by
  induction fuel₁ generalizing reader output fuel₂ with
  | zero => omega
  | succ fuel₁ ih =>
    cases fuel₂ with
    | zero => omega
    | succ fuel₂ =>
      rw [decompressBlocks, decompressBlocks]
      cases hf : reader.readBit with
      | none => rfl
      | some pair =>
        obtain ⟨final, r1⟩ := pair
        dsimp only
        cases hk : r1.readBits 2 with
        | none => rfl
        | some pair =>
          obtain ⟨kind, r2⟩ := pair
          dsimp only
          cases hb : decompressBlockBody kind r2 output with
          | error err => rfl
          | ok pair =>
            obtain ⟨bytes, rest⟩ := pair
            dsimp only
            cases final with
            | true => rfl
            | false =>
              have hlt := block_transition_bitsLeft_lt hf hk hb
              exact ih rest bytes fuel₂ (by omega) (by omega)

/-- Rewrite any adequate external budget to the decoder's local bit bound. -/
theorem decompressBlocks_eq_local (fuel : Nat) (reader : LSBReader) (output : List UInt8)
    (h : reader.bitsLeft + 1 ≤ fuel) :
    decompressBlocks fuel reader output = decompressBlocks (reader.bitsLeft + 1) reader output :=
  decompressBlocks_stable reader output fuel (reader.bitsLeft + 1) h (Nat.le_refl _)

/-- An unbudgeted symbol loop is one token step followed by an unbudgeted loop
at the successful MORE reader. Every successful token consumes a bit. -/
theorem decodeSymbol_unfold (litLen dist : HuffmanTable) (reader : LSBReader)
    (output : List UInt8) :
    decodeSymbol litLen dist reader output =
      match decodeStep litLen dist reader output with
      | .error err => .error err
      | .ok (.done bytes rest) => .ok (bytes, rest)
      | .ok (.more bytes rest) => decodeSymbol litLen dist rest bytes := by
  change decodeSymbolsFuel litLen dist (reader.bitsLeft + 1) reader output = _
  rw [decodeSymbolsFuel]
  cases hs : decodeStep litLen dist reader output with
  | error err => rfl
  | ok step =>
    cases step with
    | done bytes rest => rfl
    | more bytes rest =>
      have hlt := decodeStep_more_bitsLeft_lt hs
      exact decodeSymbolsFuel_eq_decodeSymbol litLen dist rest bytes reader.bitsLeft (by omega)

/-- The raw decoder unfolds a header and body, then recomputes its bound at the
next reader. No caller-chosen semantic fuel appears on the right-hand side. -/
theorem decompressBlocks_bitsLeft_unfold (reader : LSBReader) (output : List UInt8) :
    decompressBlocks (reader.bitsLeft + 1) reader output =
      match reader.readBit with
      | none => .error .decodeOverrun
      | some (final, r1) =>
        match r1.readBits 2 with
        | none => .error .decodeOverrun
        | some (kind, r2) =>
          match decompressBlockBody kind r2 output with
          | .error err => .error err
          | .ok (bytes, rest) =>
            if final then .ok (bytes, rest)
            else decompressBlocks (rest.bitsLeft + 1) rest bytes := by
  rw [decompressBlocks]
  cases hf : reader.readBit with
  | none => rfl
  | some pair =>
    obtain ⟨final, r1⟩ := pair
    dsimp only
    cases hk : r1.readBits 2 with
    | none => rfl
    | some pair =>
      obtain ⟨kind, r2⟩ := pair
      dsimp only
      cases hb : decompressBlockBody kind r2 output with
      | error err => rfl
      | ok pair =>
        obtain ⟨bytes, rest⟩ := pair
        dsimp only
        cases final with
        | true => rfl
        | false =>
          have hlt := block_transition_bitsLeft_lt hf hk hb
          exact decompressBlocks_eq_local reader.bitsLeft rest bytes (by omega)

end Silmaril.Formats.Compression.Deflate
