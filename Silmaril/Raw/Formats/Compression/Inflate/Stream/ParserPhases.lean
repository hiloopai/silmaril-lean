module

public import Silmaril.Formats.Compression.Inflate.Stream.ParserPhases
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Parser
public import Silmaril.Raw.Formats.Compression.Inflate.Manual.Symbols
public import Silmaril.Raw.Formats.Compression.Inflate.Manual.Dynamic
public import Silmaril.Raw.Formats.Compression.Inflate.Manual.Stored

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.ParserPhases`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.ParserPhases

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate

theorem huffmanAux_eval (entries : List CodeEntry) (code length fuel : Nat)
    (r : LSBReader) :
    (huffmanAux entries code length fuel).eval r =
      symbolResult (decodeSymbolLSBAux entries r code length fuel) := by
  induction fuel generalizing code length r with
  | zero => rfl
  | succ fuel ih =>
    simp only [huffmanAux, decodeSymbolLSBAux]
    cases lookupEntry entries code length with
    | some symbol => rfl
    | none =>
      simp only [Parser.eval, LSBReader.readBits]
      cases hr : r.readBit with
      | none => rfl
      | some pair =>
        obtain ⟨bit, next⟩ := pair
        simp only [Nat.mul_zero, Nat.add_zero]
        exact ih _ _ _

theorem huffman_eval (table : HuffmanTable) (r : LSBReader) :
    (huffman table).eval r = symbolResult (table.readSymbolLSB r) :=
  huffmanAux_eval table.entries 0 0 (table.maxBits + 1) r

theorem matchToken_eval (dist : HuffmanTable) (symbol : Nat) (r : LSBReader) :
    (matchToken dist symbol).eval r = Manual.parseMatch dist symbol r := by
  unfold matchToken Manual.parseMatch
  rw [Parser.eval]
  cases lengthRead : r.readBits (Deflate.lengthExtraBits.getD (symbol - 257) 0) with
  | none => simp only [lengthRead]
  | some pair =>
    obtain ⟨extra, next⟩ := pair
    simp only [lengthRead, Parser.eval_bind, huffman_eval, symbolResult]
    cases distanceRead : dist.readSymbolLSB next with
    | none => rfl
    | some pair =>
      obtain ⟨distanceSymbol, next⟩ := pair
      dsimp only
      by_cases reserved : 30 ≤ distanceSymbol
      · simp only [reserved, ite_true, Parser.eval]
      · simp only [reserved, ite_false, Parser.eval]
        cases extraRead : next.readBits (Deflate.distanceExtraBits.getD distanceSymbol 0) with
        | none => rfl
        | some pair => rfl

theorem token_eval (litLen dist : HuffmanTable) (r : LSBReader) :
    (token litLen dist).eval r = Manual.parseToken litLen dist r := by
  simp only [token, Parser.eval_bind, huffman_eval, symbolResult, Manual.parseToken]
  cases litLen.readSymbolLSB r with
  | none => rfl
  | some pair =>
    obtain ⟨symbol, next⟩ := pair
    dsimp only
    split
    · rfl
    · split
      · rfl
      · split
        · exact matchToken_eval dist symbol next
        · rfl

theorem storedHeader_eval (r : LSBReader) :
    storedHeader.eval r = Manual.readStoredHeader r := by
  simp only [storedHeader, Parser.eval, Manual.readStoredHeader]
  cases r.alignToByte.readBits 16 with
  | none => rfl
  | some pair =>
    obtain ⟨len, next⟩ := pair
    dsimp only
    cases next.readBits 16 with
    | none => rfl
    | some pair =>
      obtain ⟨nlen, next⟩ := pair
      dsimp only
      split <;> rfl

theorem storedBytes_eval (count : Nat) (output : List UInt8) (r : LSBReader) :
    (storedBytes count output).eval r = Deflate.readStoredBytes output r count := by
  induction count generalizing output r with
  | zero => rfl
  | succ count ih =>
    simp only [storedBytes, Parser.eval, Deflate.readStoredBytes, LSBReader.readByte]
    cases r.readBits 8 with
    | none => rfl
    | some pair => exact ih _ _

theorem stored_eval (r : LSBReader) :
    stored.eval r = Manual.decompressStored r := by
  simp only [stored, Parser.eval_bind, storedHeader_eval,
    Manual.decompressStored, Manual.decompressStoredArray]
  cases Manual.readStoredHeader r with
  | error e => rfl
  | ok pair =>
    obtain ⟨count, next⟩ := pair
    dsimp only
    rw [storedBytes_eval]
    simpa only [Array.toList_empty] using (Deflate.readStoredBytesArr_eq count #[] next).symm

theorem counts_eval (r : LSBReader) :
    counts.eval r = Manual.readDynamicCounts r := by
  simp only [counts, Parser.eval, Manual.readDynamicCounts]
  cases r.readBits 5 with
  | none => rfl
  | some pair =>
    obtain ⟨hlit, r1⟩ := pair
    dsimp only
    cases r1.readBits 5 with
    | none => rfl
    | some pair =>
      obtain ⟨hdist, r2⟩ := pair
      dsimp only
      cases r2.readBits 4 with
      | none => rfl
      | some pair =>
        obtain ⟨hclen, r3⟩ := pair
        dsimp only
        split <;> rfl

theorem scatter_eval (count index : Nat) (lengths : List Nat) (r : LSBReader) :
    (scatter count index lengths).eval r = Manual.scatterCodeLengths count index lengths r := by
  induction count generalizing index lengths r with
  | zero => rfl
  | succ count ih =>
    simp only [scatter, Parser.eval, Manual.scatterCodeLengths]
    cases r.readBits 3 with
    | none => rfl
    | some pair => exact ih _ _ _

theorem lengthRun_eval (previous : List Nat) (symbol : Nat) (r : LSBReader) :
    (lengthRun previous symbol).eval r = Manual.codeLengthRun previous symbol r := by
  unfold lengthRun Manual.codeLengthRun
  split
  · rfl
  · split
    · cases previous.getLast? with
      | none => rfl
      | some length =>
        simp only [Parser.eval]
        cases r.readBits 2 <;> rfl
    · split
      · simp only [Parser.eval]
        cases r.readBits 3 <;> rfl
      · split
        · simp only [Parser.eval]
          cases r.readBits 7 <;> rfl
        · rfl

theorem expand_eval (table : HuffmanTable) (total fuel : Nat) (lengths : List Nat)
    (r : LSBReader) :
    (expand table total fuel lengths).eval r =
      Manual.expandCodeLengths table total fuel lengths r := by
  induction fuel generalizing lengths r with
  | zero =>
    unfold expand Manual.expandCodeLengths
    split <;> rfl
  | succ fuel ih =>
    simp only [expand, Manual.expandCodeLengths]
    split
    · split <;> rfl
    · simp only [Parser.eval_bind, huffman_eval, symbolResult]
      cases table.readSymbolLSB r with
      | none => rfl
      | some pair =>
        obtain ⟨symbol, next⟩ := pair
        dsimp only
        rw [lengthRun_eval]
        cases Manual.codeLengthRun lengths symbol next with
        | error e => rfl
        | ok pair => exact ih _ _

/-- The table builder consumes no bits: its reader is framed unchanged. -/
theorem build_eval (literalCount : Nat) (lengths : List Nat) (r : LSBReader) :
    (build literalCount lengths).eval r =
      match Manual.buildDynamicTables literalCount lengths r with
      | .error e => .error e
      | .ok (literals, distances, next) => .ok ((literals, distances), next) := by
  dsimp only [build, Manual.buildDynamicTables]
  split
  · rfl
  · cases Deflate.validCodeLengths (lengths.take literalCount) 15 with
    | false => simp only [Bool.not_false, ite_true, Parser.eval]
    | true =>
      cases Deflate.validCodeLengths (lengths.drop literalCount) 15 with
      | false =>
        simp only [Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true, Parser.eval]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        generalize HuffmanTable.ofLengths (lengths.take literalCount) 15 = literals
        generalize HuffmanTable.ofLengths (lengths.drop literalCount) 15 = distances
        cases literals <;> cases distances <;> rfl

theorem afterCounts_eval (c : Manual.DynamicCounts) (r : LSBReader) :
    (afterCounts c).eval r =
      match Manual.readDynamicAfterCounts c r with
      | .error e => .error e
      | .ok (literals, distances, next) => .ok ((literals, distances), next) := by
  simp only [afterCounts, Parser.eval_bind, scatter_eval, Manual.readDynamicAfterCounts]
  cases Manual.scatterCodeLengths c.codeLengths 0 (List.replicate 19 0) r with
  | error e => rfl
  | ok pair =>
    obtain ⟨codeLens, next⟩ := pair
    dsimp only
    split
    · rfl
    · cases HuffmanTable.ofLengths codeLens 7 with
      | none => rfl
      | some table =>
        dsimp only
        rw [Parser.eval_bind, expand_eval]
        cases Manual.expandCodeLengths table (c.literals + c.distances)
            (c.literals + c.distances + 1) [] next with
        | error e => rfl
        | ok pair => exact build_eval _ _ _

theorem dynamicTables_eval (r : LSBReader) :
    dynamicTables.eval r =
      match Deflate.readDynamicTables r with
      | .error e => .error e
      | .ok (literals, distances, next) => .ok ((literals, distances), next) := by
  rw [← Manual.readDynamicTables_eq]
  simp only [dynamicTables, Parser.eval_bind, counts_eval, Manual.readDynamicTables]
  cases Manual.readDynamicCounts r with
  | error e => rfl
  | ok pair => exact afterCounts_eval _ _

/-- Every literal and overlapping match, with exact EOB/error behavior, for an
arbitrary supplied token budget and arbitrary starting history. -/
theorem symbols_eval (litLen dist : HuffmanTable) (fuel : Nat) (output : List UInt8)
    (r : LSBReader) :
    (symbols litLen dist fuel output).eval r =
      Deflate.decodeSymbolsFuel litLen dist fuel r output := by
  rw [← Manual.decodeSymbolsFuel_eq_spec]
  induction fuel generalizing output r with
  | zero => rfl
  | succ fuel ih =>
    simp only [symbols, Parser.eval_bind, token_eval, Manual.decodeSymbolsFuel,
      Manual.decodeStep]
    cases Manual.parseToken litLen dist r with
    | error e => rfl
    | ok pair =>
      obtain ⟨parsed, next⟩ := pair
      dsimp only
      cases parsed with
      | literal byte => exact ih _ _
      | endBlock => rfl
      | matchBytes length distance =>
        simp only [Manual.applyToken]
        split
        · rfl
        · exact ih _ _

end Silmaril.Formats.Compression.Inflate.Stream.ParserPhases
