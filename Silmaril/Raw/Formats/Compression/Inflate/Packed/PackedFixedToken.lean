module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedToken
public import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedFixedDecode

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Packed.PackedFixedToken`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Factor the manual parser through the complete literal/length operation,
without losing any error or reader information. -/
theorem parseToken_operations (litLen dist : HuffmanTable) (reader : LSBReader) :
    parseToken litLen dist reader =
      match canonicalOperation litLen literalLengthMeaning reader with
      | none => .error .decodeOverrun
      | some (.literal value, rest) => .ok (.literal (UInt8.ofNat value), rest)
      | some (.endBlock, rest) => .ok (.endBlock, rest)
      | some (.amount length, rest) => parseDistance dist length rest := by
  unfold parseToken canonicalOperation
  cases hcode : litLen.readSymbolLSB reader with
  | none => rfl
  | some pair =>
    rcases pair with ⟨symbol, rest⟩
    simp only [literalLengthMeaning]
    split
    · rfl
    · split
      · rfl
      · split
        · dsimp only [parseMatch, finishMeaning]
          cases rest.readBits (Deflate.lengthExtraBits.getD (symbol - 257) 0) <;> rfl
        · rfl

/-- A successful distance operation produces precisely the manual match
token, retaining its full reader. No successful decode is assumed globally. -/
theorem parseDistance_of_amount (table : HuffmanTable) (reader after : LSBReader)
    (length distance : Nat)
    (h : canonicalOperation table distanceMeaning reader = some (.amount distance, after)) :
    parseDistance table length reader = .ok (.matchBytes length distance, after) := by
  unfold canonicalOperation at h
  unfold parseDistance
  cases hcode : table.readSymbolLSB reader with
  | none => simp only [hcode] at h; cases h
  | some pair =>
    rcases pair with ⟨symbol, rest⟩
    simp only [hcode, distanceMeaning] at h
    by_cases valid : symbol < 30
    · simp only [valid, ite_true, finishMeaning] at h
      simp only [show ¬30 ≤ symbol by omega, ite_false]
      cases hread : rest.readBits (Deflate.distanceExtraBits.getD symbol 0) with
      | none => simp only [hread, Option.map_none] at h; cases h
      | some pair =>
        rcases pair with ⟨extra, final⟩
        simp only [hread, Option.map_some, Option.some.injEq, Prod.mk.injEq,
          Value.amount.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
    · simp only [valid, ite_false, finishMeaning] at h; cases h

theorem distanceOperation_amount (table : HuffmanTable) (reader after : LSBReader)
    (value : Value) (h : canonicalOperation table distanceMeaning reader = some (value, after)) :
    ∃ distance, value = .amount distance := by
  unfold canonicalOperation at h
  cases hcode : table.readSymbolLSB reader with
  | none => simp only [hcode] at h; cases h
  | some pair =>
    rcases pair with ⟨symbol, rest⟩
    simp only [hcode, distanceMeaning] at h
    split at h
    · simp only [finishMeaning] at h
      cases hread : rest.readBits (Deflate.distanceExtraBits.getD symbol 0) with
      | none => simp only [hread, Option.map_none] at h; cases h
      | some pair =>
        rcases pair with ⟨extra, final⟩
        simp only [hread, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨_, h.1.symm⟩
    · cases h

theorem decode_budget (kind : Kind) (table : Array Entry) (width : Nat)
    (state rest : Reservoir) (entry : Entry) (code limit : Nat)
    (hlookup : lookup kind table width state = .found entry rest code)
    (bound : code + extraWidth (meaning kind entry) ≤ limit) :
    DecodeBudget limit (decode kind table width state) := by
  simp only [decode, hlookup]
  cases hmeaning : meaning kind entry with
  | literal value => simpa only [hmeaning, extraWidth, Nat.add_zero, DecodeBudget] using bound
  | endBlock => simpa only [hmeaning, extraWidth, Nat.add_zero, DecodeBudget] using bound
  | invalid => simpa only [hmeaning, extraWidth, Nat.add_zero, DecodeBudget] using bound
  | baseExtra base extra =>
    simp only
    cases rest.readBits extra with
    | needInput saved => trivial
    | value amount after => simpa only [hmeaning, extraWidth, DecodeBudget] using bound

theorem fixed_literal_decode_budget (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 9 ≤ state.bits) :
    DecodeBudget 13 (decode .literalLength lenfix 9 state) := by
  obtain ⟨after, hlookup, _, _, hmeaning⟩ := fixed_literal_reservoir state reader normalizes buffered
  apply decode_budget .literalLength lenfix 9 state _ _ _ 13 hlookup
  rw [hmeaning]
  exact fixed_literal_buffer_bound ⟨state.lowBits 9, Reservoir.lowBits_lt state 9⟩

theorem fixed_distance_decode_budget (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 5 ≤ state.bits) :
    DecodeBudget 18 (decode .distance distfix 5 state) := by
  obtain ⟨after, hlookup, _, _, hmeaning⟩ := fixed_distance_reservoir state reader normalizes buffered
  apply decode_budget .distance distfix 5 state _ _ _ 18 hlookup
  rw [hmeaning]
  exact fixed_distance_buffer_bound ⟨state.lowBits 5, Reservoir.lowBits_lt state 5⟩

/-- Invalid packed fixed distance operations are exactly reserved distance
symbols, whose precise mathematical error can be recovered from the root. -/
theorem fixed_distance_invalid (state after : Reservoir) (reader : LSBReader)
    (code length : Nat) (normalizes : Reservoir.Normalizes state reader)
    (buffered : 5 ≤ state.bits)
    (h : decode .distance distfix 5 state = .invalid after code) :
    30 ≤ (distanceRootCode (state.lowBits 5)).symbol ∧
      parseDistance fixedDistanceTable length reader =
        .error (.badDistanceCode (distanceRootCode (state.lowBits 5)).symbol) := by
  obtain ⟨rest, hlookup, hcode, _, hmeaning⟩ :=
    fixed_distance_reservoir state reader normalizes buffered
  have reserved : 30 ≤ (distanceRootCode (state.lowBits 5)).symbol := by
    by_cases valid : (distanceRootCode (state.lowBits 5)).symbol < 30
    · simp only [decode, hlookup, hmeaning, distanceMeaning, valid, ite_true] at h
      cases hread : (state.dropBits (distanceRootCode (state.lowBits 5)).length).readBits
          (Deflate.distanceExtraBits.getD (distanceRootCode (state.lowBits 5)).symbol 0) <;>
        simp only [hread] at h <;> cases h
    · omega
  exact ⟨reserved, by simp only [parseDistance, hcode, reserved, ite_true]⟩

/-- Every fixed token, including either reserved-code error, has exact
canonical behavior and an exact four-part physical trace. Thirty-one buffered
bits cover thirteen length bits followed by eighteen distance bits. -/
theorem fixed_token_decode (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 31 ≤ state.bits) :
    TokenCorrespondence state reader (decodeFixedToken state) := by
  have firstCorr := fixed_literal_decode state reader normalizes (by omega)
  have firstBudget := fixed_literal_decode_budget state reader normalizes (by omega)
  unfold decodeFixedToken
  cases first : decode .literalLength lenfix 9 state with
  | tableBounds => simp only [first, DecodeCorrespondence] at firstCorr
  | needCode saved => simp only [first, DecodeCorrespondence] at firstCorr
  | needExtra base extra saved code =>
    simp only [first, DecodeCorrespondence] at firstCorr
  | invalid after code =>
    simp only [first, DecodeCorrespondence] at firstCorr
    simp only [first, DecodeBudget] at firstBudget
    rcases firstCorr with ⟨hcanonical, hdrop, hvalid⟩
    exact ⟨by rw [parseToken_operations, hcanonical],
      by simpa only [TokenTrace.total, Nat.add_zero] using hdrop,
      hvalid, by change code + 0 + 0 + 0 ≤ 31; omega⟩
  | value value rest code extra =>
    simp only [first, DecodeCorrespondence] at firstCorr
    simp only [first, DecodeBudget] at firstBudget
    rcases firstCorr with ⟨middle, hcanonical, hnorm, hdrop⟩
    have hparse := parseToken_operations fixedLiteralTable fixedDistanceTable reader
    rw [hcanonical] at hparse
    cases value with
    | literal byte =>
      exact ⟨middle, hparse, hnorm,
        by simpa only [TokenTrace.total, Nat.add_zero] using hdrop,
        by change code + extra + 0 + 0 ≤ 31; omega⟩
    | endBlock =>
      exact ⟨middle, hparse, hnorm,
        by simpa only [TokenTrace.total, Nat.add_zero] using hdrop,
        by change code + extra + 0 + 0 ≤ 31; omega⟩
    | amount length =>
      simp only
      have remaining : 18 ≤ rest.bits := by
        rw [hdrop]
        change 18 ≤ state.bits - (code + extra)
        omega
      have secondCorr := fixed_distance_decode rest middle hnorm remaining
      have secondBudget := fixed_distance_decode_budget rest middle hnorm (by omega)
      cases second : decode .distance distfix 5 rest with
      | tableBounds => simp only [second, DecodeCorrespondence] at secondCorr
      | needCode saved => simp only [second, DecodeCorrespondence] at secondCorr
      | needExtra base distanceExtra saved distanceCode =>
        simp only [second, DecodeCorrespondence] at secondCorr
      | invalid after distanceCode =>
        simp only [second, DecodeCorrespondence] at secondCorr
        simp only [second, DecodeBudget] at secondBudget
        rcases secondCorr with ⟨_, hdistanceDrop, hvalid⟩
        obtain ⟨_, hinvalid⟩ :=
          fixed_distance_invalid rest after middle distanceCode length hnorm (by omega) second
        exact ⟨hparse.trans hinvalid,
          by simpa only [TokenTrace.total, Nat.add_zero] using
            hdistanceDrop.trans (by rw [hdrop, dropBits_add]),
          hvalid, by change code + extra + distanceCode + 0 ≤ 31; omega⟩
      | value distanceValue after distanceCode distanceExtra =>
        simp only [second, DecodeCorrespondence] at secondCorr
        simp only [second, DecodeBudget] at secondBudget
        rcases secondCorr with ⟨final, hdistance, hfinal, hdistanceDrop⟩
        obtain ⟨distance, rfl⟩ := distanceOperation_amount fixedDistanceTable middle final
          distanceValue hdistance
        exact ⟨final,
          hparse.trans (parseDistance_of_amount fixedDistanceTable middle final length distance hdistance),
          hfinal,
          by simpa only [TokenTrace.total, Nat.add_assoc] using
            hdistanceDrop.trans (by rw [hdrop, dropBits_add]; simp only [Nat.add_assoc]),
          by change code + extra + distanceCode + distanceExtra ≤ 31; omega⟩

/-- Explicit physical consequences of the complete token theorem. Input is
unchanged even though canonical normalization may expose prefetched bytes. -/
theorem fixed_token_no_refill (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 31 ≤ state.bits) :
    match decodeFixedToken state with
    | .value _ after trace | .error _ after trace =>
      after.input = state.input ∧ after.bits = state.bits - trace.total ∧
        after.consumed = state.consumed + trace.total ∧
        after.hold = state.hold / 2 ^ trace.total ∧ trace.total ≤ 31
    | .incomplete => False := by
  have correspondence := fixed_token_decode state reader normalizes buffered
  cases result : decodeFixedToken state with
  | incomplete => simp only [result, TokenCorrespondence] at correspondence
  | value token after trace =>
    simp only [result, TokenCorrespondence] at correspondence
    obtain ⟨_, _, _, hdrop, hbound⟩ := correspondence
    rw [hdrop]
    exact ⟨rfl, rfl, rfl, rfl, hbound⟩
  | error error after trace =>
    simp only [result, TokenCorrespondence] at correspondence
    obtain ⟨_, hdrop, _, hbound⟩ := correspondence
    rw [hdrop]
    exact ⟨rfl, rfl, rfl, rfl, hbound⟩

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
