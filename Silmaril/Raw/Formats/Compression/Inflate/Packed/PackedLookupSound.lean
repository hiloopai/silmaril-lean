module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedLookupSound
public import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedTableEntry

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Packed.PackedLookupSound`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

/-- Consecutive physical drops have the same complete state as one combined
drop, including the logical position. This identity also holds outside the
bounded semantic contract; successful lookup separately proves the bound. -/
theorem dropBits_add (state : Reservoir) (first second : Nat) :
    (state.dropBits first).dropBits second = state.dropBits (first + second) := by
  cases state
  simp only [Reservoir.dropBits, Nat.sub_sub, Nat.add_assoc,
    Nat.div_div_eq_div_mul, Nat.pow_add]

/-- The lookup's own bit-count checks justify every successful DROPBITS.
The returned state is exact, rather than only agreeing on a counter. -/
theorem lookup_dropBits (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state rest : Reservoir) (entry : Entry) (codeBits : Nat)
    (h : lookup kind table rootBits state = .found entry rest codeBits) :
    codeBits ≤ state.bits ∧ rest = state.dropBits codeBits := by
  unfold lookup at h
  split at h
  · cases h
  · split at h
    · split at h
      · dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
            exact ⟨by assumption, dropBits_add _ _ _⟩
          · cases h
      · cases h
        exact ⟨by assumption, rfl⟩
    · cases h

/-- Successful lookup preserves reservoir validity and removes exactly the
reported prefix from the logical unread bitstream. It never pulls input. -/
theorem lookup_unread (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state rest : Reservoir) (entry : Entry) (codeBits : Nat)
    (valid : state.Valid)
    (h : lookup kind table rootBits state = .found entry rest codeBits) :
    rest.Valid ∧ rest.unread = state.unread.drop codeBits ∧
      rest.input = state.input ∧ rest.bits = state.bits - codeBits := by
  obtain ⟨bound, rfl⟩ := lookup_dropBits kind table rootBits state rest entry codeBits h
  exact ⟨Reservoir.dropBits_valid valid bound,
    Reservoir.dropBits_unread state bound, rfl, rfl⟩

/-- The canonical reader consumes exactly the same code-bit word and retains
the same logical unread suffix as the independently implemented packed lookup.
No canonical codebook interpretation is assumed by this theorem. -/
theorem lookup_readBits (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state rest : Reservoir) (entry : Entry) (codeBits : Nat) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader)
    (h : lookup kind table rootBits state = .found entry rest codeBits) :
    ∃ after, reader.readBits codeBits = some (state.lowBits codeBits, after) ∧
      Reservoir.Normalizes rest after := by
  obtain ⟨bound, rfl⟩ := lookup_dropBits kind table rootBits state rest entry codeBits h
  apply normalizes.readBits
  simp only [Reservoir.readBits, Reservoir.needBits_ready bound]

/-- A suspended lookup has not dropped a root prefix, even when the root was
available and only its subtable leaf needed more bits. -/
theorem lookup_needInput_unchanged (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state saved : Reservoir)
    (h : lookup kind table rootBits state = .needInput saved) : saved = state := by
  unfold lookup at h
  split at h
  · cases h
  · split at h
    · split at h
      · dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · cases h; rfl
      · cases h
    · cases h; rfl

/-- Every successful decoded value factors into a canonical code-bit read
followed by interpretation of the selected packed operation. In particular,
LENEXT and DISTEXT retain their real extra-bit reads and final reader, rather
than merely agreeing on the numeric decoded amount. -/
theorem decode_value_refines (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state after : Reservoir) (value : Value) (codeBits extraBits : Nat) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader)
    (decoded : decode kind table rootBits state = .value value after codeBits extraBits) :
    ∃ entry rest codeReader afterReader,
      lookup kind table rootBits state = .found entry rest codeBits ∧
      reader.readBits codeBits = some (state.lowBits codeBits, codeReader) ∧
      Reservoir.Normalizes rest codeReader ∧
      finishMeaning (meaning kind entry) codeReader = some (value, afterReader) ∧
      Reservoir.Normalizes after afterReader ∧
      after.consumed = state.consumed + codeBits + extraBits := by
  unfold decode at decoded
  cases looked : lookup kind table rootBits state with
  | tableBounds => simp only [looked] at decoded; cases decoded
  | needInput saved => simp only [looked] at decoded; cases decoded
  | found entry rest n =>
    simp only [looked] at decoded
    obtain ⟨codeReader, hread, hnorm⟩ :=
      lookup_readBits kind table rootBits state rest entry n reader normalizes looked
    have hconsumed := lookup_consumed kind table rootBits state rest entry n looked
    cases selected : meaning kind entry with
    | literal byte =>
      simp only [selected, DecodeResult.value.injEq] at decoded
      rcases decoded with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨entry, rest, codeReader, codeReader, rfl, hread, hnorm,
        by simp only [finishMeaning, selected], hnorm, by omega⟩
    | endBlock =>
      simp only [selected, DecodeResult.value.injEq] at decoded
      rcases decoded with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨entry, rest, codeReader, codeReader, rfl, hread, hnorm,
        by simp only [finishMeaning, selected], hnorm, by omega⟩
    | invalid => simp only [selected] at decoded; cases decoded
    | baseExtra base extra =>
      simp only [selected] at decoded
      cases he : rest.readBits extra with
      | needInput saved => simp only [he] at decoded; cases decoded
      | value amount final =>
        simp only [he, DecodeResult.value.injEq] at decoded
        rcases decoded with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨afterReader, hextra, hfinal⟩ := hnorm.readBits he
        have sound := Reservoir.readBits_sound extra hnorm.1
        rw [he] at sound
        exact ⟨entry, rest, codeReader, afterReader, rfl, hread, hnorm,
          by simp only [finishMeaning, selected, hextra, Option.map_some], hfinal, by
            have hcounter := sound.2.2.2.1
            omega⟩

/-! Small satisfiable branch checks: a one-bit
root plus a one-bit leaf consumes two bits, while the same root with only one
available bit suspends without consuming it. -/

theorem checked_subtable_consumption :
    lookup .literalLength checkedLinked 1 ⟨3, 2, [170], 10⟩ =
      .found ⟨0, 1, 67⟩ ⟨0, 0, [170], 12⟩ 2 ∧
    lookup .literalLength checkedLinked 1 ⟨1, 1, [170], 10⟩ =
      .needInput ⟨1, 1, [170], 10⟩ := by decide

/-- The operation-selected extra bit is consumed after the two code bits;
the unconsumed high bits and later byte remain available. -/
theorem checked_extra_consumption :
    decode .literalLength #[⟨17, 2, 3⟩] 0 ⟨23, 5, [170], 10⟩ =
      .value (.amount 4) ⟨2, 2, [170], 13⟩ 2 1 := by decide

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
