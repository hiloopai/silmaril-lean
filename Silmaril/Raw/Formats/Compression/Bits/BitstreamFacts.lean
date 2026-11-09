module

public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas

/-!
# Elementary facts about the bit readers

The general, quantified facts the DEFLATE decoder relies on: an `n`-bit read
consumes exactly `n` bits and yields a value below `2 ^ n`.  The known-answer
checks at the end pin the *bit order* of each reader — reading three bits of the
byte `0x80` gives `0` least-significant-bit first and `4` most-significant-bit
first — which is the only thing that distinguishes `LSBReader` from `MSBReader`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-! ### LSB-first reader -/

theorem LSBReader.refill_totalRead (r : LSBReader) : r.refill.totalRead = r.totalRead := by
  unfold LSBReader.refill; split <;> rfl

theorem LSBReader.readBit_totalRead {r r' : LSBReader} {b : Bool} (h : r.readBit = some (b, r')) :
    r'.totalRead = r.totalRead + 1 := by
  rw [LSBReader.readBit] at h
  by_cases hc : r.count = 0
  · simp only [hc, ↓reduceIte] at h
    by_cases hc' : r.refill.count = 0
    · simp only [hc', ↓reduceIte] at h
      exact absurd h (by simp)
    · simp only [hc', ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2, LSBReader.refill_totalRead]
  · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]

theorem LSBReader.readBits_lt {n : Nat} : ∀ {r r' : LSBReader} {v : Nat},
    r.readBits n = some (v, r') → v < 2 ^ n := by
  induction n with
  | zero =>
    intro r r' v h
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | succ n ih =>
    intro r r' v h
    simp only [LSBReader.readBits] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · next val r'' hv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hlt := ih hv
        rw [← h.1, Nat.pow_succ]
        split <;> omega

theorem LSBReader.readBits_totalRead {n : Nat} : ∀ {r r' : LSBReader} {v : Nat},
    r.readBits n = some (v, r') → r'.totalRead = r.totalRead + n := by
  induction n with
  | zero =>
    intro r r' v h
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; omega
  | succ n ih =>
    intro r r' v h
    simp only [LSBReader.readBits] at h
    split at h
    · simp at h
    · next b r1 hb =>
      split at h
      · simp at h
      · next val r2 hv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, ih hv, LSBReader.readBit_totalRead hb]
        omega

/-! ### MSB-first reader -/

theorem MSBReader.refill_totalRead (r : MSBReader) : r.refill.totalRead = r.totalRead := by
  unfold MSBReader.refill; split <;> rfl

theorem MSBReader.readBit_totalRead {r r' : MSBReader} {b : Bool} (h : r.readBit = some (b, r')) :
    r'.totalRead = r.totalRead + 1 := by
  rw [MSBReader.readBit] at h
  by_cases hc : r.count = 0
  · simp only [hc, ↓reduceIte] at h
    by_cases hc' : r.refill.count = 0
    · simp only [hc', ↓reduceIte] at h
      exact absurd h (by simp)
    · simp only [hc', ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2, MSBReader.refill_totalRead]
  · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]

theorem MSBReader.readBits_lt {n : Nat} : ∀ {r r' : MSBReader} {v : Nat},
    r.readBits n = some (v, r') → v < 2 ^ n := by
  induction n with
  | zero =>
    intro r r' v h
    simp only [MSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | succ n ih =>
    intro r r' v h
    simp only [MSBReader.readBits] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · next val r'' hv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hlt := ih hv
        rw [← h.1, Nat.pow_succ]
        split <;> omega

theorem MSBReader.readBits_totalRead {n : Nat} : ∀ {r r' : MSBReader} {v : Nat},
    r.readBits n = some (v, r') → r'.totalRead = r.totalRead + n := by
  induction n with
  | zero =>
    intro r r' v h
    simp only [MSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; omega
  | succ n ih =>
    intro r r' v h
    simp only [MSBReader.readBits] at h
    split at h
    · simp at h
    · next b r1 hb =>
      split at h
      · simp at h
      · next val r2 hv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, ih hv, MSBReader.readBit_totalRead hb]
        omega

/-! ### Bit order, pinned -/

private theorem toList_0x80 : (⟨#[0x80]⟩ : ByteArray).toList = [0x80] := by
  rw [ByteArray_toList_eq]

private theorem toList_0x4d : (⟨#[0x4d]⟩ : ByteArray).toList = [0x4d] := by
  rw [ByteArray_toList_eq]

/-- Least-significant bit first: the first three bits of `0x80` are `0, 0, 0`. -/
theorem LSBReader_readBits_three_0x80 :
    (((LSBReader.ofByteArray ⟨#[0x80]⟩).readBits 3).map Prod.fst) = some 0 := by
  simp only [LSBReader.ofByteArray, toList_0x80]; decide

/-- Most-significant bit first: the first three bits of `0x80` are `1, 0, 0`. -/
theorem MSBReader_readBits_three_0x80 :
    (((MSBReader.ofByteArray ⟨#[0x80]⟩).readBits 3).map Prod.fst) = some 4 := by
  simp only [MSBReader.ofByteArray, toList_0x80]; decide

/-- A whole byte reads back as itself, LSB-first… -/
theorem LSBReader_readBits_eight_0x4d :
    (((LSBReader.ofByteArray ⟨#[0x4d]⟩).readBits 8).map Prod.fst) = some 0x4d := by
  simp only [LSBReader.ofByteArray, toList_0x4d]; decide

/-- …and MSB-first. -/
theorem MSBReader_readBits_eight_0x4d :
    (((MSBReader.ofByteArray ⟨#[0x4d]⟩).readBits 8).map Prod.fst) = some 0x4d := by
  simp only [MSBReader.ofByteArray, toList_0x4d]; decide

end Silmaril.Formats.Compression
