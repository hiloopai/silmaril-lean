module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedTableEntry
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Bits

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Packed.PackedTableEntry`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

/-- Every successful packed lookup reports its exact code-bit consumption. -/
theorem lookup_consumed (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state rest : Reservoir) (entry : Entry) (codeBits : Nat)
    (h : lookup kind table rootBits state = .found entry rest codeBits) :
    rest.consumed = state.consumed + codeBits := by
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
            simp only [Reservoir.dropBits]
            omega
          · cases h
      · cases h
        rfl
    · cases h

/-- After a packed code has selected a base and extra-bit count, the physical
extra-bit read refines the existing mathematical bit-reader operation. -/
theorem decode_extra_refines (kind : Kind) (table : Array Entry) (rootBits : Nat)
    (state rest after : Reservoir) (entry : Entry) (codeBits base extra amount : Nat)
    (reader : LSBReader)
    (hlookup : lookup kind table rootBits state = .found entry rest codeBits)
    (hmeaning : meaning kind entry = .baseExtra base extra)
    (hn : Reservoir.Normalizes rest reader)
    (hread : rest.readBits extra = .value amount after) :
    ∃ canonical, reader.readBits extra = some (amount, canonical) ∧
      Reservoir.Normalizes after canonical ∧
      decode kind table rootBits state = .value (.amount (base + amount)) after codeBits extra := by
  obtain ⟨canonical, hr, hafter⟩ := hn.readBits hread
  exact ⟨canonical, hr, hafter, by simp only [decode, hlookup, hmeaning, hread]⟩

theorem literal_and_distance_link_tests_differ :
    isLink .literalLength ⟨0, 8, 65⟩ = false ∧
      isLink .distance ⟨0, 8, 65⟩ = true := by decide

theorem endBlock_precedes_invalid : meaning .literalLength ⟨96, 7, 0⟩ = .endBlock := by decide

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
