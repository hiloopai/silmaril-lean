module

public import Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawEmission
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawRuns

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw

open Silmaril.Formats.Compression

theorem ofMachine_invariant (kind : Protocol.ChecksumKind) (machine : RawMachine) :
    Invariant kind (ofMachine kind machine) := ⟨rfl, rfl⟩

theorem start_invariant (kind : Protocol.ChecksumKind) (input : List UInt8) :
    Invariant kind (start kind input) := ofMachine_invariant kind _

theorem start_normalizes (kind : Protocol.ChecksumKind) (input : List UInt8) :
    Reservoir.Normalizes (start kind input).reservoir (Blocks.initialReader input) :=
  RawRuns.start_normalizes input

theorem start_wellFormed (kind : Protocol.ChecksumKind) (input : List UInt8) (reader : LSBReader) :
    RawSemantics.WellFormed (start kind input).machine reader := RawRuns.start_wellFormed input reader

theorem feed_invariant (kind : Protocol.ChecksumKind) (state : State) (input : List UInt8)
    (h : Invariant kind state) : Invariant kind (feed state input) := by
  simpa only [Invariant, feed, RawMachine.feed_output] using h

theorem step_invariant (kind : Protocol.ChecksumKind) (version : Version)
    (state : State) (fuel capacity : Nat) (h : Invariant kind state) :
    Invariant kind (step kind version state fuel capacity) := by
  refine ⟨?_, ?_⟩
  · change Checksums.update kind state.check
        (RawEmission.stepEmitted version state.machine fuel capacity) = _
    rw [h.1]
    exact RawEmission.step_checksum kind version state.machine fuel capacity
  · change (state.size + (RawEmission.stepEmitted version state.machine fuel capacity).length) %
        Protocol.word32 = (RawMachine.step version state.machine fuel capacity).output.length % _
    rw [h.2, RawEmission.step_output, List.length_append]
    simp only [Nat.add_mod, Nat.mod_mod]

theorem feed_normalizes (state : State) (input : List UInt8) (reader : LSBReader)
    (h : Reservoir.Normalizes state.reservoir reader) :
    Reservoir.Normalizes (feed state input).reservoir (Reservoir.readerFeed reader input) :=
  RawRuns.feed_normalizes state.machine reader input h

theorem feed_wellFormed (state : State) (input : List UInt8) (reader : LSBReader)
    (h : RawSemantics.WellFormed state.machine reader) :
    RawSemantics.WellFormed (feed state input).machine (Reservoir.readerFeed reader input) :=
  RawRuns.feed_wellFormed state.machine reader input h

theorem feed_denote (state : State) (input : List UInt8) (reader : LSBReader) :
    RawSemantics.denote (feed state input).machine reader = RawSemantics.denote state.machine reader :=
  RawRuns.feed_denote state.machine reader input

/-- The original all-future raw continuation theorem also carries the
incrementally maintained checksum and size invariant. -/
theorem step_correct_feed (kind : Protocol.ChecksumKind) (version : Version)
    (state : State) (reader : LSBReader) (fuel capacity : Nat)
    (hinvariant : Invariant kind state)
    (hnorm : Reservoir.Normalizes state.reservoir reader)
    (hwf : RawSemantics.WellFormed state.machine reader) :
    ∃ rest, Reservoir.Normalizes (step kind version state fuel capacity).reservoir rest ∧
      RawSemantics.WellFormed (step kind version state fuel capacity).machine rest ∧
      Invariant kind (step kind version state fuel capacity) ∧
      ∀ future, RawSemantics.denote state.machine (Reservoir.readerFeed reader future) =
        RawSemantics.denote (step kind version state fuel capacity).machine
          (Reservoir.readerFeed rest future) := by
  obtain ⟨rest, hrest, hwfrest, observations⟩ :=
    RawStep.step_correct_feed version state.machine reader fuel capacity hnorm hwf
  exact ⟨rest, hrest, hwfrest, step_invariant kind version state fuel capacity hinvariant, observations⟩

/-- The list checksum is precisely the existing zlib trailer's Adler-32
observation, including the UInt32 conversion. -/
theorem checksum_adler32 (bytes : List UInt8) :
    Checksums.checksum .adler32 bytes = (adler32 ⟨bytes.toArray⟩).toNat := by
  have hbound := Checksums.checksum_lt_word32 .adler32 bytes
  simp only [Checksums.checksum, Protocol.word32] at hbound
  change adler32OfList (bytes.map UInt8.toNat) =
    (UInt32.ofNat (adler32OfList (bytes.map UInt8.toNat))).toNat
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hbound]

/-- The list checksum is precisely the existing gzip data trailer's CRC-32
observation, using the public complemented checksum. -/
theorem checksum_crc32 (bytes : List UInt8) :
    Checksums.checksum .crc32 bytes = (crc32 ⟨bytes.toArray⟩).toNat := by
  have hbound := Checksums.checksum_lt_word32 .crc32 bytes
  simp only [Checksums.checksum, Protocol.word32] at hbound
  change crc32List (bytes.map UInt8.toNat) =
    (UInt32.ofNat (crc32List (bytes.map UInt8.toNat))).toNat
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hbound]

/-- No completion premise is required: these values describe every emitted
prefix, so they are also available at a genuine raw `.done` boundary. -/
theorem adler32_values (state : State) (h : Invariant .adler32 state) :
    state.check = (adler32 ⟨state.output.toArray⟩).toNat ∧
      state.size = state.output.length % Protocol.word32 :=
  ⟨h.1.trans (checksum_adler32 _), h.2⟩

theorem crc32_values (state : State) (h : Invariant .crc32 state) :
    state.check = (crc32 ⟨state.output.toArray⟩).toNat ∧
      state.size = state.output.length % Protocol.word32 :=
  ⟨h.1.trans (checksum_crc32 _), h.2⟩

theorem start_seeds (input : List UInt8) :
    (start .adler32 input).check = 1 ∧ (start .crc32 input).check = 0 ∧
      (start .adler32 input).size = 0 ∧ (start .crc32 input).size = 0 := by
  change Checksums.checksum .adler32 [] = 1 ∧ Checksums.checksum .crc32 [] = 0 ∧
    0 % Protocol.word32 = 0 ∧ 0 % Protocol.word32 = 0
  exact ⟨Checksums.checksum_empty.1, Checksums.checksum_empty.2, Nat.zero_mod _, Nat.zero_mod _⟩

/-- Incremental state on a real stored-byte COPY: both checksum algorithms
account for exactly the one new A, and the ISIZE counter advances by one. -/
theorem storedA_checked :
    (step .adler32 .v131 (ofMachine .adler32 RawMachine.storedOneReady) 8 1).check = 0x00420042 ∧
      (step .crc32 .develop (ofMachine .crc32 RawMachine.storedOneReady) 8 1).check = 0xd3d99e8b ∧
      (step .crc32 .develop (ofMachine .crc32 RawMachine.storedOneReady) 8 1).size = 1 := by
  decide

end Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw
