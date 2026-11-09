module

public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberMachine

/-!
# Preservation of the incremental gzip-header member phase

An active header advances its saved byte controller;
a completed header enters raw DEFLATE at the exact existing cursor. Every case
preserves the member continuation for all later input extensions. Invalid
headers become an explicit member error. The header's covered-prefix trace is
still a mathematical representation of FHCRC input.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberGzipStep

open Silmaril.Formats.Compression

theorem step_correct_feed (version : Version) (header : GzipHeader.Machine)
    (reader : LSBReader) (fuel capacity : Nat)
    (hnorm : Reservoir.Normalizes (MemberMachine.gzipHeader header).reservoir reader)
    (hwf : (MemberMachine.gzipHeader header).WellFormed reader) :
    ∃ rest,
      Reservoir.Normalizes
        (MemberMachine.step version (.gzipHeader header) fuel capacity).reservoir rest ∧
      (MemberMachine.step version (.gzipHeader header) fuel capacity).WellFormed rest ∧
      ∀ future,
        (MemberMachine.gzipHeader header).denote (Reservoir.readerFeed reader future) =
          (MemberMachine.step version (.gzipHeader header) fuel capacity).denote
            (Reservoir.readerFeed rest future) := by
  change Reservoir.Normalizes header.reservoir reader at hnorm
  change reader.buffer = 0 ∧ reader.count = 0 at hwf
  rcases reader with ⟨buffer, count, input, total⟩
  rcases hwf with ⟨rfl, rfl⟩
  cases hdone : header.isDone with
  | true =>
    have hphase : header.control.phase = .done := by
      simpa only [GzipHeader.Machine.isDone, beq_iff_eq] using hdone
    simp only [MemberMachine.step, hdone, ↓reduceIte]
    refine ⟨ContainerFields.alignedReader input total, ?_,
      MemberMachine.enterBody_wellFormed .gzip header.reservoir _, ?_⟩
    · simpa only [MemberMachine.enterBody_reservoir, ContainerFields.alignedReader] using hnorm
    · intro future
      rw [MemberMachine.enterBody_denote]
      change (header.denoteReader (ContainerFields.alignedReader (input ++ future) total)).bind
          (MemberSemantics.body .gzip) =
        MemberSemantics.body .gzip (ContainerFields.alignedReader (input ++ future) total)
      simp only [GzipHeader.Machine.denoteReader, GzipHeader.Machine.denote]
      rw [GzipHeader.evaluate.eq_def, hphase]
      simp only [ContainerFields.alignedReader, Option.map_some, Nat.sub_self,
        Nat.mul_zero, Nat.add_zero, Option.bind_some]
  | false =>
    cases hbad : header.isBad with
    | true =>
      have hphase : header.control.phase = .bad := by
        simpa only [GzipHeader.Machine.isBad, beq_iff_eq] using hbad
      simp only [MemberMachine.step, hdone, hbad, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ContainerFields.alignedReader input total, hnorm, trivial, ?_⟩
      intro future
      change (header.denoteReader (ContainerFields.alignedReader (input ++ future) total)).bind
          (MemberSemantics.body .gzip) = none
      simp only [GzipHeader.Machine.denoteReader, GzipHeader.Machine.denote]
      rw [GzipHeader.evaluate.eq_def, hphase]
      rfl
    | false =>
      obtain ⟨rest, nextTotal, hrest, observations⟩ :=
        GzipHeader.step_correct_reader_feed header input total hnorm
      simp only [MemberMachine.step, hdone, hbad, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ContainerFields.alignedReader rest nextTotal, hrest, ⟨rfl, rfl⟩, ?_⟩
      intro future
      change (header.denoteReader (ContainerFields.alignedReader (input ++ future) total)).bind
          (MemberSemantics.body .gzip) =
        (header.step.denoteReader (ContainerFields.alignedReader (rest ++ future) nextTotal)).bind
          (MemberSemantics.body .gzip)
      rw [observations future]

end Silmaril.Formats.Compression.Inflate.Stream.MemberGzipStep
