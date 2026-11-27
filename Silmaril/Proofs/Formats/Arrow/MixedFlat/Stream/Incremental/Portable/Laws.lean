module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Thms
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Thms
import Silmaril.Prelude.Bytes.Equiv.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Portable

theorem reference_octets {wire : KBytes} (wf : wire.wf = true) :
    (reference wire).toList = wire.toList := by
  change KBytes.unpack wire.len (wire.read 0 wire.len) = wire.toList
  rw [wire.unpack_read wf (by simp : 0 + wire.len ≤ wire.len), List.drop_zero]
  exact List.take_of_length_le (Nat.le_of_eq (wire.length_toList wf))

theorem reference_congr {left right : KBytes} (leftWf : left.wf = true) (rightWf : right.wf = true)
    (octets : left.toList = right.toList) : reference left = reference right := by
  have same := KBytes.equiv_iff.mpr octets
  have length := KBytes.len_eq_of_equiv leftWf rightWf same
  have word := KBytes.read_congr leftWf rightWf same (off := 0) (w := left.len) (by simp)
  unfold reference
  rw [← length, word]

theorem completed_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Completed limits wire) :
    run.endOffset = wire.len ∧
    MixedFlat.Stream.read limits.mixed (reference wire) = .ok ⟨run.fields, run.batches.map Delivered.record⟩ ∧
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) = run.trace := by
  obtain ⟨_, _, opening, records, exhausted, ended⟩ := run.ran
  obtain ⟨closed, recordsExact⟩ := complete_agrees opening records exhausted ended
  exact ⟨closed, recordsExact, complete_pull_agrees opening records exhausted ended⟩

theorem original_eos {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (wf : wire.wf = true) (run : Completed limits wire) :
    ∃ offset, offset + 8 = run.endOffset ∧ readEnvelope limits.mixed.observation.ipc wire offset = .ok .eos := by
  obtain ⟨_, _, opening, records, exhausted, ended⟩ := run.ran
  obtain ⟨held, openedLimits, phase, _⟩ := open_agrees opening
  rw [← openedLimits] at held
  obtain ⟨running, finalHeld, finalLimits, finalPhase, _, _⟩ := steps_agree records held phase
  rw [← finalLimits] at finalHeld
  obtain ⟨atEnd, eos, _⟩ := finish_agrees finalHeld finalPhase exhausted ended
  obtain ⟨envelope, extent⟩ := MixedFlat.Stream.Events.readNext_eos.mp eos
  rw [finalLimits, openedLimits] at envelope
  refine ⟨_, extent.trans atEnd.symm, ?_⟩
  exact (readEnvelope_rechunk (input := reference wire) (other := wire) rfl wf
    (reference_octets wf) _ _ _).mp envelope

theorem schedules_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Completed limits left) (b : Completed limits right) (projection : Projection) :
    a.endOffset = b.endOffset ∧ a.ranges = b.ranges ∧ a.project projection = b.project projection := by
  obtain ⟨endA, eagerA, pullA⟩ := completed_exact a
  obtain ⟨endB, eagerB, pullB⟩ := completed_exact b
  have length := KBytes.len_eq_of_equiv leftWf rightWf (KBytes.equiv_iff.mpr octets)
  rw [reference_congr leftWf rightWf octets] at eagerA pullA
  have eager := Except.ok.inj (eagerA.symm.trans eagerB)
  refine ⟨endA.trans (length.trans endB.symm), ?_,
    congrArg (fun trace => trace.scan projection (fun _ _ => some true)) (pullA.symm.trans pullB)⟩
  simpa only [Completed.ranges, List.map_map, Function.comp_def] using
    congrArg (fun observed : MixedFlat.Stream.Observed => observed.batches.map MixedFlat.Stream.Batch.range) eager

theorem writer_readback {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    {fields : List MixedFlat.Field} {batches : List OrderedWriter.BatchInput}
    {shape : List MixedFlat.Field → Bool} (written : OrderedWriter.emit limits.mixed fields batches shape = .ok wire)
    (checked : checkWriterReadback limits.mixed wire fields batches = true)
    (run : Completed limits wire) :
    (reference wire).toList = wire.toList ∧
    run.fields = fields ∧
    (run.batches.map fun batch => StreamWriter.observeBatch batch.record) =
      batches.map OrderedWriter.BatchInput.observe ∧
    ∃ offset, offset + 8 = run.endOffset ∧ readEnvelope limits.mixed.observation.ipc wire offset = .ok .eos := by
  obtain ⟨_, _, _, _, wf, _⟩ := OrderedWriter.emit_readback written
  have eager := (completed_exact run).2.1
  simp [checkWriterReadback, eager, List.map_map, Function.comp_def] at checked
  exact ⟨reference_octets wf, checked.1, checked.2, original_eos wf run⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable
