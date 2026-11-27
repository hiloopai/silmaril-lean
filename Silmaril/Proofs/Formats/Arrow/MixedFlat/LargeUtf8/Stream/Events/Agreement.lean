module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.LargeUtf8.Events MixedFlat.LargeUtf8.Stream.Events

private theorem readNext_record {limits : MixedFlat.Limits} {framing : MixedFlat.LargeUtf8.Stream.Framing}
    {input : KBytes} {fields : List MixedFlat.LargeUtf8.Field} {fuel ordinal rows offset size : Nat}
    {batch : MixedFlat.LargeUtf8.Stream.Batch}
    (envelope : framing.readEnvelope limits.observation.ipc input offset = .ok (.metadata size))
    (read : MixedFlat.LargeUtf8.Stream.readRecord limits framing input fields rows offset size = .ok batch) :
    ∃ decoded, readNext limits framing input fields (fuel + 1) ordinal rows offset = .ok (some decoded) ∧
      decoded.record = batch := by
  simp [readNext, envelope]
  split
  next cause actual => rw [read] at actual; cases actual
  next record actual => exact ⟨_, rfl, Except.ok.inj (actual.symm.trans read)⟩

private theorem readNext_recordError {limits : MixedFlat.Limits} {framing : MixedFlat.LargeUtf8.Stream.Framing}
    {input : KBytes} {fields : List MixedFlat.LargeUtf8.Field} {fuel ordinal rows offset size : Nat}
    {cause : MixedFlat.LargeUtf8.Stream.Cause}
    (envelope : framing.readEnvelope limits.observation.ipc input offset = .ok (.metadata size))
    (read : MixedFlat.LargeUtf8.Stream.readRecord limits framing input fields rows offset size = .error cause) :
    readNext limits framing input fields (fuel + 1) ordinal rows offset = .error (.record ordinal offset cause) := by
  simp [readNext, envelope]
  split
  next failure actual =>
    have : failure = cause := Except.error.inj (actual.symm.trans read)
    subst failure
    rfl
  next record actual => rw [read] at actual; cases actual

private theorem pull_exact (limits : MixedFlat.Limits) (framing : MixedFlat.LargeUtf8.Stream.Framing)
    (input : KBytes) (fields : List MixedFlat.LargeUtf8.Field) (remaining ordinal rows offset : Nat)
    (reversed : List (Batch (schema fields))) :
    let direct := MixedFlat.LargeUtf8.Stream.readBatches limits framing input fields remaining ordinal rows offset
    let trace := Arrow.Events.BatchReader.read.pull (reader limits framing) (schema fields)
      (remaining + 1) (.at input fields remaining ordinal rows offset) reversed
    ∃ events, trace = ⟨reversed.reverse ++ events, observeTermination direct.termination⟩ ∧
      List.Forall₂ (fun record event => Agrees (schema fields) record.observed event) direct.batches events := by
  induction remaining using Nat.strongRecOn generalizing ordinal rows offset reversed with
  | ind remaining ih =>
    rw [MixedFlat.LargeUtf8.Stream.readBatches]
    cases envelope : framing.readEnvelope limits.observation.ipc input offset with
    | error cause =>
      refine ⟨[], ?_, .nil⟩
      simp [Arrow.Events.BatchReader.read.pull, reader, readNext, envelope, observeTermination,
        Except.map]
    | ok framed =>
      cases framed with
      | eos =>
        by_cases full : offset + framing.prefixSize = input.len
        · simp only [full, ite_true]
          refine ⟨[], ?_, .nil⟩
          simp [Arrow.Events.BatchReader.read.pull, reader, readNext, envelope, full, observeTermination,
            Except.map]
        · simp only [full, ite_false]
          refine ⟨[], ?_, .nil⟩
          simp [Arrow.Events.BatchReader.read.pull, reader, readNext, envelope, full, observeTermination,
            Except.map]
      | metadata size =>
        cases remaining with
        | zero =>
          refine ⟨[], ?_, .nil⟩
          simp [Arrow.Events.BatchReader.read.pull, reader, readNext, envelope, observeTermination,
            Except.map]
        | succ fuel =>
          cases decoded : MixedFlat.LargeUtf8.Stream.readRecord limits framing input fields rows offset size with
          | error cause =>
            simp only [decoded]
            refine ⟨[], ?_, .nil⟩
            have step := readNext_recordError (fuel := fuel) (ordinal := ordinal) envelope decoded
            simp [Arrow.Events.BatchReader.read.pull, reader, step, observeTermination, Except.map]
          | ok batch =>
            obtain ⟨next, step, rfl⟩ := readNext_record (fuel := fuel) (ordinal := ordinal) envelope decoded
            have adapted : (reader limits framing).next (.at input fields (fuel + 1) ordinal rows offset) =
                .ok (some (next.event, .at input fields fuel (ordinal + 1)
                  (rows + next.record.observed.rowCount) next.record.range.next)) := by
              simp [reader, step, Except.map]
            obtain ⟨events, collected, agreement⟩ := ih fuel (Nat.lt_succ_self fuel) (ordinal + 1)
              (rows + next.record.observed.rowCount) next.record.range.next (next.event :: reversed)
            simp only [decoded]
            refine ⟨next.event :: events, ?_, .cons next.aligned agreement⟩
            rw [Arrow.Events.BatchReader.read.pull, adapted]
            simpa [List.reverse_cons, List.append_assoc] using collected

private theorem direct_read (limits : MixedFlat.Limits) (framing : MixedFlat.LargeUtf8.Stream.Framing)
    (input : KBytes) :
    MixedFlat.LargeUtf8.Stream.read limits framing input =
      (admit limits framing input).map (fun (fields, start) =>
        ⟨fields, MixedFlat.LargeUtf8.Stream.readBatches limits framing input fields
          limits.observation.ipc.batches 0 0 start⟩) := by
  cases wf : input.wf <;>
    cases decoded : MixedFlat.LargeUtf8.Stream.readSchemaFrame limits.observation.ipc framing input <;>
    simp [MixedFlat.LargeUtf8.Stream.read, admit, wf, decoded, Except.map, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

theorem readAll_exact (limits : MixedFlat.Limits) (framing : MixedFlat.LargeUtf8.Stream.Framing)
    (input : KBytes) :
    match MixedFlat.LargeUtf8.Stream.read limits framing input with
    | .error cause => readAll limits framing input = .error (.schema cause)
    | .ok direct =>
      ∃ trace : Trace (schema direct.fields),
        readAll limits framing input = .ok ⟨schema direct.fields, trace⟩ ∧
        trace.termination = observeTermination direct.trace.termination ∧
        List.Forall₂ (fun record event => Agrees (schema direct.fields) record.observed event)
          direct.trace.batches trace.batches := by
  rw [direct_read]
  cases admitted : admit limits framing input with
  | error cause => simp [readAll, Arrow.Events.BatchReader.read, reader, admitted, Except.map, Except.mapError]
  | ok header =>
    obtain ⟨fields, start⟩ := header
    obtain ⟨events, collected, agreement⟩ :=
      pull_exact limits framing input fields limits.observation.ipc.batches 0 0 start []
    simp only [Except.map]
    let direct := MixedFlat.LargeUtf8.Stream.readBatches limits framing input fields
      limits.observation.ipc.batches 0 0 start
    refine ⟨⟨events, observeTermination direct.termination⟩, ?_, rfl, agreement⟩
    have opened : (reader limits framing).openInput input =
        .ok ⟨schema fields, .at input fields limits.observation.ipc.batches 0 0 start⟩ := by
      simp [reader, admitted, Except.map, Except.mapError]
    simp [readAll, Arrow.Events.BatchReader.read, opened, Except.map, collected, direct]

private theorem project_batches {signature : Signature} (projection : Scan.Projection signature)
    {records : List MixedFlat.LargeUtf8.Stream.Batch} {events : List (Batch signature)}
    (batches : List.Forall₂ (fun record event => Agrees signature record.observed event) records events) :
    List.Forall₂ (fun record event => Projects projection record.observed event)
      records (events.map projection.projectColumns) := by
  induction batches with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.project projection) ih

theorem readProjected_exact (limits : MixedFlat.Limits) (framing : MixedFlat.LargeUtf8.Stream.Framing)
    (input : KBytes) (projection : (source : Signature) → Scan.Projection source) :
    match MixedFlat.LargeUtf8.Stream.read limits framing input with
    | .error cause => readProjected limits framing input projection = .error (.schema cause)
    | .ok direct =>
      let selection := projection (schema direct.fields)
      ∃ trace : Trace selection.schema,
        readProjected limits framing input projection = .ok ⟨selection.schema, trace⟩ ∧
        trace.termination = observeTermination direct.trace.termination ∧
        List.Forall₂ (fun record event => Projects selection record.observed event)
          direct.trace.batches trace.batches := by
  have agrees := readAll_exact limits framing input
  cases direct : MixedFlat.LargeUtf8.Stream.read limits framing input with
  | error cause =>
    simp only [direct] at agrees
    simp [readProjected, agrees, Except.map]
  | ok decoded =>
    simp only [direct] at agrees
    obtain ⟨trace, read, terminal, batches⟩ := agrees
    let selection := projection (schema decoded.fields)
    refine ⟨projectTrace selection trace, ?_, terminal, ?_⟩
    · simp [readProjected, read, Except.map, selection]
    · exact project_batches selection batches

end Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events
