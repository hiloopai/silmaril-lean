module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip.Projection

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip

open Silmaril.Formats Silmaril.Relational
open Parquet Parquet.RecursiveSchema.Tree
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature signature declarations eraseBatch ofTrace projectTrace
  declarations_signature eraseBatches_ofTrace projectTrace_id)
open Arrow.RecursiveSchema.Stream.Events.ToIpc (schemaOf schemaOf_exact)

private theorem signature_eq {left right : Signature} (same : declarations left = declarations right) :
    left = right := by
  cases left with
  | mk n first =>
    cases right with
    | mk m last =>
      change List.ofFn first = List.ofFn last at same
      have widths : n = m := by simpa only [List.length_ofFn] using congrArg List.length same
      subst m
      apply congrArg (PositionalSchema.mk n)
      funext i
      have slot := congrArg (fun entries => entries[i.val]?) same
      simpa [List.getElem?_ofFn, i.isLt] using slot

private theorem read_written_groups {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {limits : Writer.Limits}
    {start : Nat} {observations : List Observation} {groups : List Writer.WrittenGroup}
    (wire : Writer.GroupsReadback limits compiled start observations groups) :
    (List.range' start observations.length).mapM (Rows.readGroup compiled limits.reader) = .ok observations := by
  induction wire with
  | nil => rfl
  | cons head _ next =>
    obtain ⟨_, read, same, _⟩ := head
    simp [List.range'_succ, Rows.readGroup, read, Except.map, next, same, bind, Except.bind]
    rfl

public theorem ipc_projected {limits : Writer.FromIpc.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {input returned : KBytes} {checksum : Bool} {output : Writer.Output}
    {selection : (source : Signature) → Scan.Projection source}
    (imported : Writer.FromIpc.convert limits input checksum = .ok output)
    (exported : Rows.Events.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.reader
      ipc output.bytes selection = .ok returned) :
    ∃ (source : Arrow.RecursiveSchema.Stream.Trace)
      (original : Writer.FromIpc.SourceWire limits.ipc input source),
      let view := selection (signature source.schema.fields)
      Arrow.RecursiveSchema.Stream.Writer.Readback ipc (schemaOf view.schema)
        ((projectTrace view (ofTrace source original.wire)).batches.map eraseBatch) returned := by
  obtain ⟨source, _, original, _, _, readback⟩ := (Writer.FromIpc.convert_readback imported).original
  obtain ⟨expected, opened, _, declaration, _, _, groupCount, checked⟩ := readback.original
  obtain ⟨events, _, completed, result⟩ := (Rows.Events.ToIpc.convert_readback exported).original
  obtain ⟨sig, trace, actual, reopened, native, selected, _, batches, terminal⟩ := completed.selected.original
  have sameFile : actual = expected := Except.ok.inj (reopened.symm.trans opened)
  subst actual
  have sameSignature : sig = signature source.schema.fields := by
    apply signature_eq
    rw [declarations_signature]
    have fields := native.logical.fieldsExact
    change declarations sig = expected.schema.arrow.fields.map _ at fields
    rw [declaration] at fields
    exact fields
  subst sig
  have nativeBatches := native.logical.completed.complete.mp (terminal.symm.trans completed.terminal)
  change (List.range expected.snapshot.groupCount).mapM
      (Rows.readGroup expected.schema limits.parquet.reader) = .ok (trace.batches.map eraseBatch) at nativeBatches
  rw [groupCount, List.range_eq_range'] at nativeBatches
  have sameBatches : trace.batches.map eraseBatch = source.batches.map Arrow.RecursiveSchema.Stream.Completed.observed :=
    Except.ok.inj (nativeBatches.symm.trans (read_written_groups checked))
  rw [batches, sameBatches, selected] at result
  exact ⟨source, original, by
    simpa only [Rows.Events.projected_observations, eraseBatches_ofTrace] using result⟩

public theorem ipc_identity {limits : Writer.FromIpc.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {input returned : KBytes} {checksum : Bool} {output : Writer.Output}
    (imported : Writer.FromIpc.convert limits input checksum = .ok output)
    (exported : Rows.Events.ToIpc.convert limits.parquet.schema.snapshot limits.parquet.reader
      ipc output.bytes = .ok returned) :
    ∃ source, Writer.FromIpc.SourceWire limits.ipc input source ∧
      Arrow.RecursiveSchema.Stream.Writer.Readback ipc source.schema
        (source.batches.map Arrow.RecursiveSchema.Stream.Completed.observed) returned := by
  obtain ⟨source, original, roundTrip⟩ := ipc_projected imported exported
  have schema : schemaOf (signature source.schema.fields) = source.schema :=
    schemaOf_exact (declarations_signature source.schema.fields)
  change Arrow.RecursiveSchema.Stream.Writer.Readback ipc (schemaOf (signature source.schema.fields))
    ((projectTrace (Scan.Projection.id _) (ofTrace source original.wire)).batches.map eraseBatch) returned at roundTrip
  rw [schema, projectTrace_id] at roundTrip
  change Arrow.RecursiveSchema.Stream.Writer.Readback ipc source.schema
    ((ofTrace source original.wire).batches.map eraseBatch) returned at roundTrip
  rw [eraseBatches_ofTrace] at roundTrip
  exact ⟨source, original, roundTrip⟩

public theorem parquet_identity {schemaLimits : Snapshot.Limits} {rows : Rows.Limits}
    {limits : Writer.FromIpc.Limits} {input : Bytes} {wire : KBytes} {checksum : Bool} {output : Writer.Output}
    (exported : Rows.Events.ToIpc.convert schemaLimits rows limits.ipc input = .ok wire)
    (imported : Writer.FromIpc.convert limits wire checksum = .ok output) :
    ∃ before after, Parquet.RecursiveSchema.Tree.openFile schemaLimits input = .ok before ∧
      Parquet.RecursiveSchema.Tree.openFile limits.parquet.schema.snapshot output.bytes = .ok after ∧
      after.schema.arrow = before.schema.arrow ∧ after.snapshot.groupCount = before.snapshot.groupCount ∧
      ∀ ordinal < before.snapshot.groupCount, ∃ left right,
        Rows.readGroupChecked before.schema rows ordinal = .ok left ∧
        Rows.readGroupChecked after.schema limits.parquet.reader ordinal = .ok right ∧
        left.observation = right.observation ∧
        left.inputs.map (·.original.atoms) = right.inputs.map (·.original.atoms) := by
  obtain ⟨events, _, completed, result⟩ := (Rows.Events.ToIpc.convert_readback exported).original
  obtain ⟨sig, trace, before, openBefore, native, selected, _, _, _⟩ := completed.selected.original
  have fullBatches : events.2.batches.map eraseBatch = trace.batches.map eraseBatch := by
    rw [selected, projectTrace_id]
    rfl
  have fullSchema : schemaOf events.1 = before.schema.arrow := by
    rw [selected]
    exact schemaOf_exact native.logical.fieldsExact
  obtain ⟨_, counted, countedOpen, allGroups⟩ := completed.groups
  have sameFile : counted = before := Except.ok.inj (countedOpen.symm.trans openBefore)
  subst counted
  have groupCount : trace.batches.length = before.snapshot.groupCount := by
    simpa [fullBatches] using allGroups.length_eq.symm
  obtain ⟨emitted, _, strict, _, declaration, batches, _, _, _⟩ := result.result
  rw [fullSchema] at declaration
  rw [fullBatches] at batches
  obtain ⟨source, _, original, _, _, target⟩ := (Writer.FromIpc.convert_readback imported).original
  have sameTrace : source = emitted := Except.ok.inj (original.checked.symm.trans strict)
  subst source
  obtain ⟨after, openAfter, _, targetSchema, _, _, targetCount, targetGroups⟩ := target.original
  have schema : after.schema.arrow = before.schema.arrow := targetSchema.trans declaration
  have count : after.snapshot.groupCount = before.snapshot.groupCount := by
    simpa only [Writer.FromIpc.writerInput, batches, List.length_map, groupCount] using targetCount
  refine ⟨before, after, openBefore, openAfter, schema, count, ?_⟩
  intro ordinal bound
  have all := native.groups
  have takeAll : (List.range before.snapshot.groupCount).take trace.batches.length =
      List.range before.snapshot.groupCount := List.take_of_length_le (by simp [groupCount])
  rw [takeAll] at all
  let observations := trace.batches.map eraseBatch
  have atObservation : ordinal < observations.length := by simpa [observations, groupCount] using bound
  have beforeRead : Rows.Events.CheckedRead rows before.schema ordinal observations[ordinal] := by
    simpa only [List.getElem_range, List.get_eq_getElem] using all.get
      (i := ordinal) (by simpa using bound) atObservation
  have afterRead : (Writer.FromIpc.writerInput emitted checksum).groups[ordinal]? =
      some observations[ordinal] := by
    change (emitted.batches.map Arrow.RecursiveSchema.Stream.Completed.observed)[ordinal]? = _
    rw [batches]
    exact List.getElem?_eq_getElem atObservation
  obtain ⟨left, originalRead, originalRows⟩ := beforeRead
  obtain ⟨_, _, group⟩ := targetGroups.group_at afterRead
  simp only [Nat.zero_add] at group
  obtain ⟨right, targetRead, targetRows, _⟩ := group
  have equal := originalRows.trans targetRows.symm
  exact ⟨left, right, originalRead, targetRead, equal, signed_traces_eq originalRead targetRead schema.symm equal⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip
