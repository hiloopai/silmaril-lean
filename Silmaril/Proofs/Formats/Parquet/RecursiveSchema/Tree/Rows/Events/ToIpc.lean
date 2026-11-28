module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc

open Silmaril.Formats
open Silmaril.Relational
open Parquet Parquet.RecursiveSchema.Tree
open Parquet.RecursiveSchema.Tree.Rows.Events (Trace ProjectedWire readProjected readProjected_wire)
open Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch fieldName)
open Arrow.RecursiveSchema.Stream.Events.ToIpc (emit schemaOf)

private theorem eos_length {Group Failure Error : Type} {read : Group → Except Failure Arrow.RecursiveSchema.Batch.Rows.Observation}
    {report : Group → Failure → Error} {order : List Group} {batches : List Arrow.RecursiveSchema.Batch.Rows.Observation}
    {terminal : Arrow.Events.Termination Error}
    (witness : Parquet.Reader.Recursive.Prefix read report order batches terminal) :
    terminal = .eos → batches.length = order.length := by
  induction witness with
  | eos => exact fun _ => rfl
  | failed _ => intro ending; cases ending
  | more _ _ ih => intro ending; simp [ih ending]

private theorem completed {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    (accepted : readProjected schemaLimits limits input selection = .ok events)
    (ending : events.2.termination = .eos) : Completed schemaLimits limits input selection events := by
  have wire := readProjected_wire accepted
  refine ⟨wire, ending, ?_⟩
  obtain ⟨source, opened, admitted, groups⟩ := wire.groups
  obtain ⟨_, trace, actual, openedExact, original, _, _, batches, terminal⟩ := wire.original
  have same : actual = opened := Except.ok.inj (openedExact.symm.trans admitted)
  subst actual
  have checkedCount := eos_length original.logical.completed (terminal.symm.trans ending)
  change (trace.batches.map eraseBatch).length = (List.range opened.snapshot.groupCount).length at checkedCount
  have selectedCount : events.2.batches.length = trace.batches.length := by
    simpa only [List.length_map] using congrArg List.length batches
  rw [selectedCount, ← List.length_map (f := eraseBatch), checkedCount, List.take_length] at groups
  exact ⟨source, opened, admitted, groups⟩

private theorem selected_names {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    (wire : ProjectedWire schemaLimits limits input selection events) :
    declarations events.1 = (schemaOf events.1).fields.map (fun field => (fieldName field, field)) := by
  obtain ⟨source, _, _, _, original, _, declared, _, _⟩ := wire.original
  have names (i : Fin source.width) : (source.kind i).1 = fieldName (source.kind i).2 := by
    have member : source.kind i ∈ declarations source := List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [original.logical.fieldsExact] at member
    obtain ⟨field, _, equality⟩ := List.mem_map.mp member
    simp [← equality]
  simp only [schemaOf, declared, List.map_ofFn, Function.comp_def]
  exact congrArg List.ofFn (funext fun i => Prod.ext (names ((selection source).index i)) rfl)

public theorem convert_readback {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    Readback schemaLimits limits ipc input selection wire := by
  cases projected : readProjected schemaLimits limits input selection with
  | error cause => simp [convert, projected, emit] at written
  | ok events =>
    obtain ⟨source, trace⟩ := events
    obtain ⟨ending, certificate⟩ := Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_readback
      (by simpa [convert, projected] using written)
    exact ⟨⟨source, trace⟩, projected, completed projected ending, certificate⟩

public theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {wire : KBytes}
    {selected : Σ source : Signature, Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (projected : readProjected schemaLimits limits input selection = .ok selected)
    (written : convert schemaLimits limits ipc input selection = .ok wire)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc wire = .ok native) :
    declarations native.1 = declarations selected.1 ∧
      native.2.batches.map eraseBatch = selected.2.batches.map eraseBatch ∧ native.2.termination = .eos := by
  obtain ⟨source, trace⟩ := selected
  exact Arrow.RecursiveSchema.Stream.Events.ToIpc.agrees_events (selected_names (readProjected_wire projected))
    (by simpa [convert, projected] using written) readback

public theorem convert_group_failure {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {ordinal : Nat} {cause : Rows.Error}
    {completedBatches : List Arrow.RecursiveSchema.Batch.Rows.Observation}
    (refused : convert schemaLimits limits ipc input selection = .error (.readError (.group ordinal cause) completedBatches)) :
    ∃ events, readProjected schemaLimits limits input selection = .ok events ∧
      ProjectedWire schemaLimits limits input selection events ∧
      events.2.termination = .readError (.group ordinal cause) ∧ events.2.batches.map eraseBatch = completedBatches ∧
      ordinal = completedBatches.length ∧
      ∃ opened, Parquet.RecursiveSchema.Tree.openFile schemaLimits input = .ok opened ∧
        Rows.readGroupChecked opened.schema limits ordinal = .error cause := by
  cases projected : readProjected schemaLimits limits input selection with
  | error original => simp [convert, projected, emit] at refused
  | ok events =>
    obtain ⟨source, trace⟩ := events
    cases ending : trace.termination with
    | closed => simp [convert, projected, emit, ending] at refused
    | closeError original => simp [convert, projected, emit, ending] at refused
    | eos =>
      cases writer : Arrow.RecursiveSchema.Stream.Writer.emit ipc (schemaOf source) (trace.batches.map eraseBatch) <;>
        simp [convert, projected, emit, ending, writer, Except.mapError] at refused
    | readError original =>
      obtain ⟨originalEq, exactPrefix⟩ : original = .group ordinal cause ∧ trace.batches.map eraseBatch = completedBatches := by
        simpa [convert, projected, emit, ending] using refused
      have wire := readProjected_wire projected
      have failed := ending.trans (congrArg Arrow.Events.Termination.readError originalEq)
      obtain ⟨reached, native⟩ := Rows.Events.projected_failure wire failed
      have count : trace.batches.length = completedBatches.length := by
        simpa only [List.length_map] using congrArg List.length exactPrefix
      exact ⟨⟨source, trace⟩, rfl, wire, failed, exactPrefix, reached.trans count, native⟩

public theorem convert_writer_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {cause : Arrow.RecursiveSchema.Stream.Writer.Error}
    (refused : convert schemaLimits limits ipc input selection = .error (.writer cause)) :
    ∃ events, readProjected schemaLimits limits input selection = .ok events ∧
      Completed schemaLimits limits input selection events ∧
      Arrow.RecursiveSchema.Stream.Writer.emit ipc (schemaOf events.1)
        (events.2.batches.map eraseBatch) = .error cause := by
  cases projected : readProjected schemaLimits limits input selection with
  | error original => simp [convert, projected, emit] at refused
  | ok events =>
    obtain ⟨source, trace⟩ := events
    cases ending : trace.termination with
    | closed => simp [convert, projected, emit, ending] at refused
    | readError original => simp [convert, projected, emit, ending] at refused
    | closeError original => simp [convert, projected, emit, ending] at refused
    | eos =>
      cases written : Arrow.RecursiveSchema.Stream.Writer.emit ipc (schemaOf source) (trace.batches.map eraseBatch) with
      | ok output => simp [convert, projected, emit, ending, written, Except.mapError] at refused
      | error original =>
        have same : original = cause := by
          simpa [convert, projected, emit, ending, written, Except.mapError] using refused
        exact ⟨⟨source, trace⟩, rfl, completed projected ending, same ▸ written⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc
