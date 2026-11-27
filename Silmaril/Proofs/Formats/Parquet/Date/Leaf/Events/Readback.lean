module

public import Silmaril.Formats.Parquet.Date.Leaf.Events.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.DateStream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Events

open Silmaril.Formats Parquet Date.Leaf Date.Leaf.Events
open Silmaril.Relational

variable {ε δ : Type} {bound : Bound} {read : Nat → Except ε Slots} {tag : Nat → ε → δ}

private theorem denote_prefix {indices : List Nat} {groups : List Slots}
    (decoded : indices.mapM read = .ok groups) (rest : List Nat) :
    Reader.denoteGroups (rowsAtWith bound read tag) (indices ++ rest) =
      let tail := Reader.denoteGroups (rowsAtWith bound read tag) rest
      (groups.map (rows bound) ++ tail.1, tail.2) := by
  induction indices generalizing groups with
  | nil =>
    simp [Pure.pure, Except.pure] at decoded
    subst groups
    rfl
  | cons index indices ih =>
    cases first : read index with
    | error cause => simp [List.mapM_cons, first, Bind.bind, Except.bind] at decoded
    | ok slots =>
      cases more : indices.mapM read with
      | error cause => simp [List.mapM_cons, first, more, Bind.bind, Except.bind] at decoded
      | ok tail =>
        have same : slots :: tail = groups := by
          simpa [List.mapM_cons, first, more, Bind.bind, Except.bind, Pure.pure, Except.pure] using decoded
        subst groups
        simp [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError, ih more]

private theorem mapM_of_eof (indices : List Nat)
    (eof : (Reader.denoteGroups (rowsAtWith bound read tag) indices).2 = .eos) :
    ∃ groups, indices.mapM read = .ok groups := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index indices ih =>
    cases first : read index with
    | error cause =>
      simp [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError] at eof
    | ok slots =>
      have following : (Reader.denoteGroups (rowsAtWith bound read tag) indices).2 = .eos := by
        simpa [Reader.denoteGroups, rowsAtWith, first, Except.map, Except.mapError] using eof
      obtain ⟨groups, tail⟩ := ih following
      exact ⟨slots :: groups, by simp [List.mapM_cons, first, tail, Bind.bind, Except.bind,
        Pure.pure, Except.pure]⟩

theorem traceWith_firstError {before after : List Nat} {index : Nat} {groups : List Slots} {cause : ε}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM read = .ok groups) (failed : read index = .error cause) :
    traceWith bound read tag =
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (tag index cause)⟩ := by
  simp [traceWith, split, denote_prefix earlier, Reader.denoteGroups, rowsAtWith, failed,
    Except.map, Except.mapError, List.map_map]

theorem traceWith_eof (ended : (traceWith bound read tag).termination = .eos) :
    ∃ groups, (List.range bound.snapshot.groupCount).mapM read = .ok groups ∧
      traceWith bound read tag = ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .eos⟩ := by
  obtain ⟨groups, decoded⟩ := mapM_of_eof _ ended
  have ordered := denote_prefix (bound := bound) (tag := tag) decoded []
  rw [List.append_nil] at ordered
  exact ⟨groups, decoded, by simp [traceWith, ordered, Reader.denoteGroups, List.map_map]⟩

theorem emitWith_readback {output : Arrow.ObservationLimits} {sourceError : ε → δ}
    {closed : δ} {writerError : Arrow.DateStream.Writer.Error → δ} {groups : List Slots}
    {wire : KBytes} (emitted : emitWith output bound sourceError closed writerError
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .eos⟩ = .ok wire) :
    Arrow.DateStream.read output.ipc wire =
      .ok (Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups) := by
  have mapped : (Arrow.DateStream.Writer.emit output bound.binding.leaf.name bound.nullable
      groups).mapError writerError = .ok wire := by
    simpa [emitWith, rows, AlignedColumns.ofRows, Function.comp_def, List.map_map] using emitted
  cases wrote : Arrow.DateStream.Writer.emit output bound.binding.leaf.name bound.nullable groups with
  | error cause => simp [wrote, Except.mapError] at mapped
  | ok wire' =>
    have exactWire : wire' = wire := by simpa [wrote, Except.mapError] using mapped
    exact exactWire ▸ Arrow.DateStream.Writer.emit_readback wrote

theorem readAll_reference {limits : Date.Limits} {ordinal : Nat} {input : Bytes} {bound : Bound}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound) :
    readAll limits ordinal input = .ok ⟨schema bound, trace limits bound⟩ := by
  unfold readAll
  have ready : openSource limits ordinal input = .ok ⟨schema bound, source limits bound⟩ := by
    simp [openSource, opened, Except.mapError, Except.map]
  rw [ready, Reader.readAll_opened]
  rfl

theorem trace_firstError {limits : Date.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : Date.Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    trace limits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .readError (.groupFailure index cause)⟩ :=
  traceWith_firstError split earlier failed

theorem toIpc_firstError {limits : Date.Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : Date.Leaf.Error}
    (opened : openLeaf limits.snapshot input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc limits output ordinal input = .error (.source (.groupFailure index cause)) := by
  simp [toIpc, opened, emit, emitWith, trace_firstError split earlier failed, Except.mapError,
    Bind.bind, Except.bind]

theorem toIpc_readback {limits : Date.Limits} {output : Arrow.ObservationLimits} {ordinal : Nat}
    {input : Bytes} {wire : KBytes} (written : toIpc limits output ordinal input = .ok wire) :
    ∃ bound groups, openLeaf limits.snapshot input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      readAll limits ordinal input = .ok ⟨schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ rows bound), .eos⟩⟩ ∧
      Arrow.DateStream.read output.ipc wire =
        .ok (Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups) := by
  cases opened : openLeaf limits.snapshot input ordinal with
  | error cause => simp [toIpc, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    cases ended : (trace limits bound).termination with
    | closed => simp [toIpc, opened, emit, emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | closeError cause =>
      simp [toIpc, opened, emit, emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | readError cause =>
      simp [toIpc, opened, emit, emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | eos =>
      obtain ⟨groups, decoded, sameTrace⟩ :=
        traceWith_eof (bound := bound) (read := readGroup limits bound) (tag := Error.groupFailure) ended
      change trace limits bound = _ at sameTrace
      refine ⟨bound, groups, rfl, decoded, (readAll_reference opened).trans ?_, ?_⟩
      · rw [sameTrace]
      · apply emitWith_readback (sourceError := IpcError.source) (closed := IpcError.closed)
          (writerError := IpcError.writer)
        simpa [toIpc, opened, emit, sameTrace, Except.mapError, Bind.bind, Except.bind] using written

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Events
