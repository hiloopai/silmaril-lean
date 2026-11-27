module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary

open Silmaril.Formats Parquet Date.Leaf
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary
open Silmaril.Relational

theorem trace_firstError {limits : Limits} {bound : Bound} {before after : List Nat}
    {index : Nat} {groups : List Slots} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Dictionary.readGroup limits bound) = .ok groups)
    (failed : Dictionary.readGroup limits bound index = .error cause) :
    Dictionary.trace limits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Events.traceWith_firstError split earlier failed

theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Dictionary.readGroup limits bound) = .ok groups)
    (failed : Dictionary.readGroup limits bound index = .error cause) :
    Dictionary.readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  simp [Dictionary.readAll, opened, trace_firstError split earlier failed, Except.map, Except.mapError]

theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Dictionary.readGroup limits bound) = .ok groups)
    (failed : Dictionary.readGroup limits bound index = .error cause) :
    Dictionary.toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) := by
  simp [Dictionary.toIpc, opened, trace_firstError split earlier failed, Events.emitWith, Except.mapError,
    Bind.bind, Except.bind]

theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : Dictionary.toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (Dictionary.readGroup limits bound) = .ok groups ∧
      Dictionary.readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      Arrow.DateStream.read output.ipc wire =
        .ok (Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups) := by
  cases opened : openLeaf input bytes ordinal with
  | error cause =>
    simp [Dictionary.toIpc, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    cases ended : (Dictionary.trace limits bound).termination with
    | closed =>
      simp [Dictionary.toIpc, opened, Events.emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | closeError cause =>
      simp [Dictionary.toIpc, opened, Events.emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | readError cause =>
      simp [Dictionary.toIpc, opened, Events.emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | eos =>
      obtain ⟨groups, decoded, sameTrace⟩ := Events.traceWith_eof (bound := bound)
        (read := Dictionary.readGroup limits bound) (tag := Error.groupFailure) ended
      change Dictionary.trace limits bound = _ at sameTrace
      refine ⟨bound, groups, rfl, decoded, ?_, ?_⟩
      · simp [Dictionary.readAll, opened, sameTrace, Except.map, Except.mapError]
      · apply Events.emitWith_readback (sourceError := IpcError.source) (closed := IpcError.closed)
          (writerError := IpcError.writer)
        simpa [Dictionary.toIpc, opened, sameTrace, Except.mapError, Bind.bind, Except.bind] using written

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary
