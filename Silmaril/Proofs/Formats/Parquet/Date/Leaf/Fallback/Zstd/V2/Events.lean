module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Arrow.DateStream.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2

open Silmaril.Formats Parquet Date.Leaf
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2
open Silmaril.Relational

theorem trace_firstError {limits : Limits} {bound : Bound} {before after : List Nat}
    {index : Nat} {groups : List Slots} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Date.Leaf.Fallback.Zstd.V2.readGroup limits bound) = .ok groups)
    (failed : Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index = .error cause) :
    Date.Leaf.Fallback.Zstd.V2.trace limits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Events.traceWith_firstError split earlier failed

theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Date.Leaf.Fallback.Zstd.V2.readGroup limits bound) = .ok groups)
    (failed : Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index = .error cause) :
    Date.Leaf.Fallback.Zstd.V2.readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ := by
  simp [Date.Leaf.Fallback.Zstd.V2.readAll, opened, trace_firstError split earlier failed, Except.map, Except.mapError]

theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Date.Leaf.Fallback.Zstd.V2.readGroup limits bound) = .ok groups)
    (failed : Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index = .error cause) :
    Date.Leaf.Fallback.Zstd.V2.toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) := by
  simp [Date.Leaf.Fallback.Zstd.V2.toIpc, opened, trace_firstError split earlier failed, Events.emitWith, Except.mapError,
    Bind.bind, Except.bind]

theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : Date.Leaf.Fallback.Zstd.V2.toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (Date.Leaf.Fallback.Zstd.V2.readGroup limits bound) = .ok groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      Date.Leaf.Fallback.Zstd.V2.readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches := by
  cases opened : openLeaf input bytes ordinal with
  | error cause =>
    simp [Date.Leaf.Fallback.Zstd.V2.toIpc, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok bound =>
    cases ended : (Date.Leaf.Fallback.Zstd.V2.trace limits bound).termination with
    | closed =>
      simp [Date.Leaf.Fallback.Zstd.V2.toIpc, opened, Events.emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | closeError cause =>
      simp [Date.Leaf.Fallback.Zstd.V2.toIpc, opened, Events.emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | readError cause =>
      simp [Date.Leaf.Fallback.Zstd.V2.toIpc, opened, Events.emitWith, ended, Except.mapError, Bind.bind, Except.bind] at written
    | eos =>
      obtain ⟨groups, decoded, sameTrace⟩ := Events.traceWith_eof (bound := bound)
        (read := Date.Leaf.Fallback.Zstd.V2.readGroup limits bound) (tag := Error.groupFailure) ended
      change Date.Leaf.Fallback.Zstd.V2.trace limits bound = _ at sameTrace
      have groupCount := (Snapshot.check_groups (Date.Leaf.open_exact opened).1).1
      have count := (List.mapM_eq_ok_iff_forall₂.mp decoded).length_eq
      simp only [List.length_range, groupCount] at count
      refine ⟨bound, groups, rfl, decoded, count.symm, ?_, ?_⟩
      · simp [Date.Leaf.Fallback.Zstd.V2.readAll, opened, sameTrace, Except.map, Except.mapError]
      · let result := Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups
        have readBack : Arrow.DateStream.read output.ipc wire = .ok result := by
          apply Events.emitWith_readback (sourceError := IpcError.source) (closed := IpcError.closed)
            (writerError := IpcError.writer)
          simpa [Date.Leaf.Fallback.Zstd.V2.toIpc, opened, sameTrace, Except.mapError, Bind.bind, Except.bind] using written
        obtain ⟨_, start, schema, batches⟩ := (Arrow.DateStream.read_iff output.ipc wire result).mp readBack
        exact ⟨result, start, readBack, rfl, by simp [result, Arrow.DateStream.Writer.observation],
          schema, batches⟩

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2
