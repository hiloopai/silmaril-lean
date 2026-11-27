module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc

open Silmaril.Formats
open Parquet.RecursiveSchema.Repeated
open Parquet.RecursiveSchema.Repeated.Writer.FromIpc
open Arrow.RecursiveSchema.Stream (Completed Trace)

private theorem zip_observations {batches : List Completed} {cuts : List (List (List Nat))}
    (length : cuts.length = batches.length) :
    (List.zipWith (fun (batch : Completed) sizes =>
      (⟨batch.observed, some sizes⟩ : Writer.Group)) batches cuts).map (·.data) =
      batches.map Completed.observed := by
  induction batches generalizing cuts with
  | nil => simp
  | cons batch tail ih =>
    cases cuts with
    | nil => simp at length
    | cons sizes rest => simp_all

public theorem writerInput_exact {options : Options} {source : Trace} {rows : Writer.Input}
    (bound : writerInput options source = .ok rows) :
    rows.schema = source.schema ∧ rows.observations = source.batches.map Completed.observed ∧
      rows.checksum = options.checksum := by
  unfold writerInput at bound
  cases cuts : options.cuts with
  | none =>
    simp only [cuts] at bound
    cases Except.ok.inj bound
    simp [Writer.Input.observations]
  | some cuts =>
    simp only [cuts] at bound
    split at bound
    · rename_i length
      cases Except.ok.inj bound
      exact ⟨rfl, zip_observations length, rfl⟩
    · contradiction

public theorem terminal_wire {limits : Limits} {options : Options} {input : KBytes}
    {trace : Trace} (rejected : convert limits options input = .error (.terminal trace)) :
    TerminalWire limits.ipc input trace := by
  unfold convert at rejected
  cases decoded : Arrow.RecursiveSchema.Stream.readTrace limits.ipc input with
  | error cause => simp [decoded, Except.mapError, bind, Except.bind] at rejected
  | ok source =>
    simp only [decoded, Except.mapError, bind, Except.bind] at rejected
    cases stopped : source.terminal with
    | eos ordinal offset =>
      cases bound : writerInput options source with
      | error cause =>
        simp only [stopped, bound, Except.error.injEq] at rejected
        subst cause
        unfold writerInput at bound
        split at bound
        · contradiction
        · split at bound <;> simp at bound
      | ok rows =>
        cases written : Writer.emit limits.parquet rows <;>
          simp [stopped, bound, written] at rejected
    | failed ordinal offset cause =>
      simp only [stopped, Except.error.injEq, Error.terminal.injEq] at rejected
      subst trace
      obtain ⟨count, remaining, fuel, failed⟩ :=
        Arrow.RecursiveSchema.Stream.readTrace_failure decoded stopped
      exact ⟨decoded, Arrow.RecursiveSchema.Stream.readTrace_wire decoded,
        offset, cause, remaining, by simpa [count] using stopped, by simpa [count] using fuel, failed⟩

public theorem convert_readback {limits : Limits} {options : Options} {input : KBytes}
    {output : Writer.Output} (accepted : convert limits options input = .ok output) :
    Readback limits options input output := by
  unfold convert at accepted
  cases decoded : Arrow.RecursiveSchema.Stream.readTrace limits.ipc input with
  | error cause => simp [decoded, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    simp only [decoded, Except.mapError, bind, Except.bind] at accepted
    cases stopped : source.terminal with
    | failed ordinal offset cause => simp [stopped] at accepted
    | eos ordinal offset =>
      simp only [stopped] at accepted
      cases bound : writerInput options source with
      | error cause => simp [bound] at accepted
      | ok rows =>
        simp only [bound] at accepted
        cases written : Writer.emit limits.parquet rows with
        | error cause => simp [written] at accepted
        | ok file =>
          simp only [written, Except.ok.injEq] at accepted
          subst output
          obtain ⟨count, envelope, endAt⟩ :=
            Arrow.RecursiveSchema.Stream.readTrace_eos decoded stopped
          obtain ⟨schema, observations, _⟩ := writerInput_exact bound
          obtain ⟨construction, readback⟩ := Writer.emit_wire written
          exact ⟨source, rows, ⟨decoded, Arrow.RecursiveSchema.Stream.readTrace_wire decoded,
            offset, by simpa [count] using stopped, envelope, endAt⟩,
            bound, schema, observations, written, construction, readback⟩

public theorem file {limits : Limits} {options : Options} {input : KBytes}
    {output : Writer.Output} (readback : Readback limits options input output) :
    ∃ (trace : Trace) (file : Source limits.parquet.schema.snapshot output.bytes),
      SourceWire limits.ipc input trace ∧
      openFile limits.parquet.schema.snapshot output.bytes = .ok file ∧
      file.snapshot.bytes = output.bytes ∧ file.snapshot.footer = output.footer ∧
      file.snapshot.metadata = output.metadata ∧ file.schema.arrow = trace.schema ∧
      file.snapshot.groupCount = trace.batches.length ∧
      Rows.readAll limits.parquet.rows file.schema = .ok (trace.batches.map Completed.observed) ∧
      List.Forall₂ (Rows.GroupWire limits.parquet.rows file.schema)
        (List.range file.snapshot.groupCount) (trace.batches.map Completed.observed) := by
  obtain ⟨trace, rows, source, _, originalSchema, observations, _, _, written⟩ := readback.original
  obtain ⟨file, reopened, bytes, footer, metadata, schema, count, read, groups⟩ := written.original
  have size := congrArg List.length observations
  simp only [Writer.Input.observations, List.length_map] at size
  exact ⟨trace, file, source, reopened, bytes, footer, metadata, schema.trans originalSchema,
    count.trans size, observations ▸ read, observations ▸ groups⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc
