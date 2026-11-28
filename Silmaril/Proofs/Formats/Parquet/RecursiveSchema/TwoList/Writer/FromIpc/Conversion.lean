module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc

open Silmaril.Formats
open Parquet.RecursiveSchema.TwoList.Writer.FromIpc
open Parquet.RecursiveSchema.TwoList
open Arrow.RecursiveSchema hiding Limits Error

public theorem convert_terminal_wire {limits : Limits} {input : KBytes} {checksum : Bool}
    {source : Stream.Trace} (rejected : convert limits input checksum = .error (.terminal source)) :
    TerminalWire limits.ipc input source := by
  unfold convert at rejected
  cases decoded : Stream.readTrace limits.ipc input with
  | error cause => simp [decoded, Except.mapError, bind, Except.bind] at rejected
  | ok trace =>
    simp only [decoded, Except.mapError, bind, Except.bind] at rejected
    cases terminal : trace.terminal with
    | eos ordinal offset =>
      cases written : Writer.emit limits.parquet (writerInput trace checksum) <;>
        simp [terminal, written] at rejected
    | failed ordinal offset cause =>
      simp only [terminal, Except.error.injEq, Error.terminal.injEq] at rejected
      subst source
      obtain ⟨count, remaining, budget, failure⟩ := Stream.readTrace_failure decoded terminal
      subst ordinal
      exact ⟨decoded, Stream.readTrace_wire decoded, offset, cause, remaining, terminal, budget, failure⟩

public theorem convert_readback {limits : Limits} {input : KBytes} {checksum : Bool}
    {output : Writer.Output} (accepted : convert limits input checksum = .ok output) :
    Readback limits input checksum output := by
  unfold convert at accepted
  cases decoded : Stream.readTrace limits.ipc input with
  | error cause => simp [decoded, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    simp only [decoded, Except.mapError, bind, Except.bind] at accepted
    cases terminal : source.terminal with
    | failed ordinal offset cause => simp [terminal] at accepted
    | eos ordinal offset =>
      cases written : Writer.emit limits.parquet (writerInput source checksum) with
      | error cause => simp [terminal, written] at accepted
      | ok file =>
        simp only [terminal, written, Except.ok.injEq] at accepted
        subst output
        obtain ⟨count, envelope, extent⟩ := Stream.readTrace_eos decoded terminal
        have strict := Stream.read_iff.mpr ⟨decoded, ordinal, offset, terminal⟩
        subst ordinal
        exact ⟨source, ⟨strict, Stream.readTrace_wire decoded, offset, terminal, envelope, extent⟩,
          written, Writer.emit_wire written⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc
