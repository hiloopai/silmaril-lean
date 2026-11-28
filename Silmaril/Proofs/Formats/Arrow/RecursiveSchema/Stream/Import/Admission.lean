module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Import

open Silmaril.Formats.Arrow.RecursiveSchema
open Silmaril.Formats.Arrow.RecursiveSchema.Stream
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import

public theorem admit_iff {limits : Batch.Limits} {input : KBytes} {source : Trace} :
    admit limits input = .ok source ↔ read limits input = .ok source := by
  constructor
  · intro accepted
    cases decoded : readTrace limits input with
    | error => simp [admit, decoded] at accepted
    | ok trace =>
      cases terminal : trace.terminal with
      | failed => simp [admit, decoded, terminal] at accepted
      | eos ordinal offset =>
        have same : trace = source := by simpa [admit, decoded, terminal] using accepted
        subst source
        exact Stream.read_iff.mpr ⟨decoded, ordinal, offset, terminal⟩
  · intro strict
    obtain ⟨decoded, _, _, terminal⟩ := Stream.read_iff.mp strict
    simp [admit, decoded, terminal]

public theorem admit_wire {limits : Batch.Limits} {input : KBytes} {source : Trace}
    (accepted : admit limits input = .ok source) : SourceWire limits input source := by
  have strict := admit_iff.mp accepted
  obtain ⟨decoded, ordinal, offset, terminal⟩ := Stream.read_iff.mp strict
  obtain ⟨count, envelope, extent⟩ := Stream.readTrace_eos decoded terminal
  subst ordinal
  exact ⟨strict, Stream.readTrace_wire decoded, offset, terminal, envelope, extent⟩

public theorem admit_terminal_wire {limits : Batch.Limits} {input : KBytes} {source : Trace}
    (rejected : admit limits input = .error (.terminal source)) : TerminalWire limits input source := by
  cases decoded : readTrace limits input with
  | error => simp [admit, decoded] at rejected
  | ok trace =>
    cases terminal : trace.terminal with
    | eos => simp [admit, decoded, terminal] at rejected
    | failed ordinal offset cause =>
      simp only [admit, decoded, terminal, Except.error.injEq, Error.terminal.injEq] at rejected
      subst source
      obtain ⟨count, remaining, budget, failure⟩ := Stream.readTrace_failure decoded terminal
      subst ordinal
      exact ⟨decoded, Stream.readTrace_wire decoded, offset, cause, remaining, terminal, budget, failure⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Import
