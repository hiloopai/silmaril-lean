module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Defs

/-! Strict Arrow V5 IPC admission followed by checked signed Tree emission. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc

open Arrow.RecursiveSchema.Stream (Completed Trace)

@[expose] public section

structure Limits where
  ipc : Arrow.RecursiveSchema.Batch.Limits := {}
  parquet : Writer.Limits := {}

inductive Error where
  | openError (original : Arrow.RecursiveSchema.Error)
  | terminal (original : Trace)
  | writer (original : Writer.Error)
  deriving Repr

/-- Use the original declaration and exactly one group per completed batch. -/
def writerInput (source : Trace) (checksum : Bool) : Writer.Input :=
  ⟨source.schema, source.batches.map Completed.observed, checksum⟩

/-- Source admission reaches exact EOS before the writer can examine its
declaration, observations or limits. -/
def convert (limits : Limits) (input : KBytes) (checksum : Bool := false) :
    Except Error Writer.Output :=
  match Arrow.RecursiveSchema.Stream.Import.admit limits.ipc input with
  | .error (.openError cause) => .error (.openError cause)
  | .error (.terminal source) => .error (.terminal source)
  | .ok source => (Writer.emit limits.parquet (writerInput source checksum)).mapError .writer

abbrev SourceWire := Arrow.RecursiveSchema.Stream.Import.SourceWire
abbrev TerminalWire := Arrow.RecursiveSchema.Stream.Import.TerminalWire

/-- The exact original IPC declaration and ordered batch observations are
the model for native construction and checked original Parquet readback. -/
structure Readback (limits : Limits) (input : KBytes) (checksum : Bool)
    (output : Writer.Output) : Prop where
  original : ∃ source groups,
    SourceWire limits.ipc input source ∧
    Writer.emit limits.parquet (writerInput source checksum) = .ok output ∧
    Writer.Construction limits.parquet (writerInput source checksum) output groups ∧
    Writer.Readback limits.parquet (writerInput source checksum) output groups

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.FromIpc
