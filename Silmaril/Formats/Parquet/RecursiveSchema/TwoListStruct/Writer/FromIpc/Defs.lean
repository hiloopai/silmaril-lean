module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Defs

/-! Strict recursive Arrow V5 IPC to the checked canonical TwoListStruct writer. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc

open Arrow.RecursiveSchema.Stream (Completed Trace)

@[expose] public section

structure Limits where
  ipc : Arrow.RecursiveSchema.Batch.Limits := {}
  parquet : Writer.Limits := {}

inductive Error where
  | openError (original : Arrow.RecursiveSchema.Error)
  | terminal (original : Trace)
  | declaration (original : Trace)
  | writer (original : Writer.Error)
  deriving Repr

/-- Keep the exact declaration and one group per complete source batch. -/
def writerInput (source : Trace) (checksum : Bool) : Writer.Input :=
  ⟨source.schema, source.batches.map Completed.observed, checksum⟩

/-- The original stream reaches exact EOS before the writer sees its
declaration or batches. A terminal failure returns the original trace. -/
def convert (limits : Limits) (input : KBytes) (checksum : Bool := false) :
    Except Error Writer.Output :=
  match Arrow.RecursiveSchema.Stream.Import.admit limits.ipc input with
  | .error (.openError cause) => .error (.openError cause)
  | .error (.terminal source) => .error (.terminal source)
  | .ok source =>
    if Writer.supportsRequiredDeclaration source.schema then
      (Writer.emit limits.parquet (writerInput source checksum)).mapError .writer
    else .error (.declaration source)

abbrev SourceWire := Arrow.RecursiveSchema.Stream.Import.SourceWire
abbrev TerminalWire := Arrow.RecursiveSchema.Stream.Import.TerminalWire

/-- The two original carriers share the strict source declaration and
every ordered batch observation, including explicit zero-row groups. -/
structure Readback (limits : Limits) (input : KBytes) (checksum : Bool)
    (output : Writer.Output) : Prop where
  original : ∃ source,
    SourceWire limits.ipc input source ∧
    Writer.emit limits.parquet (writerInput source checksum) = .ok output ∧
    Writer.Construction limits.parquet (writerInput source checksum) output ∧
    Writer.Readback limits.parquet (writerInput source checksum) output

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.FromIpc
