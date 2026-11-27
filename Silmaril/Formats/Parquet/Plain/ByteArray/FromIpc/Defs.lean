module

public import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs

/-! One checked BinaryView IPC field to one unannotated PLAIN V1
BYTE_ARRAY Parquet row group. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc

open Arrow.BinaryView

structure Source where
  name : String
  nullable : Bool
  batches : List (List (Option KBytes))

def Source.observed (source : Source) : Stream.Observed :=
  ⟨⟨source.name, source.nullable, .binary⟩, source.batches⟩

def Source.layout (source : Source) : FlatColumn.Layout :=
  if source.nullable then .optional else .required

def Source.slots (source : Source) : List (Option Bytes) :=
  source.batches.flatten.map (Option.map (Bytes.ofList ∘ KBytes.toList))

inductive Error where
  | source (cause : Stream.Error)
  | expectedBinaryView
  | requiredSlot
  | writer (cause : PlainByteArrayV1Writer.File.Error)
  deriving DecidableEq, Repr

/-- Read the original native stream through exact EOS under its own limits. -/
def readSource (ipc : Arrow.Limits) (view : Column.Limits) (input : KBytes) :
    Except Error Source := do
  let source ← (Stream.read ipc view input).mapError .source
  match source with
  | ⟨⟨name, nullable, .binary⟩, batches⟩ => return ⟨name, nullable, batches⟩
  | ⟨⟨_, _, .utf8⟩, _⟩ => throw .expectedBinaryView

/-- Fully exhaust the source, then offer its ordered slots to the checked
singleton writer. Every success has one group, including schema-only input. -/
def convert (ipc : Arrow.Limits) (view : Column.Limits) (limits : PlainByteArrayV1Writer.File.Limits)
    (input : KBytes) : Except Error PlainByteArrayV1Writer.File.Encoded := do
  let source ← readSource ipc view input
  let some prepared := PlainByteArrayV1Writer.File.Input.ofSlots source.name source.layout source.slots
    | throw .requiredSlot
  (PlainByteArrayV1Writer.File.emit limits prepared).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc
