module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs

/-! Opt-in Snappy PLAIN BYTE_ARRAY V1/V2 export for an annotated STRING leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy

inductive PageError where
  | physical (cause : File.PageError)
  | invalidText (slot : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | openFile (cause : Utf8.Error)
  | column (cause : FlatColumn.Error PageError)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

/-- The shared callback uses the checked footer codec and exact framed body.
Each present scalar is validated as text in original logical slot order. -/
def decodePage (limits : File.Limits) (layout : FlatColumn.Layout) :
    FlatColumn.DecodePage String PageError := fun leaf metadata header body => do
  let raw ← (File.decodePage limits layout leaf metadata header body).mapError .physical
  Utf8.decodeSlotsWith PageError.invalidText raw

/-- Read the matched Snappy column from the same snapshot as the annotation.
The column walk checks both sizes and verifies the original stored CRC. -/
def readGroup {name : String} {layout : FlatColumn.Layout}
    (limits : File.Limits) (checked : Utf8.Checked name layout) (index : Nat) :
    Except (FlatColumn.Error PageError) (List (Option String)) :=
  FlatColumn.readColumnFor .snappy checked.physical.binding limits.column File.policy
    (decodePage limits layout) index

/-- CRC and scalar preparation are tied to the very same payload window.
The original slots preserve the definition mask and exact Unicode octets. -/
def PageWire (limits : File.Limits) (layout : FlatColumn.Layout) (metadata : Footer.ColumnMetadata)
    (source : Bytes) (frame : Page.Frame) (text : List (Option String)) : Prop :=
  (∃ status, Parquet.Page.Checksum.verify limits.column.maxPageBytes source frame = .ok status) ∧
  source.slice? frame.payload.start (some frame.payload.stop) = some (FlatColumn.frameBody source frame) ∧
  frame.value.compressedSize ≤ limits.column.maxPageBytes ∧
  frame.value.uncompressedSize ≤ limits.column.maxPageBytes ∧
  text.length = FlatColumn.pageSlots frame.value ∧
  File.PageWire limits layout metadata source frame
    (text.map (fun slot => slot.map (fun value => (⟨value.toByteArray⟩ : Bytes))))

def GroupWire {name : String} {layout : FlatColumn.Layout}
    (limits : File.Limits) (checked : Utf8.Checked name layout) (index : Nat)
    (group : Footer.RowGroup) (text : List (Option String)) : Prop :=
  FlatColumn.ColumnWireWith .snappy checked.physical.binding limits.column (PageWire limits layout)
    index group text

/-- Finish every selected source group before applying the IPC writer limits. -/
def convert (parquet : File.Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (name : String) (layout : FlatColumn.Layout) : Except Error KBytes := do
  let checked ← (Utf8.openFile parquet input name layout).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM
    (readGroup parquet checked)).mapError .column
  (Arrow.MixedFlat.OrderedWriter.emit ipc (Utf8.fields name layout)
    (groups.map (Utf8.batch name layout))).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy
