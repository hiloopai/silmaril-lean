module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs

/-! Opt-in Zstandard PLAIN V1 data for a strictly selected flat DATE leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Zstd

open FlatColumn.Zstd (CompressionLimits)

structure Limits where
  pages : Gzip.Limits := {}
  compression : CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

inductive GroupError where
  | plan (cause : Gzip.GroupError)
  | checksum (page offset : Nat) (cause : Page.Checksum.Error)
  | decode (page offset : Nat) (cause : FlatColumn.Zstd.Error)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

def columnLayout (bound : Bound) : FlatColumn.Layout :=
  if bound.nullable then .optional else .required

def columnLimits (limits : Limits) : FlatColumn.Zstd.Limits :=
  ⟨⟨limits.pages.framing, limits.pages.maxStoredChunkBytes,
    limits.pages.scalar.compressedBytes, limits.pages.maxRows⟩, limits.pages.scalar, limits.compression⟩

abbrev planData (bound : Bound) (frame : Page.Frame) : Except Gzip.PageError Gzip.DataPage :=
  Gzip.planDataFor .zstd bound frame

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except GroupError Gzip.CheckedGroup :=
  Gzip.checkGroupFor .zstd .plan (fun frame ordinal =>
    (planData bound frame).mapError (.plan ∘ Gzip.atFrame ordinal frame)) limits.pages bound index

abbrev GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : Gzip.CheckedGroup) :=
  Gzip.GroupWire limits.pages bound index checked (fun page => planData bound page.frame = .ok page) .zstd

/-- Verify the optional outer CRC on the original full V1 payload before
passing the same bytes to the checked single-frame Zstandard decoder. -/
def decodePage (limits : Limits) (bound : Bound) (metadata : Footer.ColumnMetadata)
    (page : Gzip.DataPage) (ordinal : Nat) : Except GroupError Slots := do
  let frame := page.frame
  let source := bound.snapshot.bytes
  let _ ← (Page.Checksum.verify limits.pages.scalar.compressedBytes source frame).mapError
    (.checksum ordinal frame.header.start)
  (FlatColumn.Zstd.decodePage (columnLimits limits) (columnLayout bound) bound.binding.leaf
    metadata frame.value (Page.Checksum.payloadBytes source frame)).mapError
      (.decode ordinal frame.header.start)

def PageWire (limits : Limits) (bound : Bound) (metadata : Footer.ColumnMetadata)
    (page : Gzip.DataPage) (slots : Slots) : Prop :=
  (∃ status, Page.Checksum.verify limits.pages.scalar.compressedBytes bound.snapshot.bytes page.frame = .ok status) ∧
    FlatColumn.Zstd.PageWire (columnLimits limits) (columnLayout bound) metadata page.frame.value
      (Page.Checksum.payloadBytes bound.snapshot.bytes page.frame) slots

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← checked.data.zipIdx.mapM fun (page, ordinal) =>
    decodePage limits bound checked.selection.column.metadata page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete Date32 IPC after the checked selected leaf reaches EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Zstd
