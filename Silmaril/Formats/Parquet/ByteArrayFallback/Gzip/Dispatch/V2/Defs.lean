module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.Defs
public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Defs

/-! Opt-in per-group dispatch over the original opaque GZIP V2 frames. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2

open Arrow.BinaryView
open Plain.ByteArray

abbrev Limits := Dictionary.Limits

def isPlainV2 (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 header => header.encoding == 0
  | _ => false

/-- A recorded V2 PLAIN header selects fallback. The selected reader checks
admission and supplies its own result, including any typed failure. -/
def profile (frames : List Page.Frame) : Dispatch.Profile :=
  if frames.any isPlainV2 then .fallback else .dictionary

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  match profile frames with
  | .dictionary => Dictionary.V2.readFrames limits metadata source group column name rows frames
  | .fallback => Fallback.V2.readFrames limits metadata source group column name rows frames

/-- Frame the selected chunk once and pass the unmodified frames to one strict reader. -/
def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .gzip limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toSnappyLimits.toLimits (readFrames limits) index

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  match profile frames with
  | .dictionary => Dictionary.V2.FramesWire limits metadata source rows frames slots
  | .fallback => Fallback.V2.FramesWire limits metadata source rows frames slots

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .gzip checked.physical.binding limits.toSnappyLimits.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Export one native BinaryView batch per successfully checked original group through EOS. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Snappy.Error KBytes :=
  Snappy.convertWith parquet.toSnappyLimits ipc view input name (readGroup parquet)

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2
