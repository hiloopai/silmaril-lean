module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.Defs
public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Defs

/-! Opt-in three-way per-group dispatch over the original opaque GZIP V2 frames. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray

abbrev Limits := V2.Limits

inductive Profile where
  | plain
  | dictionary
  | fallback
  deriving DecidableEq, Repr

/-- The original leading frame selects the PLAIN-only or dictionary-backed path.
The dictionary-backed choice uses the existing V2 tag test. -/
def profile (frames : List Page.Frame) : Profile :=
  match (ByteArrayFallback.splitLeading frames).1 with
  | none => .plain
  | some _ =>
    match V2.profile frames with
    | .dictionary => .dictionary
    | .fallback => .fallback

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  match profile frames with
  | .plain => Gzip.Plain.V2.readFrames limits metadata source group column name rows frames
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
  | .plain => Gzip.Plain.V2.FramesWire limits metadata source rows frames slots
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

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain
