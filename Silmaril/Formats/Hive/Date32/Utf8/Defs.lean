module

public import Silmaril.Formats.Hive.Date32.Defs
public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Defs

/-! # Checked Hive paths with one DATE key and one UTF-8 key -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32.Utf8

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

inductive Order where
  | dateFirst
  | textFirst
  deriving Repr

/-- The caller declares the virtual column order independently of the order
of segments in each literal path. Both keys are required and nullable. -/
structure Keys where
  date : String
  text : String
  order : Order

def Keys.dateField (keys : Keys) : TypedPartitions.Field Kind :=
  ⟨keys.date, .int32 .optional, .reject⟩

def Keys.textField (keys : Keys) : TypedPartitions.Field Kind :=
  ⟨keys.text, .byteArray .optional, .reject⟩

def Keys.schema (keys : Keys) : PartitionSchema Kind :=
  match keys.order with
  | .dateFirst => ⟨#[keys.dateField, keys.textField]⟩
  | .textFirst => ⟨#[keys.textField, keys.dateField]⟩

/-- Construct the typed cells at their declared positions. -/
def Keys.cells (keys : Keys) (day : Option Int32) (text : Option Bytes) :
    Scan.Row keys.schema.toScan Value := by
  rcases keys with ⟨dateName, textName, order⟩
  cases order
  · exact Fin.cases day (Fin.cases text (fun i => nomatch i))
  · exact Fin.cases text (Fin.cases day (fun i => nomatch i))

/-- DATE becomes a signed epoch day. Text becomes the UTF-8 bytes of the
already decoded path component. Marker nulls bypass both conversions. -/
def convert : TypedPartitions.Convert Value Date32.Error := fun field text =>
  match field.kind with
  | .int32 _ => Date32.decodeText text
  | .byteArray _ => .ok ⟨text.toUTF8⟩

/-- Admit every supplied literal occurrence before looking up Parquet bytes. -/
def preparePaths (int32 byteArray : Field) (keys : Keys) (options : PartitionPath.Options)
    (paths : List String) : Except (Manifest.PrepareError Date32.Error) (List (Manifest.File keys.schema Value)) :=
  Manifest.prepare (Int32ByteArrayGroup.File.schema int32 byteArray) keys.schema options convert paths

/-- Strict paired-source read after complete path admission. The projection
selects from the physical pair followed by the declared virtual columns. -/
def scanPaths {Failure : Type} {int32 byteArray : Field} {keys : Keys}
    (options : PartitionPath.Options) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (keys.schema.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate keys.schema.toScan Value) (paths : List String) :
    Except (Manifest.PrepareError Date32.Error)
      (Events.Trace projection.schema Value (Manifest.FileError (Manifest.Int32ByteArray.Error Failure))) :=
  (preparePaths int32 byteArray keys options paths).map
    (Manifest.scan (Manifest.int32ByteArraySnapshotOpener limits int32 byteArray keys.schema lookup) projection keep)

end Silmaril.Formats.Hive.Date32.Utf8
