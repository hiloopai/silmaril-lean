module

public import Silmaril.Formats.Hive.Date32.Utf8.Defs
import Silmaril.Formats.Hive.Manifest.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Thms
import Silmaril.Proofs.Formats.Hive.Date32.Utf8

public section

namespace Silmaril.Formats.Hive.Date32.Utf8

open Silmaril.Relational Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Value)

theorem Keys.schema_order (keys : Keys) :
    keys.schema.keys = match keys.order with
      | .dateFirst => [keys.date, keys.text]
      | .textFirst => [keys.text, keys.date] := by
  rcases keys with ⟨_, _, order⟩
  cases order <;> rfl

/-- After the shared key checks, decode in declaration order. Every
successful nullable value is placed at its declared position. -/
theorem decode_eq_fields (keys : Keys) (entries : PartitionPath.Partition)
    (valid : PartitionPath.validateKeys (entries.map Prod.fst) = .ok ())
    (known : ∀ entry ∈ entries, entry.1 = keys.date ∨ entry.1 = keys.text) :
    TypedPartitions.decode keys.schema convert entries =
      (match keys.order with
      | .dateFirst => do
        let day ← TypedPartitions.decodeField convert entries keys.dateField
        let text ← TypedPartitions.decodeField convert entries keys.textField
        pure (keys.cells day text)
      | .textFirst => do
        let text ← TypedPartitions.decodeField convert entries keys.textField
        let day ← TypedPartitions.decodeField convert entries keys.dateField
        pure (keys.cells day text)) :=
  Proofs.Formats.Hive.Date32.Utf8.decode_eq_fields keys entries valid known

theorem convert_date (keys : Keys) (text : String) :
    convert keys.dateField text = Date32.decodeText text := rfl

theorem convert_text (keys : Keys) (text : String) :
    convert keys.textField text = .ok ⟨text.toUTF8⟩ := rfl

/-- Successful admission preserves literal occurrence order, including repeats. -/
theorem preparePaths_paths (int32 byteArray : Field) (keys : Keys) (options : PartitionPath.Options)
    {paths : List String} {files : List (Manifest.File keys.schema Value)}
    (admitted : preparePaths int32 byteArray keys options paths = .ok files) :
    files.map (·.path.declared) = paths :=
  Manifest.prepare_preserves_paths options convert admitted

/-- The first binding failure after an admitted prefix keeps its literal path
and typed cause. Later declarations have no effect. -/
theorem preparePaths_first_binding_error (int32 byteArray : Field) (keys : Keys)
    (options : PartitionPath.Options) (before : List String) (bad : String) (after : List String)
    (cause : TypedPartitions.Error Date32.Error)
    {files : List (Manifest.File keys.schema Value)}
    (prefixOk : preparePaths int32 byteArray keys options before = .ok files)
    (failed : Manifest.prepareFile keys.schema options convert bad = .error (.binding bad cause)) :
    preparePaths int32 byteArray keys options (before ++ bad :: after) = .error (.binding bad cause) :=
  Proofs.Formats.Hive.Date32.Utf8.preparePaths_first_binding_error int32 byteArray keys options
    before bad after cause prefixOk failed

/-- A failed admission is returned before the resolver or projection is used. -/
theorem scanPaths_admission_error {Failure : Type} {int32 byteArray : Field} {keys : Keys}
    (options : PartitionPath.Options) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (keys.schema.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate keys.schema.toScan Value) (paths : List String)
    {cause : Manifest.PrepareError Date32.Error}
    (failed : preparePaths int32 byteArray keys options paths = .error cause) :
    scanPaths options limits lookup projection keep paths = .error cause := by
  simp [scanPaths, failed, Except.map]

/-- The checked reader observes the independent ordered group fold at the
requested projection, including repeated or empty projection positions. -/
theorem scanPaths_eq_reference {Failure : Type} {int32 byteArray : Field} {keys : Keys}
    (options : PartitionPath.Options) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (keys.schema.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate keys.schema.toScan Value)
    {paths : List String} {files : List (Manifest.File keys.schema Value)}
    (admitted : preparePaths int32 byteArray keys options paths = .ok files) :
    scanPaths options limits lookup projection keep paths =
      .ok (Manifest.denoteInt32ByteArraySnapshots limits lookup projection keep files) := by
  simp [scanPaths, admitted, Except.map, Manifest.scanInt32ByteArraySnapshots_eq_reference]

end Silmaril.Formats.Hive.Date32.Utf8
