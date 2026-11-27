module

public import Silmaril.Formats.Hive.Date32.Defs
import Silmaril.Proofs.Formats.Hive.Date32

public section

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32.RowGroups

/-- The admitted present text is the canonical four-digit calendar spelling of the day. -/
theorem decodeText_ok_iff (text : String) (day : DateInterop.Date32.Payload) :
    decodeText text = .ok day ↔
      Csv.Typed.Codecs.Date32.print day = some text.toUTF8.data.toList :=
  Proofs.Formats.Hive.Date32.decodeText_ok_iff text day

/-- Bind a singleton parsed directory, converting only present DATE text. -/
theorem decodeDirectory_singleton (key : String) (options : PartitionPath.Options)
    (directory : String) (text : Option String) (nonempty : key ≠ "")
    (parsed : PartitionPath.parse options directory = .ok [(key, text)]) :
    WritePlan.decodeDirectory (partition key) options convert directory =
      ((text.mapM decodeText).mapError fun reason =>
        WritePlan.RestoreError.binding directory (.conversion key reason)).map (fun day _ => day) :=
  Proofs.Formats.Hive.Date32.decodeDirectory_singleton key options directory text nonempty parsed

/-- Once Hive has admitted the literal path and parsed its named entry, a
marker becomes null and only a present value is passed to the DATE codec. -/
theorem bindFileCells_singleton (key : String) (options : PartitionPath.Options) (file : File)
    (directory : String) (text : Option String) (nonempty : key ≠ "")
    (path : WritePlan.FlatInt32.checkFilePath (Failure := Error) file.path = .ok directory)
    (parsed : PartitionPath.parse options directory = .ok [(key, text)]) :
    bindFileCells (partition key) options convert file =
      ((text.mapM decodeText).mapError fun reason =>
        FileError.partition (.binding directory (.conversion key reason))).map (fun day _ => day) :=
  Proofs.Formats.Hive.Date32.bindFileCells_singleton key options file directory text nonempty path parsed

/-- A reached path or DATE binding failure ends the scan before the predicate
or payload for that occurrence. The prefix keeps the original batch tags. -/
theorem scanPruned_first_binding_error (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate (partition key).toScan Cell)
    (before : List File) (bad : File) (after : List File) (reason : FileError Error)
    (admitted : checkRead (Failure := Error) leaf (partition key) policy = .ok ())
    (done : ∀ item ∈ before.zipIdx,
      (Events.scanFile leaf (partition key) options convert policy limits predicate item).result = .ok ())
    (failed : bindFileCells (partition key) options convert bad = .error reason) :
    scanPruned leaf key options policy limits predicate (before ++ bad :: after) =
      .ok ⟨before.zipIdx.flatMap
        (fun item => (Events.scanFile leaf (partition key) options convert policy limits predicate item).batches),
        .error (.file before.length bad.path reason)⟩ :=
  Proofs.Formats.Hive.Date32.scanPruned_first_binding_error
    leaf key options policy limits predicate before bad after reason admitted done failed

end Silmaril.Formats.Hive.Date32
