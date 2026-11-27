module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Defs
public import Silmaril.Formats.Relational.NamedTable.Defs

/-! Atomic named-table import from selected native DATE/UTF-8 Hive files. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Date32.Utf8.ManifestWriter (File Limits ReadError Schema readSelected)
open Int32ByteArrayGroup.File (Kind Value)

inductive SourceError where
  | admission (reason : Manifest.PrepareError Date32.Error)
  | runtime (reason : ReadError)

abbrev Database (Name : Type*) := Packed Name String Value

abbrev ScanResult (schema : Scan.Schema String Kind) :=
  Except (Manifest.PrepareError Date32.Error) (Events.Trace schema Value ReadError)

variable {Name : Type*} {schema : Scan.Schema String Kind}

/-- Keep typed admission distinct from errors reached after the projected
schema was available. The ordered rows include width-zero positions. -/
def collectResult (result : ScanResult schema) : Except SourceError (Events.Observation String Value SourceError) :=
  match result with
  | .error reason => .error (.admission reason)
  | .ok trace =>
    let outcome := match trace.termination with
      | .eos => .eos
      | .closed => .closed
      | .readError reason => .readError (.runtime reason)
      | .closeError reason => .closeError (.runtime reason)
    .ok ⟨⟨schema, trace.rows⟩, outcome⟩

def importResult [DecidableEq Name] (db : Database Name) (name : Name) (result : ScanResult schema) :
    Except (ImportError SourceError) (Database Name) :=
  importCollected db name schema (collectResult result)

/-- Install the exact projected table at a vacant name only after EOS. -/
def importSelected [DecidableEq Name] (db : Database Name) (name : Name) (layout : Schema)
    (options : PartitionPath.Options) (limits : Limits) (projection : Scan.Projection layout.toScan)
    (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File) :
    Except (ImportError SourceError) (Database Name) :=
  importResult db name (readSelected layout options limits projection keep files)

end Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8
