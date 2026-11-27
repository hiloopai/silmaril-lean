module

public import Silmaril.Formats.Hive.Date32.Render.Defs

/-! # Checked native Parquet manifests with one Hive DATE partition key -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32 (Database physical)
open WritePlan.FlatInt32.RowGroups (EmitError File Policy ReadError)

/-- Route a checked named table by its DATE column and emit a bounded native
manifest. The physical leaf remains nullable, unannotated INT32. -/
def emitManifest {Name : Type*} (db : Database Name) (name : Name) (leaf key : String)
    (options : PartitionPath.Options) (policy : Policy) (limits : FlatInt32Writer.Limits) :
    Except (EmitError RenderError) (List File) :=
  WritePlan.FlatInt32.RowGroups.emit db name leaf (partition key) options encode policy limits

/-- Restore all supplied literal occurrences in manifest order. -/
def restoreManifest (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits) (files : List File) :
    Except (ReadError Error) (Scan.Table ((partition key).extend (physical leaf)) Cell) :=
  WritePlan.FlatInt32.RowGroups.restore leaf (partition key) options convert policy limits files

end Silmaril.Formats.Hive.Date32
