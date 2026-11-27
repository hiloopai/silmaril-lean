module

public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Defs

/-! # Opt-in ISO DATE Hive keys on native INT32 manifests -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32 (physical)
open WritePlan.FlatInt32.RowGroups

inductive Error where
  | invalidDate (text : String)
  deriving DecidableEq, Repr

/-- Convert present, already decoded text to a signed day since 1970-01-01. -/
def decodeText (text : String) : Except Error DateInterop.Date32.Payload :=
  match Csv.Typed.Codecs.Date32.parse text.toUTF8.data.toList with
  | some day => .ok day
  | none => .error (.invalidDate text)

def convert : TypedPartitions.Convert Cell Error := fun _ => decodeText

/-- One required key whose explicit null marker is still a nullable cell. -/
def partition (key : String) : TypedPartitions.PartitionSchema Unit :=
  ⟨#[⟨key, (), .reject⟩]⟩

/-- Scan supplied file occurrences with the Hive URI/decoded-marker policy.
The virtual DATE cell uses signed epoch-day storage; the physical leaf is the
existing nullable unannotated INT32 profile. -/
def scanPruned (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate (partition key).toScan Cell) (files : List File) :
    Except (ReadError Error) (Events.Trace ((partition key).extend (physical leaf)) Error) :=
  Events.scanPruned leaf (partition key) options convert policy limits predicate files

end Silmaril.Formats.Hive.Date32
