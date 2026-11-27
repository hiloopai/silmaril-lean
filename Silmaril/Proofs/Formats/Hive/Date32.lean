module

public import Silmaril.Formats.Hive.Date32.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Thms
public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32
open Hive.WritePlan.FlatInt32.RowGroups
open Snapshot.FlatInt32 (Cell)

theorem decodeText_ok_iff (text : String) (day : DateInterop.Date32.Payload) :
    decodeText text = .ok day ↔
      Csv.Typed.Codecs.Date32.print day = some text.toUTF8.data.toList := by
  rw [← Csv.Typed.Codecs.Date32.parse_eq_some_iff]
  unfold decodeText
  cases Csv.Typed.Codecs.Date32.parse text.toUTF8.data.toList <;> simp

theorem decodeDirectory_singleton (key : String) (options : PartitionPath.Options)
    (directory : String) (text : Option String) (nonempty : key ≠ "")
    (parsed : PartitionPath.parse options directory = .ok [(key, text)]) :
    WritePlan.decodeDirectory (partition key) options convert directory =
      ((text.mapM decodeText).mapError fun reason =>
        WritePlan.RestoreError.binding directory (.conversion key reason)).map (fun day _ => day) := by
  simp only [WritePlan.decodeDirectory, parsed, Except.mapError]
  simp [TypedPartitions.decode, TypedPartitions.PartitionSchema.keys, partition, PartitionPath.validateKeys,
    nonempty, TypedPartitions.decodeField, PartitionPath.lookup, convert]
  have constantRows (day : Option DateInterop.Date32.Payload) :
      (fun i : Fin 1 => Fin.cases day (fun j : Fin 0 => nomatch j) i) = fun _ => day := by
    funext i
    have h : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  cases text with
  | none => exact congrArg Except.ok (constantRows none)
  | some value =>
    cases h : decodeText value with
    | error cause =>
      simp only [Option.mapM, h, Except.map]
      rfl
    | ok day =>
      simp [Option.mapM, h, Except.map]
      exact congrArg Except.ok (constantRows (some day))

theorem bindFileCells_singleton (key : String) (options : PartitionPath.Options) (file : File)
    (directory : String) (text : Option String) (nonempty : key ≠ "")
    (path : Hive.WritePlan.FlatInt32.checkFilePath (Failure := Error) file.path = .ok directory)
    (parsed : PartitionPath.parse options directory = .ok [(key, text)]) :
    bindFileCells (partition key) options convert file =
      ((text.mapM decodeText).mapError fun reason =>
        FileError.partition (.binding directory (.conversion key reason))).map (fun day _ => day) := by
  simp only [bindFileCells, path, Except.mapError, decodeDirectory_singleton key options directory text nonempty parsed,
    Bind.bind, Except.bind]
  cases text.mapM decodeText <;> rfl

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
        .error (.file before.length bad.path reason)⟩ := by
  have failure : Events.scanFile leaf (partition key) options convert policy limits predicate
      (bad, before.length) = ⟨[], .error (.file before.length bad.path reason)⟩ := by
    simp [Events.scanFile, failed]
  have trace := Events.scanPruned_first_error leaf (partition key) options convert policy limits predicate
    before bad after (.file before.length bad.path reason) admitted done (by rw [failure])
  simpa [scanPruned, failure] using trace

end Silmaril.Proofs.Formats.Hive.Date32
