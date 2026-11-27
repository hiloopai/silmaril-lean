module

public import Silmaril.Formats.Hive.Manifest.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.Correctness

public section

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert partitionCells)

variable {Kind : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem prepareFileWithFileParser_declared {Failure : Type*} (parse : FileParser)
    (options : PartitionPath.Options) (convert : Convert Value Failure)
    {declared : String} {file : File schema Value}
    (prepared : prepareFileWithFileParser schema parse options convert declared = .ok file) :
    file.path.declared = declared :=
  Proofs.Formats.Hive.Manifest.prepareFileWithFileParser_declared parse options convert prepared

theorem prepareFileWith_declared {Failure : Type*} (parse : DirectoryParser)
    (options : PartitionPath.Options) (convert : Convert Value Failure)
    {declared : String} {file : File schema Value}
    (prepared : prepareFileWith schema parse options convert declared = .ok file) :
    file.path.declared = declared :=
  prepareFileWithFileParser_declared parse.asFileParser options convert prepared

/-- Successful preparation preserves the original ordered opener inputs, including repeats. -/
theorem prepare_preserves_paths {Failure : Type*} (options : PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (prepared : prepare physical schema options convert paths = .ok files) :
    files.map (fun file => file.path.declared) = paths :=
  Proofs.Formats.Hive.Manifest.prepare_preserves_paths options convert prepared

/-- An open failure in the current file stops the scan regardless of the predicate or suffix. -/
theorem scan_open_failure {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) (rest : List (File schema Value)) {reason : Error}
    (failed : opener file.path.declared = .error reason) :
    scan opener projection predicate (file :: rest) =
      ⟨[], .readError (.open file.path.declared reason)⟩ := by
  simp [scan, ParquetScan.assemble, scanFile, failed]

/-- The first non-EOF file determines termination. Keep all previously selected
rows and that file's selected prefix. The remaining declarations cannot
change the observation. -/
theorem scan_first_terminal {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (before : List (File schema Value)) (current : File schema Value) (after : List (File schema Value))
    (exhausted : ∀ file ∈ before, (scanFile opener projection predicate file).termination = .eos)
    (stop : (scanFile opener projection predicate current).termination ≠ .eos) :
    let run := scan opener projection predicate (before ++ current :: after)
    let last := scanFile opener projection predicate current
    run.rows = before.flatMap (fun file => (scanFile opener projection predicate file).rows) ++ last.rows ∧
      run.termination = last.termination :=
  Proofs.Formats.Hive.Manifest.scan_first_terminal opener projection predicate before current after exhausted stop

/-- Filtering and projection preserve each opened file's terminal outcome. -/
theorem scanFile_termination_eq_full {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) :
    (scanFile opener projection predicate file).termination =
      (scanFile opener (Scan.Projection.id (schema.extend physical)) (fun _ => some true) file).termination :=
  (Proofs.Formats.Hive.Manifest.scanFile_observation opener projection predicate file).2

/-- Strict partition filtering and projection agree with applying the logical
scan after full typed reading, for rows and the original terminal outcome. -/
theorem scan_equivalent_thenFilter {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scan opener projection predicate files⟩)
      (.ok ⟨projection.schema, (scan opener (Scan.Projection.id (schema.extend physical)) (fun _ => some true)
        files).scan projection (fun row => predicate (partitionCells row))⟩) :=
  Proofs.Formats.Hive.Manifest.scan_equivalent_thenFilter opener projection predicate files

end Silmaril.Formats.Hive.Manifest
