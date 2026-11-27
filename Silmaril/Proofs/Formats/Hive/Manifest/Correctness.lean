module

public import Silmaril.Formats.Hive.Manifest.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert partitionCells)

variable {Kind : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem prepareFileWithFileParser_declared {Failure : Type*} (parse : FileParser) (options : Silmaril.Formats.Hive.PartitionPath.Options)
    (convert : Convert Value Failure) {declared : String} {file : File schema Value}
    (prepared : prepareFileWithFileParser schema parse options convert declared = .ok file) :
    file.path.declared = declared := by
  simp only [prepareFileWithFileParser, Except.bind, Except.map] at prepared
  split at prepared
  · cases prepared
  · split at prepared
    · cases prepared
    · split at prepared
      · cases prepared
      · split at prepared
        · cases prepared
        · cases prepared
          rfl

theorem prepare_preserves_paths {Failure : Type*} (options : Silmaril.Formats.Hive.PartitionPath.Options)
    (convert : Convert Value Failure) {paths : List String} {files : List (File schema Value)}
    (prepared : prepare physical schema options convert paths = .ok files) :
    files.map (fun file => file.path.declared) = paths := by
  unfold prepare at prepared
  split at prepared
  · cases prepared
  · induction paths generalizing files with
    | nil =>
      change Except.ok [] = Except.ok files at prepared
      cases prepared
      rfl
    | cons path rest ih =>
      rw [List.mapM_cons] at prepared
      simp only [bind, Except.bind, pure, Except.pure] at prepared
      split at prepared
      · cases prepared
      · rename_i file parsed
        split at prepared
        · cases prepared
        · rename_i tail more
          cases prepared
          simp [prepareFileWithFileParser_declared (DirectoryParser.asFileParser Silmaril.Formats.Hive.PartitionPath.parse) options convert parsed, ih more]

theorem scan_first_terminal {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (before : List (File schema Value)) (current : File schema Value) (after : List (File schema Value))
    (exhausted : ∀ file ∈ before, (scanFile opener projection predicate file).termination = .eos)
    (stop : (scanFile opener projection predicate current).termination ≠ .eos) :
    let run := scan opener projection predicate (before ++ current :: after)
    let last := scanFile opener projection predicate current
    run.rows = before.flatMap (fun file => (scanFile opener projection predicate file).rows) ++ last.rows ∧
      run.termination = last.termination := by
  induction before with
  | nil =>
    simp only [List.nil_append, List.flatMap_nil]
    have stopped := Silmaril.Formats.Hive.ParquetScan.assemble_stops
      (scanFile opener projection predicate) current after stop
    rw [scan, stopped]
    exact ⟨rfl, rfl⟩
  | cons file rest ih =>
    have headEof := Silmaril.Formats.Hive.ParquetScan.assemble_eof
      (scanFile opener projection predicate) file (rest ++ current :: after)
      (exhausted file (List.mem_cons_self ..))
    have tail := ih (fun entry member => exhausted entry (List.mem_cons_of_mem _ member))
    simp only [List.cons_append, List.flatMap_cons, scan] at tail ⊢
    exact ⟨by rw [headEof.1, tail.1, List.append_assoc], headEof.2.trans tail.2⟩

theorem scanFile_observation {Group Error : Type*}
    (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) :
    let strict := scanFile opener projection predicate file
    let full := scanFile opener (Scan.Projection.id (schema.extend physical)) (fun _ => some true) file
    let reference := full.scan projection (fun row => predicate (partitionCells row))
    strict.rows = reference.rows ∧ strict.termination = reference.termination := by
  dsimp only
  erw [Events.Trace.rows_scan, Events.Trace.termination_scan]
  cases opened : opener file.path.declared with
  | error reason =>
    simp only [scanFile, opened]
    exact ⟨rfl, trivial⟩
  | ok source =>
    let part : ParquetScan.Partition physical schema Value Error :=
      ⟨file.cells, [ParquetScan.readFile source.source source.fuel]⟩
    let strict := ParquetScan.scanPartition projection predicate part
    let full := ParquetScan.scanPartition (Scan.Projection.id (schema.extend physical)) (fun _ => some true) part
    have hoisted := ParquetScan.scanPartition_observation projection predicate part
    have identity := ParquetScan.scanPartition_observation
      (Scan.Projection.id (schema.extend physical)) (fun _ => some true) part
    have fullRows : full.rows = part.augmented.rows := by
      simpa [Events.Trace.rows_scan, Scan.Projection.scan, Scan.select] using identity.1
    have term : strict.termination = full.termination := hoisted.2.trans identity.2.symm
    have rows : strict.rows = projection.scan (fun row => predicate (partitionCells row)) full.rows := by
      rw [fullRows]
      simpa only [Events.Trace.rows_scan] using hoisted.1
    simp only [scanFile, opened]
    refine ⟨rows, ?_⟩
    let lift : Events.Termination Error → Events.Termination (FileError Error) := fun outcome =>
      match outcome with
      | .eos => .eos | .closed => .closed
      | .readError reason => .readError (.source file.path.declared reason)
      | .closeError reason => .closeError (.source file.path.declared reason)
    exact congrArg lift term

theorem scan_equivalent_thenFilter {Group Error : Type*} (opener : Opener Group physical Value Error)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scan opener projection predicate files⟩)
      (.ok ⟨projection.schema, (scan opener (Scan.Projection.id (schema.extend physical)) (fun _ => some true)
        files).scan projection (fun row => predicate (partitionCells row))⟩) := by
  apply Events.EventStream.equivalent_open_iff.mpr
  unfold scan
  erw [ParquetScan.assemble_scan]
  exact ParquetScan.assemble_observation _ _ files (scanFile_observation opener projection predicate)

end Silmaril.Proofs.Formats.Hive.Manifest
