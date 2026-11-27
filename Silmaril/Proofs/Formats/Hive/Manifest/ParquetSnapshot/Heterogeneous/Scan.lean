module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Parquet.FlatProjection.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous

open Silmaril.Formats Hive Manifest Silmaril.Relational
open Silmaril.Formats.Hive.Manifest.Heterogeneous
open Parquet.FlatProjection.Events (Cell)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem unmap_error_ok {ε δ α : Type} {result : Except ε α} {wrap : ε → δ} {value : α}
    (accepted : result.mapError wrap = .ok value) : result = .ok value := by
  cases result <;> cases accepted
  rfl

private theorem prepareFile_exact {schema : Schema} {options : PartitionPath.Options} {path : String}
    {file : File schema.partitions Cell}
    (accepted : Heterogeneous.prepareFile schema.partitions options path = .ok file) :
    Manifest.prepareFile schema.partitions options convertCell path = .ok file := by
  obtain ⟨prepared, bound, accepted⟩ := bind_ok accepted
  split at accepted
  · contradiction
  cases Except.ok.inj accepted
  exact unmap_error_ok bound

theorem bindFile_exact {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry} {bound : BoundFile schema}
    (accepted : bindFile schema options limits entry = .ok bound) :
    Manifest.prepareFile schema.partitions options convertCell entry.path = .ok bound.partition ∧
      Parquet.FlatProjection.Events.openFile limits entry.bytes schema.ordinals = .ok bound.physical ∧
      ∃ root leaves, bound.physical.snapshot.metadata.schema = root :: leaves ∧
        Parquet.Footer.ColumnOrder.isFlat root leaves = true ∧
        leaves.find? (fun leaf => schema.partitions.keys.contains leaf.name) = none := by
  obtain ⟨partition, prepared, accepted⟩ := bind_ok accepted
  obtain ⟨checked, opened, accepted⟩ := bind_ok accepted
  cases shape : checked.snapshot.metadata.schema with
  | nil => simp [shape] at accepted
  | cons root leaves =>
    cases flat : Parquet.Footer.ColumnOrder.isFlat root leaves with
    | false => simp [shape, flat, Bind.bind, Except.bind, throw] at accepted
    | true =>
      simp only [shape, flat, Bool.not_true, Bool.false_eq_true, ite_false] at accepted
      cases collision : leaves.find? (fun leaf => schema.partitions.keys.contains leaf.name) with
      | some leaf =>
        rw [collision] at accepted
        simp [Bind.bind, Except.bind, throw] at accepted
      | none =>
        rw [collision] at accepted
        by_cases same : labels checked.schema = labels schema.physical
        · simp [same, pure, Except.pure] at accepted
          cases accepted
          exact ⟨prepareFile_exact prepared, unmap_error_ok opened, root, leaves, shape, flat, collision⟩
        · simp [same] at accepted

theorem extend_counts {schema : Schema} (entry : Entry × Nat) (cells : Scan.Row schema.partitions.toScan Cell)
    (physical : PhysicalTrace schema) :
    (extend entry cells physical).batches.map (·.rowCount) = physical.batches.map (·.rowCount) := by
  simp [extend, ParquetScan.extendTrace, List.map_map, Function.comp_def, AlignedColumns.ofRows]

theorem readFile_direct {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry × Nat} {bound : BoundFile schema}
    (accepted : bindFile schema options limits entry.1 = .ok bound) :
    Parquet.FlatProjection.Events.readAll limits entry.1.bytes schema.ordinals =
        .ok ⟨bound.physical.schema, bound.physical.trace limits⟩ ∧
      readFile schema options limits entry = extend entry bound.partition.cells (bound.trace limits) :=
  ⟨Parquet.FlatProjection.Events.readAll_opened (bindFile_exact accepted).2.1, by simp [readFile, accepted]⟩

private theorem cast_termination {left right : Scan.Schema String Parquet.FlatProjection.Events.Kind}
    (same : left = right) (trace : Arrow.Events.Trace left Cell Parquet.FlatProjection.Events.Error) :
    (cast (congrArg (fun schema => Arrow.Events.Trace schema Cell Parquet.FlatProjection.Events.Error) same)
      trace).termination = trace.termination := by
  cases same
  rfl

theorem readFile_read_error {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry × Nat} {bound : BoundFile schema}
    {cause : Parquet.FlatProjection.Events.Error}
    (accepted : bindFile schema options limits entry.1 = .ok bound)
    (failed : (bound.physical.trace limits).termination = .readError cause) :
    readFile schema options limits entry =
      ⟨(extend entry bound.partition.cells (bound.trace limits)).batches,
        .readError (.file entry.2 entry.1.path (.readParquet cause))⟩ := by
  have term := (cast_termination bound.schemaExact (bound.physical.trace limits)).trans failed
  change (bound.trace limits).termination = .readError cause at term
  simp only [readFile, accepted, extend, ParquetScan.extendTrace, term, atFile]

theorem extend_rows {schema : Schema} (entry : Entry × Nat)
    (cells : Scan.Row schema.partitions.toScan Cell) (physical : PhysicalTrace schema) :
    (extend entry cells physical).rows =
      physical.rows.map (fun row => TypedPartitions.extendRow row cells) :=
  ParquetScan.rows_extendTrace ⟨physical.batches, atFile entry physical.termination⟩ cells

private theorem readFile_eos {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry × Nat}
    (eos : (readFile schema options limits entry).termination = .eos) :
    FileBatches schema options limits entry (readFile schema options limits entry).batches := by
  cases accepted : bindFile schema options limits entry.1 with
  | error cause => simp [readFile, accepted] at eos
  | ok bound =>
    obtain ⟨direct, observed⟩ := readFile_direct accepted
    refine ⟨bound, (bindFile_exact accepted).1, direct, ?_, congrArg Arrow.Events.Trace.batches observed⟩
    rw [observed] at eos
    have term := cast_termination bound.schemaExact (bound.physical.trace limits)
    change (bound.trace limits).termination = (bound.physical.trace limits).termination at term
    cases outcome : (bound.trace limits).termination <;>
      simp [extend, ParquetScan.extendTrace, atFile, outcome] at eos
    exact term.symm.trans outcome

private theorem assemble_eos {schema : Schema} (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (entries : List (Entry × Nat))
    (eos : (ParquetScan.assemble (readFile schema options limits) entries).termination = .eos) :
    ∃ files, List.Forall₂ (FileBatches schema options limits) entries files ∧
      (ParquetScan.assemble (readFile schema options limits) entries).batches = files.flatten := by
  induction entries with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons entry rest ih =>
    cases outcome : (readFile schema options limits entry).termination with
    | eos =>
      have tailEos : (ParquetScan.assemble (readFile schema options limits) rest).termination = .eos := by
        simpa [ParquetScan.assemble, outcome] using eos
      obtain ⟨files, direct, batches⟩ := ih tailEos
      refine ⟨(readFile schema options limits entry).batches :: files,
        .cons (readFile_eos outcome) direct, ?_⟩
      simp [ParquetScan.assemble, outcome, batches]
    | closed => simp [ParquetScan.assemble, outcome] at eos
    | readError => simp [ParquetScan.assemble, outcome] at eos
    | closeError => simp [ParquetScan.assemble, outcome] at eos

theorem read_eos {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {manifest : List Entry} {trace : Trace schema}
    (readOk : Heterogeneous.read schema options limits manifest = .ok trace) (eos : trace.termination = .eos) :
    ∃ files, List.Forall₂ (FileBatches schema options limits) manifest.zipIdx files ∧
      trace.batches = files.flatten := by
  cases checked : checkSchema schema with
  | error => simp [Heterogeneous.read, checked, Except.map] at readOk
  | ok =>
    simp [Heterogeneous.read, checked, Except.map] at readOk
    exact readOk ▸ assemble_eos options limits manifest.zipIdx (readOk.symm ▸ eos)

private theorem assemble_prefix {α : Type} {schema : Schema} (run : α → Trace schema)
    {before rest : List α} (earlier : ∀ entry ∈ before, (run entry).termination = .eos) :
    ParquetScan.assemble run (before ++ rest) =
      ⟨before.flatMap (fun entry => (run entry).batches) ++ (ParquetScan.assemble run rest).batches,
        (ParquetScan.assemble run rest).termination⟩ := by
  induction before with
  | nil => cases observed : ParquetScan.assemble run rest
           simp [observed]
  | cons first tail ih =>
    have head := earlier first (by simp)
    have following := ih (fun entry member => earlier entry (by simp [member]))
    simp [ParquetScan.assemble, head, following, List.append_assoc]

theorem read_first_error {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {manifest : List Entry}
    {before after : List (Entry × Nat)} {current : Entry × Nat} {cause : Error}
    (admitted : checkSchema schema = .ok ())
    (split : manifest.zipIdx = before ++ current :: after)
    (earlier : ∀ entry ∈ before, (readFile schema options limits entry).termination = .eos)
    (failed : (readFile schema options limits current).termination = .readError cause) :
    Heterogeneous.read schema options limits manifest = .ok
      ⟨before.flatMap (fun entry => (readFile schema options limits entry).batches) ++
        (readFile schema options limits current).batches, .readError cause⟩ := by
  have stop : (readFile schema options limits current).termination ≠ .eos := by simp [failed]
  simp only [Heterogeneous.read, admitted, Except.map, split, assemble_prefix _ earlier,
    ParquetScan.assemble_stops _ current after stop, failed]

theorem project_agrees (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (manifest : List Entry) (p : Scan.Projection schema.output) :
    project schema options limits manifest p =
      (Heterogeneous.read schema options limits manifest).map (fun trace => trace.scan p (fun _ => some true)) := by
  cases checked : checkSchema schema with
  | error => simp [project, Heterogeneous.read, checked, Except.map]
  | ok _ => simp [project, Heterogeneous.read, checked, Except.map, ParquetScan.assemble_scan]

theorem project_counts {schema : Schema} (p : Scan.Projection schema.output) (trace : Trace schema) :
    (trace.scan p (fun _ => some true)).batches.map (·.rowCount) = trace.batches.map (·.rowCount) := by
  simp [Arrow.Events.Trace.scan, Scan.Projection.scan, Scan.select, List.map_map, Function.comp_def,
    Scan.Projection.project, AlignedColumns.ofRows]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous
