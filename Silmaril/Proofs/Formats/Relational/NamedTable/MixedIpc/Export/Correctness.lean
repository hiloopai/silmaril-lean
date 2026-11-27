module

public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Defs
public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Thms
public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Formats.Arrow.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Export

open Silmaril.Relational
open Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Relational.NamedTable.MixedIpc
open Silmaril.Formats.Relational.NamedTable.MixedIpc.Export
open Silmaril.Formats.Relational
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats

theorem row_rowPair (descriptor : Descriptor) (row : Scan.Row descriptor.schema Cell) :
    descriptor.row (rowPair descriptor row) = row := by
  cases descriptor with
  | mk order integer binary =>
    cases order <;> funext i
    · exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => nomatch k) j) i
    · exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => nomatch k) j) i

theorem prepare_exact {Name : Type*} {db : Database Name} {name : Name}
    {expected : Descriptor} {sizes : List Nat} {batches : List (List Pair)}
    (prepared : Export.prepare db name expected sizes = .ok batches) :
    ∃ rows : Scan.Table expected.schema Cell,
      Scan.observePacked db name = some ⟨expected.schema, rows⟩ ∧
      sizes.sum = rows.length ∧ batches = (sizes.splitLengths rows).map (List.map (rowPair expected)) := by
  unfold Export.prepare NamedTable.exportChunks at prepared
  cases found : Scan.observePacked db name with
  | none => simp [found, Except.mapError, Bind.bind, Except.bind] at prepared
  | some table =>
    by_cases count : sizes.sum = table.rowCount
    · by_cases exactSchema : table.schema = expected.schema
      · rcases table with ⟨schema, rows⟩
        change schema = expected.schema at exactSchema
        subst schema
        refine ⟨rows, rfl, count, ?_⟩
        simpa [found, count, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] using prepared.symm
      · have different : List.ofFn table.schema.kind ≠ List.ofFn expected.schema.kind := by
          intro same
          apply exactSchema
          apply (NamedTable.schemaMatches_eq_true_iff _ _).mp
          simp [NamedTable.schemaMatches, same]
        simp [found, count, different, Except.mapError, Bind.bind, Except.bind, throw] at prepared
    · simp [found, count, Except.mapError, Bind.bind, Except.bind] at prepared

private theorem writer_fields (descriptor : Descriptor) :
    (writerSchema descriptor).fields = descriptor.fields := by
  cases descriptor with
  | mk order integer binary => cases order <;> rfl

private theorem ofFields_fields (descriptor : Descriptor) :
    Descriptor.ofFields descriptor.fields = some descriptor := by
  cases descriptor with
  | mk order integer binary =>
    rcases integer with ⟨i, ni⟩
    rcases binary with ⟨b, nb⟩
    cases order <;> rfl

private theorem intSlot_map (ints : List (Option Int32)) :
    (ints.map (Option.map Arrow.Value.int32)).mapM intSlot = some ints := by
  induction ints with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [List.mapM_cons, intSlot, ih]

private theorem pack_exact (octets : List UInt8) : (pack octets).toList = octets :=
  Arrow.Writer.emitBytes_bytes octets

private theorem observe_cons (head : Field × Column) (tail : List (Field × Column)) :
    Writer.observeColumns (head :: tail) =
      (match head.2 with
      | .primitive values => some (Writer.ColumnObservation.int32 values)
      | .binaryView values => some (Writer.ColumnObservation.binaryView (values.map (Option.map KBytes.toList)))
      | .utf8View values => some (Writer.ColumnObservation.utf8View values)).bind (fun value =>
        (Writer.observeColumns tail).bind (fun rest => some ((head.1, value) :: rest))) := by
  rcases head with ⟨field, column⟩
  cases column <;> simp [Writer.observeColumns, List.mapM_cons]

private theorem columns_length {columns : List (Field × Column)}
    {observed : List (Field × Writer.ColumnObservation)}
    (decoded : Writer.observeColumns columns = some observed) : columns.length = observed.length := by
  induction columns generalizing observed with
  | nil =>
    cases decoded
    rfl
  | cons first rest ih =>
    rcases first with ⟨field, value⟩
    rw [observe_cons] at decoded
    cases tail : Writer.observeColumns rest with
    | none => cases value <;> simp [tail] at decoded
    | some result =>
      have length := ih tail
      cases value <;> simp [tail] at decoded
      all_goals subst observed; simp [length]

private theorem writer_observe (descriptor : Descriptor) (pairs : List Pair) :
    (writerBatch pairs).observe (writerSchema descriptor) = observePairs descriptor pairs := by
  cases order : descriptor.viewFirst <;>
    simp [observePairs, StreamWriter.BatchInput.observe, Writer.Input.observe, Writer.Order.pair,
      writerSchema, StreamWriter.Schema.recordInput, Writer.Input.intField, Writer.Input.viewField,
      Writer.Input.intColumn, Arrow.Writer.ColumnValues.observe, Descriptor.intField, Descriptor.viewField,
      writerBatch, order, List.map_map, Option.map_map, Function.comp_def, pack_exact]

private theorem batchPairs_of_observed (descriptor : Descriptor) (batch : Stream.Batch) (pairs : List Pair)
    (equal : StreamWriter.observeBatch batch = observePairs descriptor pairs) :
    batchPairs descriptor batch = some pairs := by
  rcases batch with ⟨range, count, columns⟩
  have lists := congrArg Prod.snd equal
  change Writer.observeColumns columns = (observePairs descriptor pairs).2 at lists
  unfold observePairs at lists
  have rows : count = pairs.length := congrArg Prod.fst equal
  subst count
  have length : columns.length = 2 := by
    have := columns_length lists
    cases order : descriptor.viewFirst <;> simpa [order] using this
  rcases columns with _ | ⟨⟨first, firstColumn⟩, rest⟩
  · simp at length
  rcases rest with _ | ⟨⟨second, secondColumn⟩, rest⟩
  · simp at length
  have noMore : rest = [] := by simpa using length
  subst rest
  cases order : descriptor.viewFirst <;>
    cases firstColumn <;> cases secondColumn <;>
    simp [Writer.observeColumns, order, List.mapM_cons] at lists
  · rename_i ints bytes
    obtain ⟨⟨firstExact, intExact⟩, secondExact, byteExact⟩ := lists
    have byteCount := congrArg List.length byteExact
    simp [List.length_map] at byteCount
    have intRead : ints.mapM intSlot = some (pairs.map Prod.fst) := by
      rw [intExact]
      simpa only [List.map_map, Function.comp_def] using intSlot_map (pairs.map Prod.fst)
    simp [batchPairs, Descriptor.fields, order, firstExact, secondExact, intRead,
      byteCount, byteExact, List.zip_map']
  · rename_i bytes ints
    obtain ⟨⟨firstExact, byteExact⟩, secondExact, intExact⟩ := lists
    have byteCount := congrArg List.length byteExact
    simp [List.length_map] at byteCount
    have intRead : ints.mapM intSlot = some (pairs.map Prod.fst) := by
      rw [intExact]
      simpa only [List.map_map, Function.comp_def] using intSlot_map (pairs.map Prod.fst)
    simp [batchPairs, Descriptor.fields, order, firstExact, secondExact, intRead,
      byteCount, byteExact, List.zip_map']

private theorem prepareBatches_of_observed (descriptor : Descriptor) (index : Nat)
    {source : List Stream.Batch} {batches : List (List Pair)}
    (equal : source.map StreamWriter.observeBatch = batches.map (observePairs descriptor)) :
    prepareBatches descriptor index source = .ok batches := by
  induction source generalizing index batches with
  | nil =>
    cases batches with
    | nil => rfl
    | cons rows rest => simp at equal
  | cons batch rest ih =>
    cases batches with
    | nil => simp at equal
    | cons rows remaining =>
      simp only [List.map_cons, List.cons.injEq] at equal
      have pairs := batchPairs_of_observed descriptor batch rows equal.1
      simp [prepareBatches, pairs, ih (index + 1) equal.2, Bind.bind, Except.bind, pure, Except.pure]

theorem emit_ok_iff {Name : Type*} (db : Database Name) (name : Name)
    (expected : Descriptor) (sizes : List Nat) (limits : MixedIpc.Limits) (wire : KBytes) :
    Export.emit db name expected sizes limits = .ok wire ↔
      ∃ batches, Export.prepare db name expected sizes = .ok batches ∧
        octetBytes batches ≤ limits.inputBytes ∧
        StreamWriter.emit limits.mixed (writerSchema expected) (batches.map writerBatch) = .ok wire ∧
        wire.len ≤ limits.inputBytes := by
  cases prepared : Export.prepare db name expected sizes with
  | error cause => simp [Export.emit, prepared, Bind.bind, Except.bind]
  | ok batches =>
    by_cases octets : octetBytes batches ≤ limits.inputBytes
    · cases written : StreamWriter.emit limits.mixed (writerSchema expected) (batches.map writerBatch) with
      | error cause =>
        simp [Export.emit, prepared, Nat.not_lt.mpr octets, written, Except.mapError, Bind.bind, Except.bind]
      | ok encoded =>
        by_cases bounded : encoded.len ≤ limits.inputBytes
        · simp [Export.emit, prepared, Nat.not_lt.mpr octets, written, Except.mapError, Bind.bind,
            Except.bind, Nat.not_lt.mpr bounded, pure, Except.pure, octets]
          intro h
          exact h ▸ bounded
        · simp [Export.emit, prepared, Nat.not_le.mp bounded, Nat.not_lt.mpr octets, written,
            Except.mapError, Bind.bind, Except.bind, throw, octets]
          rintro rfl
          exact Nat.not_le.mp bounded
    · simp [Export.emit, prepared, Nat.not_le.mp octets, octets, Bind.bind, Except.bind, throw]

theorem read_of_observed {expected : Descriptor} {limits : MixedIpc.Limits} {wire : KBytes}
    {decoded : Stream.Observed} {batches : List (List Pair)}
    (bounded : wire.len ≤ limits.inputBytes)
    (read : Stream.read limits.mixed wire = .ok decoded) (fields : decoded.fields = expected.fields)
    (observed : decoded.batches.map StreamWriter.observeBatch = batches.map (observePairs expected)) :
    MixedIpc.read limits wire = .ok ⟨expected, batches⟩ := by
  have shape : Descriptor.ofFields decoded.fields = some expected := by rw [fields, ofFields_fields]
  simp [MixedIpc.read, Nat.not_lt.mpr bounded, read, MixedIpc.prepare,
    Except.mapError, Except.bind, shape, prepareBatches_of_observed expected 0 observed, Bind.bind, pure, Except.pure]

private theorem read_of_writer {expected : Descriptor} {limits : MixedIpc.Limits} {wire : KBytes}
    {batches : List (List Pair)} (bounded : wire.len ≤ limits.inputBytes)
    (written : StreamWriter.emit limits.mixed (writerSchema expected) (batches.map writerBatch) = .ok wire) :
    MixedIpc.read limits wire = .ok ⟨expected, batches⟩ := by
  obtain ⟨decoded, read, fields, observed⟩ := StreamWriter.emit_readback written
  apply read_of_observed bounded read (fields.trans (writer_fields expected))
  simpa [List.map_map, Function.comp_def, writer_observe] using observed

theorem emit_readback {Name : Type*} {db : Database Name} {name : Name}
    {expected : Descriptor} {sizes : List Nat} {limits : MixedIpc.Limits} {wire : KBytes}
    (written : Export.emit db name expected sizes limits = .ok wire) :
    ∃ rows : Scan.Table expected.schema Cell, ∃ prepared : Prepared,
      Scan.observePacked db name = some ⟨expected.schema, rows⟩ ∧
      MixedIpc.read limits wire = .ok prepared ∧
      prepared.descriptor = expected ∧
      prepared.batches = (sizes.splitLengths rows).map (List.map (rowPair expected)) ∧
      prepared.batches.map List.length = sizes ∧
      prepared.table = ⟨expected.schema, rows⟩ := by
  obtain ⟨batches, prepared, _, emitted, bounded⟩ := (emit_ok_iff _ _ _ _ _ _).mp written
  obtain ⟨rows, source, count, grouping⟩ := prepare_exact prepared
  refine ⟨rows, ⟨expected, batches⟩, source, read_of_writer bounded emitted, rfl, grouping, ?_, ?_⟩
  · simp [grouping, List.map_map, Function.comp_def, List.map_splitLengths_length rows sizes count.le]
  · simp [Prepared.table, grouping, ← List.map_flatten, List.map_map, Function.comp_def,
      List.flatten_splitLengths rows sizes count.ge, row_rowPair]

theorem emit_import {Name Target : Type*} [DecidableEq Target]
    {db : Database Name} {name : Name} {expected : Descriptor} {sizes : List Nat}
    {limits : MixedIpc.Limits} {wire : KBytes} (written : Export.emit db name expected sizes limits = .ok wire)
    (dest : Database Target) (key : Target) (vacant : dest key = none) :
    ∃ rows : Scan.Table expected.schema Cell,
      Scan.observePacked db name = some ⟨expected.schema, rows⟩ ∧
      importIpc dest key expected limits wire =
        .ok (Function.update dest key (some ⟨expected.schema, rows⟩)) := by
  obtain ⟨rows, prepared, source, read, descriptor, _, _, table⟩ := emit_readback written
  refine ⟨rows, source, (importIpc_ok_iff _ _ _ _ _ _).mpr ⟨vacant, prepared, read, descriptor, ?_⟩⟩
  change (fun table : Scan.Observation Label Cell =>
    Function.update dest key (some ⟨table.schema, table.rows⟩)) ⟨expected.schema, rows⟩ =
      (fun table : Scan.Observation Label Cell =>
        Function.update dest key (some ⟨table.schema, table.rows⟩)) prepared.table
  rw [table]

end Silmaril.Proofs.Formats.Relational.NamedTable.MixedIpc.Export
