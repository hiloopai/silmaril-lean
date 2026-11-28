module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows

open Occurrences

public section

/-- Discarding addresses yields the exact original signed slot stream. -/
theorem tape_atoms (carrier : ListPath.Chunk.Carrier) (observed : ListPath.Chunk.Observation) :
    (Tape.ofRead carrier observed).atoms = observed.atoms :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.tape_atoms carrier observed

/-- The addressed entry names its original data frame and slot within that frame. -/
theorem tape_of_slot {carrier : ListPath.Chunk.Carrier} {observed : ListPath.Chunk.Observation}
    {slot : Nat} {entry : Addressed} (found : (Tape.ofRead carrier observed).slots[slot]? = some entry) :
    ∃ page ordinal localSlot,
      observed.pages[ordinal]? = some page ∧
      page.decoded.atoms[localSlot]? = some entry.atom ∧
      entry.point = ⟨carrier.address, observed.dictionary.isSome.toNat + ordinal,
        page.frame.header.start, page.start.slots + localSlot⟩ :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.tape_of_slot found

/-- Taking an occurrence advances the cursor and partitions the original window. -/
theorem take_partition {whole head rest : Slice} {depth : Nat}
    (taken : whole.take depth = some (head, rest)) :
    head.tape = whole.tape ∧ rest.tape = whole.tape ∧ head.start = whole.start ∧
      whole.start < head.stop ∧ head.stop = rest.start ∧ rest.stop = whole.stop :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.take_partition taken

/-- All columns are checked in original physical footer order. -/
theorem readColumns_order {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {caps : ListPath.Chunk.Limits} {group : Nat}
    {inputs : List (CheckedColumn compiled caps group)}
    (read : readColumns compiled caps group = .ok inputs) :
    inputs.map CheckedColumn.ordinal = List.range compiled.leaves.size :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.readColumns_order read

/-- The result keeps the original checked inputs used by the native reader. -/
theorem readGroupChecked_origin {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {limits : Limits} {group : Nat}
    {result : GroupResult compiled limits group}
    (read : readGroupChecked compiled limits group = .ok result) :
    readColumns compiled limits.chunk group = .ok result.inputs :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.readGroupChecked_origin read

/-- Projecting the reconstructed rows by the checked schema recovers every original physical slot stream. -/
theorem project_exact {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {limits : Limits} {group : Nat}
    (result : GroupResult compiled limits group) :
    Projection.trace (schemaWidths compiled) result.inputs.length schemaLimits.maxSchemaDepth
      compiled.schema.fields result.observation.rows =
        some ((result.inputs.map fun input => input.original.atoms).toArray) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.project_exact result

/-- A shared topology refusal is the assembler’s reached disagreement. -/
theorem shared_failure {widths : Array Nat} {slotBudget depth : Nat} {fields : List Repeated.Field}
    {requested : Nat} {columns : Array Tape} {failure : {fault // originalFault columns fault}}
    (refused : join widths slotBudget depth fields requested columns = .error failure)
    (shared : failure.val.shared) :
    assemble widths slotBudget depth fields requested columns = .error failure.val :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.shared_failure refused shared

/-- A join refusal follows group admission and complete original reads of all its columns. -/
theorem readGroupChecked_join_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {limits : Limits} {group : Nat} {fault : Fault}
    (read : readGroupChecked compiled limits group = .error (.join fault)) :
    ∃ admission : Admitted compiled limits group, ∃ inputs,
      admit compiled limits group = .ok admission ∧
      readColumns compiled limits.chunk group = .ok inputs ∧
      ∃ witness : originalFault (tapes inputs) fault,
        join (schemaWidths compiled) limits.maxSlots schemaLimits.maxSchemaDepth
          compiled.schema.fields admission.value.numRows.toNat (tapes inputs) = .error ⟨fault, witness⟩ :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.readGroupChecked_join_failure read

/-- Both kinds of boundary retain the checked original coordinates. -/
theorem original_boundary {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {caps : ListPath.Chunk.Limits} {group : Nat}
    {inputs : List (CheckedColumn compiled caps group)} {boundary : Boundary}
    (found : originalBoundary (tapes inputs) boundary) :
    ∃ input, inputs[boundary.point.column.column]? = some input ∧
      match boundary with
      | .slot point =>
        ∃ page ordinal localSlot entry,
          input.tape.slots[point.slot]? = some entry ∧
          input.original.pages[ordinal]? = some page ∧
          page.decoded.atoms[localSlot]? = some entry.atom ∧
          point = ⟨input.binding.carrier.address, input.original.dictionary.isSome.toNat + ordinal,
            page.frame.header.start, page.start.slots + localSlot⟩
      | .end point =>
        point = ⟨input.binding.carrier.address, input.original.frames.length,
          input.binding.carrier.span.stop, input.original.stop.slots⟩ :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.original_boundary found

theorem GroupResult.order {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {limits : Limits} {group : Nat}
    {result : GroupResult compiled limits group}
    (read : readGroupChecked compiled limits group = .ok result) :
    result.inputs.map CheckedColumn.ordinal = List.range compiled.leaves.size :=
  readColumns_order (readGroupChecked_origin read)

/-- Each input has the original frame chain and per-version decoder witnesses. -/
theorem CheckedColumn.wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {caps : ListPath.Chunk.Limits} {group : Nat}
    (input : CheckedColumn compiled caps group) :
    ListPath.Chunk.Wire caps input.binding.carrier input.original :=
  input.binding.read_wire input.read

theorem GroupResult.bounded {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {limits : Limits} {group : Nat}
    (result : GroupResult compiled limits group) :
    compiled.leaves.size ≤ limits.maxColumns ∧ result.observation.rowCount ≤ limits.chunk.maxRows ∧
      declaredSlots result.admission.value ≤ limits.maxSlots ∧ slotCount (tapes result.inputs) ≤ limits.maxSlots :=
  ⟨result.admission.columnLimit, result.exact.rowCount ▸ result.admission.rowLimit,
    result.admission.slotLimit, result.exact.bounded⟩

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows
