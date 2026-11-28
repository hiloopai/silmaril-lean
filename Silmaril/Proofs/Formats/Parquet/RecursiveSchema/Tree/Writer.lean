module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer

open Silmaril.Formats
open Parquet Parquet.RecursiveSchema.Tree
open Parquet.RecursiveSchema.Tree.Writer
open Arrow.RecursiveSchema.Batch.Rows (Observation)

public theorem emit_wire {limits : Limits} {input : Input} {out : Output}
    (written : emit limits input = .ok out) :
    ∃ groups, Construction limits input out groups ∧ Readback limits input out groups := by
  unfold emit at written
  cases emitted : emitChecked limits input with
  | error cause => simp [emitted, Except.map] at written
  | ok checked =>
    simp [emitted, Except.map] at written
    subst out
    exact ⟨checked.groups, checked.construction, checked.readback⟩

public theorem group_at {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {compiled : Compiled schemaLimits snapshot}
    {ordinal : Nat} {inputs : List Observation} {groups : List WrittenGroup}
    (wire : GroupsReadback limits compiled ordinal inputs groups)
    {index : Nat} {input : Observation} (found : inputs[index]? = some input) :
    ∃ group, groups[index]? = some group ∧ GroupReadback limits compiled (ordinal + index) input group := by
  induction wire generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp at found
      subst input
      exact ⟨_, rfl, by simpa using head⟩
    | succ index =>
      obtain ⟨group, written, read⟩ := ih (by simpa only [List.getElem?_cons_succ] using found)
      exact ⟨group, written, by simpa only [Nat.add_assoc, Nat.add_comm 1 index] using read⟩

public theorem group_original {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {compiled : Compiled schemaLimits snapshot}
    {ordinal : Nat} {input : Observation} {group : WrittenGroup}
    (wire : GroupReadback limits compiled ordinal input group) :
    ∃ result, Rows.readGroupChecked compiled limits.reader ordinal = .ok result ∧
      result.observation = input ∧
      (result.inputs.map fun column => column.original.atoms).toArray = group.traces ∧
      result.inputs.map Rows.CheckedColumn.ordinal = List.range compiled.leaves.size := by
  obtain ⟨result, read, rows, atoms⟩ := wire
  refine ⟨result, read, rows, ?_, Rows.GroupResult.order read⟩
  simpa [Rows.tapes, Function.comp_def, Rows.CheckedColumn.tape, Rows.tape_atoms] using atoms

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer
