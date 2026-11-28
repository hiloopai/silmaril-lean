module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows

open Silmaril.Formats.Parquet Silmaril.Formats.Parquet.RecursiveSchema
open Tree Tree.Rows Tree.Occurrences
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)

public theorem tape_atoms {P : Type} (carrier : ListPath.Chunk.Carrier P) (observed : ListPath.Chunk.Observation) :
    (Tape.ofRead carrier observed).atoms = observed.atoms := by
  simp only [Tape.atoms, Tape.ofRead, List.toList_toArray, addressed,
    List.map_flatMap, List.map_map, ListPath.Chunk.Observation.atoms]
  have aux : ∀ (pages : List ListPath.Chunk.ObservedPage) (offset : Nat),
      ((pages.zipIdx offset).flatMap fun pair => pair.1.decoded.atoms) =
        pages.flatMap (·.decoded.atoms) := by
    intro pages
    induction pages with
    | nil => simp
    | cons page pages ih =>
      intro offset
      simp [ih]
  simpa only [Function.comp_def, List.zipIdx_map_fst] using
    aux observed.pages observed.dictionary.isSome.toNat

public theorem tape_of_slot {P : Type} {carrier : ListPath.Chunk.Carrier P} {observed : ListPath.Chunk.Observation}
    {slot : Nat} {entry : Addressed} (found : (Tape.ofRead carrier observed).slots[slot]? = some entry) :
    ∃ page ordinal localSlot,
      observed.pages[ordinal]? = some page ∧
      page.decoded.atoms[localSlot]? = some entry.atom ∧
      entry.point = ⟨carrier.address, observed.dictionary.isSome.toNat + ordinal,
        page.frame.header.start, page.start.slots + localSlot⟩ := by
  have member : entry ∈ addressed carrier observed := by
    have h := Array.mem_of_getElem? found
    simpa [Tape.ofRead] using h
  simp only [addressed, List.mem_flatMap, List.mem_map] at member
  obtain ⟨⟨page, pageIndex⟩, hpage, item, hatom, rfl⟩ := member
  obtain ⟨atom, atomIndex⟩ := item
  rw [List.mk_mem_zipIdx_iff_le_and_getElem?_sub] at hpage hatom
  obtain ⟨hp, hpage⟩ := hpage
  obtain ⟨ha, hatom⟩ := hatom
  refine ⟨page, pageIndex - observed.dictionary.isSome.toNat, atomIndex - page.start.slots,
    hpage, hatom, ?_⟩
  change page.start.slots ≤ atomIndex at ha
  have pageNumber : observed.dictionary.isSome.toNat + (pageIndex - observed.dictionary.isSome.toNat) = pageIndex := by omega
  have slotNumber : page.start.slots + (atomIndex - page.start.slots) = atomIndex := by omega
  simp only [pageNumber, slotNumber]

public theorem take_partition {whole head rest : Slice} {depth : Nat}
    (taken : whole.take depth = some (head, rest)) :
    head.tape = whole.tape ∧ rest.tape = whole.tape ∧ head.start = whole.start ∧
      whole.start < head.stop ∧ head.stop = rest.start ∧ rest.stop = whole.stop := by
  unfold Slice.take at taken
  split at taken
  · have low := (seek whole.tape depth (whole.start + 1) (whole.stop - (whole.start + 1))).property.1
    cases taken
    exact ⟨rfl, rfl, rfl, Nat.lt_of_succ_le low, rfl, rfl⟩
  · contradiction

private theorem mapM_project {α β : Type} {f : α → Except InputError β} {project : β → α}
    (one : ∀ a b, f a = .ok b → project b = a) {input : List α} {output : List β}
    (read : input.mapM f = .ok output) : output.map project = input := by
  induction input generalizing output with
  | nil => simpa using (show output = [] from (Except.ok.inj read).symm)
  | cons head tail ih =>
    rw [List.mapM_cons] at read
    cases first : f head with
    | error cause => simp [first, bind, Except.bind] at read
    | ok value =>
      cases rest : tail.mapM f with
      | error cause => simp [first, rest, bind, Except.bind] at read
      | ok values =>
        simp [first, rest, bind, Except.bind, pure, Except.pure] at read
        subst output
        simp [one _ _ first, ih rest]

public theorem readColumns_order {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Tree.Compiled schemaLimits snapshot} {caps : ListPath.Chunk.Limits} {group : Nat}
    {inputs : List (CheckedColumn compiled caps group)}
    (read : readColumns compiled caps group = .ok inputs) :
    inputs.map CheckedColumn.ordinal = List.range compiled.leaves.size := by
  unfold readColumns at read
  cases bindings : (List.range compiled.leaves.size).mapM (bindOriginal compiled group) with
  | error cause => simp [bindings, bind, Except.bind] at read
  | ok columns =>
    simp only [bindings, bind, Except.bind] at read
    have boundOrder := mapM_project (project := Sigma.fst) (fun a b h => by
      unfold bindOriginal at h
      cases original : bindLeaf compiled group a <;>
        simp [original, Except.mapError, bind, Except.bind, pure, Except.pure] at h
      subst b
      rfl) bindings
    have originals := mapM_project (project := fun checked => (⟨checked.ordinal, checked.binding⟩ : OpenColumn compiled group))
      (fun a b h => by
        unfold readOriginal at h
        split at h <;> simp at h
        subst b
        rfl) read
    have := congrArg (List.map Sigma.fst) originals
    simpa [List.map_map, Function.comp_def, boundOrder] using this

public theorem readGroupChecked_origin {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Tree.Compiled schemaLimits snapshot} {limits : Limits} {group : Nat}
    {result : GroupResult compiled limits group}
    (read : readGroupChecked compiled limits group = .ok result) :
    readColumns compiled limits.chunk group = .ok result.inputs := by
  unfold readGroupChecked at read
  cases admission : admit compiled limits group with
  | error cause => simp [admission, Except.mapError, bind, Except.bind] at read
  | ok checked =>
    cases decoded : readColumns compiled limits.chunk group with
    | error cause => simp [admission, decoded, Except.mapError, bind, Except.bind] at read
    | ok inputs =>
      cases merged : join (schemaWidths compiled) limits.maxSlots schemaLimits.maxSchemaDepth
          compiled.schema.fields checked.value.numRows.toNat (tapes inputs) with
      | error cause => simp [admission, decoded, merged, Except.mapError, bind, Except.bind] at read
      | ok rows =>
        simp [admission, decoded, merged, Except.mapError, bind, Except.bind, pure, Except.pure] at read
        subst result
        rfl

public theorem project_exact {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Tree.Compiled schemaLimits snapshot} {limits : Limits} {group : Nat}
    (result : GroupResult compiled limits group) :
    Projection.trace (schemaWidths compiled) result.inputs.length schemaLimits.maxSchemaDepth
      compiled.schema.fields result.observation.rows =
        some ((result.inputs.map fun input => input.original.atoms).toArray) := by
  have exact := result.exact.exact
  simpa [tapes, Function.comp_def, CheckedColumn.tape, tape_atoms] using exact

public theorem shared_failure {widths : Array Nat} {slotBudget depth : Nat} {fields : List Repeated.Field}
    {requested : Nat} {columns : Array Tape} {failure : {fault // originalFault columns fault}}
    (refused : join widths slotBudget depth fields requested columns = .error failure)
    (shared : failure.val.shared) :
    assemble widths slotBudget depth fields requested columns = .error failure.val := by
  unfold join at refused
  split at refused
  · split at refused
    next fault original =>
      split at refused
      · cases refused
        exact original
      · cases refused
        exact False.elim shared
    next rows original =>
      split at refused
      · split at refused
        · contradiction
        · cases refused
          exact False.elim shared
      · cases refused
        exact False.elim shared
  · cases refused
    exact False.elim shared

public theorem readGroupChecked_join_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Tree.Compiled schemaLimits snapshot} {limits : Limits} {group : Nat} {fault : Fault}
    (read : readGroupChecked compiled limits group = .error (.join fault)) :
    ∃ admission : Admitted compiled limits group, ∃ inputs,
      admit compiled limits group = .ok admission ∧
      readColumns compiled limits.chunk group = .ok inputs ∧
      ∃ witness : originalFault (tapes inputs) fault,
        join (schemaWidths compiled) limits.maxSlots schemaLimits.maxSchemaDepth
          compiled.schema.fields admission.value.numRows.toNat (tapes inputs) = .error ⟨fault, witness⟩ := by
  unfold readGroupChecked at read
  cases admission : admit compiled limits group with
  | error cause => simp [admission, Except.mapError, bind, Except.bind] at read
  | ok checked =>
    cases decoded : readColumns compiled limits.chunk group with
    | error cause => simp [admission, decoded, Except.mapError, bind, Except.bind] at read
    | ok inputs =>
      cases merged : join (schemaWidths compiled) limits.maxSlots schemaLimits.maxSchemaDepth
          compiled.schema.fields checked.value.numRows.toNat (tapes inputs) with
      | ok rows => simp [admission, decoded, merged, Except.mapError, bind, Except.bind, pure, Except.pure] at read
      | error cause =>
        simp [admission, decoded, merged, Except.mapError, bind, Except.bind] at read
        subst fault
        exact ⟨checked, inputs, rfl, rfl, cause.property, merged⟩

public theorem original_boundary {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Tree.Compiled schemaLimits snapshot} {caps : ListPath.Chunk.Limits} {group : Nat}
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
          input.binding.carrier.span.stop, input.original.stop.slots⟩ := by
  unfold originalBoundary tapes at found
  simp only [List.getElem?_toArray, List.getElem?_map] at found
  cases selected : inputs[boundary.point.column.column]? with
  | none => simp [selected] at found
  | some input =>
    refine ⟨input, rfl, ?_⟩
    cases boundary with
    | slot point =>
      change (match (inputs[point.column.column]?.map CheckedColumn.tape) with
        | none => False
        | some tape => tape.slots[point.slot]?.map (·.point) = some point) at found
      simp only [Boundary.point] at selected
      rw [selected] at found
      change (input.tape.slots[point.slot]?.map (·.point)) = some point at found
      obtain ⟨entry, indexed, coordinate⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨page, ordinal, localSlot, atPage, atSlot, exactPoint⟩ := tape_of_slot indexed
      exact ⟨page, ordinal, localSlot, entry, indexed, atPage, atSlot, coordinate.symm.trans exactPoint⟩
    | «end» point =>
      change (match (inputs[point.column.column]?.map CheckedColumn.tape) with
        | none => False
        | some tape => tape.finish = point) at found
      simp only [Boundary.point] at selected
      rw [selected] at found
      exact found.symm

public theorem readGroup_checked {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Tree.Compiled schemaLimits snapshot} {group : Nat}
    {batch : Observation}
    (accepted : readGroup schema limits group = .ok batch) :
    ∃ result, readGroupChecked schema limits group = .ok result ∧ result.observation = batch := by
  unfold readGroup at accepted
  cases read : readGroupChecked schema limits group with
  | error cause => simp [read, Except.map] at accepted
  | ok result =>
    simp [read, Except.map] at accepted
    exact ⟨result, rfl, accepted⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows
