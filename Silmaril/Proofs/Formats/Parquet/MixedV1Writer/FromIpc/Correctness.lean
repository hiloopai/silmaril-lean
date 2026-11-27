module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc
open Silmaril.Formats.Parquet.MixedV1Writer
open Silmaril.Formats.Relational.NamedTable

private theorem required_exact {α : Type} {slots : List (Option α)} {values : List α}
    (checked : slots.mapM id = some values) : values.map some = slots := by
  induction slots generalizing values with
  | nil =>
    cases checked
    rfl
  | cons slot rest ih =>
    cases slot with
    | none => simp [List.mapM_cons] at checked
    | some value =>
      cases tail : rest.mapM id with
      | none => simp [List.mapM_cons, tail] at checked
      | some restValues =>
        simp [List.mapM_cons, tail] at checked
        subst values
        simp [ih tail]

private theorem prepareInt_exact {nullable : Bool} {ordinal : Nat} {slots : List (Option Int32)}
    {input : PlainV1Writer.Input} (checked : prepareInt nullable ordinal slots = .ok input) :
    input.slots = slots := by
  cases nullable
  · cases admitted : slots.mapM id with
    | none => simp [prepareInt, admitted] at checked
    | some values =>
      simp [prepareInt, admitted] at checked
      subst input
      exact required_exact admitted
  · simp [prepareInt] at checked
    subst input
    rfl

private theorem prepareBytes_exact {nullable : Bool} {ordinal : Nat} {slots : List (Option Bytes)}
    {input : PlainByteArrayV1Writer.Input} (checked : prepareBytes nullable ordinal slots = .ok input) :
    input.slots = slots := by
  cases nullable
  · cases admitted : slots.mapM id with
    | none => simp [prepareBytes, admitted] at checked
    | some values =>
      simp [prepareBytes, admitted] at checked
      subst input
      exact required_exact admitted
  · simp [prepareBytes] at checked
    subst input
    rfl

private theorem prepareGroup_exact {descriptor : MixedIpc.Descriptor} {index : Nat}
    {pairs : List MixedIpc.Pair} {group : Multi.Group}
    (checked : prepareGroup descriptor index pairs = .ok group) :
    group.rows = pairs.map toRow := by
  cases ints : prepareInt descriptor.integer.2 index (pairs.map Prod.fst) with
  | error cause => simp [prepareGroup, ints, Bind.bind, Except.bind] at checked
  | ok integer =>
    cases bytes : prepareBytes descriptor.binary.2 index (pairs.map fun pair => pair.2.map Bytes.ofList) with
    | error cause => simp [prepareGroup, ints, bytes, Bind.bind, Except.bind] at checked
    | ok binary =>
      simp [prepareGroup, ints, bytes, Bind.bind, Except.bind, pure, Except.pure] at checked
      subst group
      simp [Multi.Group.rows, prepareInt_exact ints, prepareBytes_exact bytes, List.zip_map', toRow]

private theorem prepareGroups_exact {descriptor : MixedIpc.Descriptor} {ordinal : Nat}
    {batches : List (List MixedIpc.Pair)} {groups : List Multi.Group}
    (checked : prepareGroups descriptor ordinal batches = .ok groups) :
    groups.map Multi.Group.rows = batches.map (List.map toRow) := by
  induction batches generalizing ordinal groups with
  | nil =>
    cases checked
    rfl
  | cons pairs rest ih =>
    cases group : prepareGroup descriptor ordinal pairs with
    | error cause => simp [prepareGroups, group, Bind.bind, Except.bind] at checked
    | ok head =>
      cases tail : prepareGroups descriptor (ordinal + 1) rest with
      | error cause => simp [prepareGroups, group, tail, Bind.bind, Except.bind] at checked
      | ok remaining =>
        simp [prepareGroups, group, tail, Bind.bind, Except.bind, pure, Except.pure] at checked
        subst groups
        exact congrArg₂ List.cons (prepareGroup_exact group) (ih tail)

theorem prepareOrdered_exact {source : MixedIpc.Prepared} {plan : Multi.Input}
    (checked : prepareOrdered source = .ok plan) :
    source.batches ≠ [] ∧
    plan.intField = field source.descriptor.integer ∧ plan.byteField = field source.descriptor.binary ∧
    plan.groups.map Multi.Group.rows = source.batches.map (List.map toRow) := by
  by_cases empty : source.batches = []
  · simp [prepareOrdered, empty] at checked
  cases admitted : prepareGroups source.descriptor 0 source.batches with
  | error cause => simp [prepareOrdered, empty, admitted, Except.map] at checked
  | ok groups =>
    simp [prepareOrdered, empty, admitted, Except.map] at checked
    subst plan
    exact ⟨empty, rfl, rfl, prepareGroups_exact admitted⟩

theorem prepare_exact {source : MixedIpc.Prepared} {plan : Multi.Input}
    (checked : prepare source = .ok plan) :
    source.descriptor.viewFirst = false ∧ source.batches ≠ [] ∧
    plan.intField = field source.descriptor.integer ∧ plan.byteField = field source.descriptor.binary ∧
    plan.groups.map Multi.Group.rows = source.batches.map (List.map toRow) := by
  cases order : source.descriptor.viewFirst
  · exact ⟨rfl, prepareOrdered_exact (by simpa [prepare, order] using checked)⟩
  · simp [prepare, order] at checked

theorem convertOrdered_ok_iff {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {output : Multi.Encoded} :
    convertOrdered source sink input = .ok output ↔
      ∃ observed plan, MixedIpc.read source input = .ok observed ∧
        prepareOrdered observed = .ok plan ∧
        Multi.emitOrdered (physicalOrder observed.descriptor) sink plan = .ok output := by
  cases decoded : MixedIpc.read source input with
  | error cause => simp [convertOrdered, decoded, Except.mapError, Bind.bind, Except.bind]
  | ok observed =>
    cases planned : prepareOrdered observed with
    | error cause => simp [convertOrdered, emitOrderedPrepared, decoded, planned, Except.mapError, Bind.bind, Except.bind]
    | ok plan =>
      cases emitted : Multi.emitOrdered (physicalOrder observed.descriptor) sink plan <;>
        simp [convertOrdered, emitOrderedPrepared, decoded, planned, emitted, Except.mapError, Bind.bind, Except.bind]

theorem convert_ok_iff {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {output : Multi.Encoded} :
    convert source sink input = .ok output ↔
      ∃ observed plan, MixedIpc.read source input = .ok observed ∧
        prepare observed = .ok plan ∧ Multi.emit sink plan = .ok output := by
  cases decoded : MixedIpc.read source input with
  | error cause => simp [convert, decoded, Except.mapError, Bind.bind, Except.bind]
  | ok observed =>
    cases planned : prepare observed with
    | error cause => simp [convert, decoded, planned, Except.mapError, Bind.bind, Except.bind]
    | ok plan =>
      cases emitted : Multi.emit sink plan <;>
        simp [convert, decoded, planned, emitted, Except.mapError, Bind.bind, Except.bind]

theorem emit_indexed_of_plan {sink : Multi.Limits} {order : Order} {output : Multi.Encoded}
    {observed : MixedIpc.Prepared} {plan : Multi.Input}
    (planned : prepareOrdered observed = .ok plan)
    (emitted : Multi.emitOrdered order sink plan = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked (field observed.descriptor.integer) (field observed.descriptor.binary),
      Int32ByteArrayGroup.openFile sink.writer.readback output.bytes
        (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok opened ∧
      opened.snapshot.groupCount = observed.batches.length ∧
      ∀ i : Fin observed.batches.length,
        opened.readGroup sink.writer.readback i.val = .ok ((observed.batches.get i).map toRow) ∧
        Int32ByteArrayGroup.GroupWire opened sink.writer.readback i.val ((observed.batches.get i).map toRow) := by
  obtain ⟨intField, byteField, groups⟩ := plan
  obtain ⟨_, intLabel, byteLabel, paired⟩ := prepareOrdered_exact planned
  change intField = field observed.descriptor.integer at intLabel
  change byteField = field observed.descriptor.binary at byteLabel
  subst intField
  subst byteField
  have length : groups.length = observed.batches.length := by
    simpa using congrArg List.length paired
  obtain ⟨opened, openedOk, count, indexed⟩ := Multi.emitOrdered_indexed emitted
  refine ⟨opened, openedOk, count.trans length, ?_⟩
  intro i
  let j : Fin groups.length := ⟨i.val, by rw [length]; exact i.isLt⟩
  have rows := congrArg (fun xs : List (List Int32ByteArrayGroup.Row) => xs[i.val]?) paired
  have exactRows : (groups.get j).rows = (observed.batches.get i).map toRow := by
    simpa [List.getElem?_map, List.getElem?_eq_getElem, List.get_eq_getElem, i.isLt, j, length] using rows
  exact exactRows ▸ indexed j

theorem convert_indexed {source : MixedIpc.Limits} {sink : Multi.Limits} {input : KBytes}
    {output : Multi.Encoded} (written : convert source sink input = .ok output) :
    ∃ (observed : MixedIpc.Prepared) (opened : Int32ByteArrayGroup.Checked
        (field observed.descriptor.integer) (field observed.descriptor.binary)),
      MixedIpc.read source input = .ok observed ∧
      observed.descriptor.viewFirst = false ∧
      Int32ByteArrayGroup.openFile sink.writer.readback output.bytes
        (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok opened ∧
      opened.snapshot.groupCount = observed.batches.length ∧
      ∀ i : Fin observed.batches.length,
        opened.readGroup sink.writer.readback i.val = .ok ((observed.batches.get i).map toRow) ∧
        Int32ByteArrayGroup.GroupWire opened sink.writer.readback i.val ((observed.batches.get i).map toRow) := by
  obtain ⟨observed, plan, read, planOk, emitted⟩ := convert_ok_iff.mp written
  have order := (prepare_exact planOk).1
  have planned : prepareOrdered observed = .ok plan := by simpa [prepare, order] using planOk
  obtain ⟨opened, openedOk, count, indexed⟩ := emit_indexed_of_plan planned emitted
  exact ⟨observed, opened, read, order, openedOk, count, indexed⟩

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc
