module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Thms
import Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts

open Silmaril.Formats Silmaril.Formats.Parquet
open MixedV1Writer.FromIpc (field toRow physicalOrder prepareOrdered prepareOrdered_exact)
open MixedV1Writer.FromIpc.Complete.PageCuts
open Silmaril.Formats.Relational.NamedTable

theorem split_exact {α : Type} (cuts : List Nat) (slots : List α)
    (extent : cuts.sum = slots.length) :
    (splitSlots cuts slots).flatten = slots ∧ (splitSlots cuts slots).map List.length = cuts := by
  induction cuts generalizing slots with
  | nil =>
    have empty : slots = [] := List.length_eq_zero_iff.mp extent.symm
    simp [splitSlots, empty]
  | cons count rest ih =>
    simp only [List.sum_cons] at extent
    have bound : count ≤ slots.length := by omega
    have tail : rest.sum = (slots.drop count).length := by
      simp only [List.length_drop]
      omega
    obtain ⟨recovered, sizes⟩ := ih _ tail
    exact ⟨by simp [splitSlots, recovered], by simp [splitSlots, sizes, Nat.min_eq_left bound]⟩

theorem validateColumn_checked {maximum ordinal : Nat} {column : Int32ByteArrayGroup.Selection}
    {rows : Nat} {cuts : List Nat} (checked : validateColumn maximum ordinal column rows cuts = .ok ()) :
    cuts.length ≤ maximum ∧ MixedV1Writer.MultiPage.ValidCuts cuts ∧ cuts.sum = rows := by
  unfold validateColumn at checked
  split at checked
  · contradiction
  rename_i maximumOk
  split at checked
  · contradiction
  rename_i shape
  split at checked
  · contradiction
  rename_i extent
  exact ⟨Nat.le_of_not_gt maximumOk, not_not.mp shape, not_not.mp extent⟩

private theorem intCuts_exact (cuts : List Nat) (input : PlainV1Writer.Input)
    (extent : cuts.sum = input.numValues) :
    (cutInts cuts input).map PlainV1Writer.Input.numValues = cuts ∧
    (cutInts cuts input).flatMap PlainV1Writer.Input.slots = input.slots := by
  cases input with
  | required slots =>
    obtain ⟨whole, sizes⟩ := split_exact cuts slots extent
    exact ⟨by simpa [cutInts, PlainV1Writer.Input.numValues, List.map_map, Function.comp_def] using sizes,
      by
        simpa [cutInts, List.flatMap_map, PlainV1Writer.Input.slots, whole]
          using (List.map_flatMap (f := some) (g := id) (l := splitSlots cuts slots)).symm⟩
  | optional slots =>
    obtain ⟨whole, sizes⟩ := split_exact cuts slots extent
    exact ⟨by simpa [cutInts, PlainV1Writer.Input.numValues, List.map_map, Function.comp_def] using sizes,
      by simpa [cutInts, List.flatMap_map, Function.comp_def, PlainV1Writer.Input.slots] using whole⟩

private theorem byteCuts_exact (cuts : List Nat) (input : PlainByteArrayV1Writer.Input)
    (extent : cuts.sum = input.numValues) :
    (cutBytes cuts input).map PlainByteArrayV1Writer.Input.numValues = cuts ∧
    (cutBytes cuts input).flatMap PlainByteArrayV1Writer.Input.slots = input.slots := by
  cases input with
  | required slots =>
    obtain ⟨whole, sizes⟩ := split_exact cuts slots extent
    exact ⟨by simpa [cutBytes, PlainByteArrayV1Writer.Input.numValues, List.map_map, Function.comp_def] using sizes,
      by
        simpa [cutBytes, List.flatMap_map, PlainByteArrayV1Writer.Input.slots, whole]
          using (List.map_flatMap (f := some) (g := id) (l := splitSlots cuts slots)).symm⟩
  | optional slots =>
    obtain ⟨whole, sizes⟩ := split_exact cuts slots extent
    exact ⟨by simpa [cutBytes, PlainByteArrayV1Writer.Input.numValues, List.map_map, Function.comp_def] using sizes,
      by simpa [cutBytes, List.flatMap_map, Function.comp_def, PlainByteArrayV1Writer.Input.slots] using whole⟩

theorem cutGroup_exact {maximum ordinal : Nat} {cuts : BatchCuts}
    {group : MixedV1Writer.Multi.Group} {output : MixedV1Writer.MultiPage.Group}
    (cut : cutGroup maximum ordinal cuts group = .ok output) :
    groupCuts output = cuts ∧ output.intSlots = group.integers.slots ∧ output.byteSlots = group.octets.slots := by
  cases integers : validateColumn maximum ordinal .int32 group.integers.numValues cuts.integers with
  | error cause => simp [cutGroup, integers, Bind.bind, Except.bind] at cut
  | ok result =>
    cases result
    cases bytes : validateColumn maximum ordinal .byteArray group.octets.numValues cuts.octets with
    | error cause => simp [cutGroup, integers, bytes, Bind.bind, Except.bind] at cut
    | ok result =>
      cases result
      simp [cutGroup, integers, bytes, Bind.bind, Except.bind, pure, Except.pure] at cut
      subst output
      obtain ⟨intSizes, intSlots⟩ := intCuts_exact _ _ (validateColumn_checked integers).2.2
      obtain ⟨byteSizes, byteSlots⟩ := byteCuts_exact _ _ (validateColumn_checked bytes).2.2
      exact ⟨by cases cuts; simp_all [groupCuts, MixedV1Writer.MultiPage.Group.intCuts,
        MixedV1Writer.MultiPage.Group.byteCuts], intSlots, byteSlots⟩

private theorem cutGroups_exact {maximum start : Nat} {cuts : Policy}
    {groups : List MixedV1Writer.Multi.Group} {output : List MixedV1Writer.MultiPage.Group}
    (checked : cutGroups maximum start cuts groups = .ok output) :
    output.map groupCuts = cuts ∧ output.map MixedV1Writer.MultiPage.Group.rows =
      groups.map MixedV1Writer.Multi.Group.rows := by
  induction cuts generalizing start groups output with
  | nil =>
    cases groups with
    | nil => cases checked; exact ⟨rfl, rfl⟩
    | cons first rest => simp [cutGroups] at checked
  | cons cut cuts ih =>
    cases groups with
    | nil => simp [cutGroups] at checked
    | cons first rest =>
      cases head : cutGroup maximum start cut first with
      | error cause => simp [cutGroups, head, Bind.bind, Except.bind] at checked
      | ok chunked =>
        cases tail : cutGroups maximum (start + 1) cuts rest with
        | error cause => simp [cutGroups, head, tail, Bind.bind, Except.bind] at checked
        | ok chunkedRest =>
          simp [cutGroups, head, tail, Bind.bind, Except.bind, pure, Except.pure] at checked
          subst output
          obtain ⟨cutsHead, ints, bytes⟩ := cutGroup_exact head
          obtain ⟨cutsTail, rowsTail⟩ := ih tail
          exact ⟨by simp [cutsHead, cutsTail], by
            simp [MixedV1Writer.MultiPage.Group.rows, MixedV1Writer.Multi.Group.rows, ints, bytes, rowsTail]⟩

theorem prepare_exact {limits : MixedV1Writer.MultiPage.Limits} {policy : Policy} {observed : MixedIpc.Prepared}
    {plan : MixedV1Writer.MultiPage.Input} (ready : prepare limits policy observed = .ok plan) :
    plan.intField = field observed.descriptor.integer ∧ plan.byteField = field observed.descriptor.binary ∧
    plan.groups.map groupCuts = policy ∧
    plan.groups.map MixedV1Writer.MultiPage.Group.rows = observed.batches.map (List.map toRow) := by
  by_cases count : policy.length = observed.batches.length
  · by_cases cap : limits.maxPages < (policy.map BatchCuts.pageCount).sum
    · simp [prepare, count, cap, Bind.bind, Except.bind, throw] at ready
    cases prepared : prepareOrdered observed with
    | error cause => simp [prepare, count, cap, prepared, Except.mapError, Bind.bind, Except.bind] at ready
    | ok original =>
      cases cuts : cutGroups limits.maxPagesPerChunk 0 policy original.groups with
      | error cause => simp [prepare, count, cap, prepared, cuts, Except.mapError, Bind.bind, Except.bind] at ready
      | ok groups =>
        simp [prepare, count, cap, prepared, cuts, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] at ready
        subst plan
        obtain ⟨_, integer, binary, rows⟩ := prepareOrdered_exact prepared
        obtain ⟨policyExact, rowsExact⟩ := cutGroups_exact cuts
        exact ⟨integer, binary, policyExact, rowsExact.trans rows⟩
  · simp [prepare, count, Bind.bind, Except.bind, throw] at ready

theorem convert_groups_checked {source : MixedIpc.Limits} {limits : MixedV1Writer.MultiPage.Limits}
    {policy : Policy} {input : KBytes} {bytes : Bytes} {observed : MixedIpc.Prepared}
    (read : MixedIpc.read source input = .ok observed) (nonempty : observed.batches ≠ [])
    (written : convert source limits policy input = .ok bytes) :
    ∃ plan output, prepare limits policy observed = .ok plan ∧
      MixedV1Writer.MultiPage.emit (physicalOrder observed.descriptor) limits plan = .ok output ∧
      output.bytes = bytes := by
  cases batches : observed.batches with
  | nil => exact (nonempty batches).elim
  | cons first rest =>
    cases prepared : prepare limits policy observed with
    | error cause => simp [convert, read, batches, prepared, Except.mapError, Bind.bind, Except.bind] at written
    | ok plan =>
      cases emitted : MixedV1Writer.MultiPage.emit (physicalOrder observed.descriptor) limits plan with
      | error cause => simp [convert, read, batches, prepared, emitted, Except.mapError, Except.map,
          Bind.bind, Except.bind] at written
      | ok output =>
        simp [convert, read, batches, prepared, emitted, Except.mapError, Except.map, Bind.bind, Except.bind] at written
        exact ⟨plan, output, rfl, emitted, written⟩

theorem read_roundTrip {source returned : MixedIpc.Limits} {limits : MixedV1Writer.MultiPage.Limits}
    {policy : Policy} {reverse : Int32ByteArrayGroup.File.Limits} {input output : KBytes}
    {bytes : Bytes} {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source limits policy input = .ok bytes)
    (groupLimits : reverse.group = limits.file.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = limits.file.writer.footer)
    (backward : Int32ByteArrayGroup.ToIpc.convertOrdered reverse returned.mixed bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed := by
  by_cases empty : observed.batches = []
  · rcases observed with ⟨descriptor, batches⟩
    change batches = [] at empty
    subst batches
    cases policy with
    | cons head tail => simp [convert, original, Except.mapError, Bind.bind, Except.bind, throw] at forward
    | nil =>
      cases emitted : MixedV1Writer.FromIpc.SchemaOnly.emit limits.file descriptor with
      | error cause => simp [convert, original, emitted, Except.mapError, Except.map, Bind.bind, Except.bind] at forward
      | ok file =>
        simp [convert, original, emitted, Except.mapError, Except.map, Bind.bind, Except.bind] at forward
        subst bytes
        have explicit : MixedV1Writer.FromIpc.SchemaOnly.convert source limits.file input = .ok file := by
          simp [MixedV1Writer.FromIpc.SchemaOnly.convert, original, emitted, Except.mapError, Bind.bind, Except.bind]
        exact (MixedV1Writer.FromIpc.RoundTrip.read_roundTripSchemaOnly
          original explicit groupLimits footerLimits backward carrier).1
  · obtain ⟨⟨integer, binary, groups⟩, file, prepared, emitted, rfl⟩ := convert_groups_checked original empty forward
    obtain ⟨integerExact, binaryExact, _, rows⟩ := prepare_exact prepared
    change integer = field observed.descriptor.integer at integerExact
    change binary = field observed.descriptor.binary at binaryExact
    subst integer
    subst binary
    have length : groups.length = observed.batches.length := by
      simpa using congrArg List.length rows
    obtain ⟨projection, opened, count, indexed⟩ := MixedV1Writer.MultiPage.emit_indexed emitted
    obtain ⟨_, verified, _⟩ := MixedV1Writer.MultiPage.emit_checked emitted
    obtain ⟨_, _, _, _, _, _, _, footer, _⟩ := verified
    rcases observed with ⟨descriptor, batches⟩
    refine MixedV1Writer.FromIpc.RoundTrip.read_of_indexed (by rw [groupLimits]; exact opened)
      (count.trans length) (fun i => ?_) (by rw [footerLimits]; exact footer) rfl backward carrier
    let j : Fin groups.length := ⟨i.val, by rw [length]; exact i.isLt⟩
    have atOrdinal := congrArg (fun xs : List (List Int32ByteArrayGroup.Row) => xs[i.val]?) rows
    have sameRows : (groups.get j).rows = (batches.get i).map toRow := by
      simpa [List.getElem?_map, List.getElem?_eq_getElem, List.get_eq_getElem, i.isLt, j, length] using atOrdinal
    rw [groupLimits, ← sameRows]
    exact (indexed j).1

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts
