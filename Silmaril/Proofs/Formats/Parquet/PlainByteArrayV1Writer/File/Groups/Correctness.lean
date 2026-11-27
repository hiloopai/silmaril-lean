module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Formats.Parquet.Snapshot.Footer.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Groups

variable {limits : Limits} {input : Input} {output : Encoded}

theorem emit_checked (written : emit limits input = .ok output) :
    input.groups.length ≤ limits.groupLimit ∧ input.totalRows ≤ limits.rowLimit ∧
      output.Checked limits input ∧ certify limits input output = .ok () := by
  simp only [emit, Bind.bind, Except.bind] at written
  split at written
  · contradiction
  rename_i groups
  split at written
  · contradiction
  rename_i rows
  split at written
  · contradiction
  cases built : assemble limits input with
  | error cause => simp [built] at written
  | ok packed =>
    simp only [built] at written
    cases certified : certify limits input packed with
    | error cause => simp [certified] at written
    | ok checkedUnit =>
      cases checkedUnit
      simp only [certified] at written
      split at written
      · rename_i exactLayout
        have same : packed = output := Except.ok.inj written
        subst output
        exact ⟨Nat.le_of_not_gt groups, Nat.le_of_not_gt rows, exactLayout, certified⟩
      · contradiction

private theorem certify_steps (certified : certify limits input output = .ok ()) :
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits.file output.bytes input.name input.layout = .ok checked ∧
      checked.snapshot.footer = output.footer ∧ checked.snapshot.metadata = metadata input output ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits.file) = .ok input.groups := by
  cases opened : Plain.ByteArray.File.openFile limits.file output.bytes input.name input.layout with
  | error cause => simp [certify, opened, Except.mapError, Bind.bind, Except.bind] at certified
  | ok checked =>
    by_cases mismatch : checked.snapshot.footer ≠ output.footer ∨ checked.snapshot.metadata ≠ metadata input output
    · simp [certify, opened, mismatch, Except.mapError, Bind.bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw] at certified
    cases groups : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits.file) with
    | error cause => simp [certify, opened, mismatch, groups, Except.mapError, Bind.bind, Except.bind] at certified
    | ok slots =>
      by_cases same : slots = input.groups
      · have ⟨exactFooter, exactMeta⟩ : checked.snapshot.footer = output.footer ∧
            checked.snapshot.metadata = metadata input output := by
          simpa only [not_or, not_not] using mismatch
        exact ⟨checked, rfl, exactFooter, exactMeta, groups.trans (congrArg Except.ok same)⟩
      · simp [certify, opened, mismatch, groups, same, Except.mapError, Bind.bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at certified

theorem emit_bounds (written : emit limits input = .ok output) :
    input.groups.length ≤ limits.maxGroups ∧
    input.groups.length ≤ limits.file.snapshot.footer.compact.maxCollectionSize ∧
    input.totalRows ≤ limits.file.maxFileRows ∧ input.totalRows < 2^63 ∧
    output.bytes.length ≤ limits.file.maxFileBytes ∧ output.bytes.length < 2^63 := by
  obtain ⟨groups, rows, checked, _⟩ := emit_checked written
  obtain ⟨groupsCap, compactCap⟩ := Nat.le_min.mp groups
  obtain ⟨rowCap, signedRows⟩ := Nat.le_min.mp rows
  obtain ⟨byteCap, signedBytes⟩ := Nat.le_min.mp checked.1
  exact ⟨groupsCap, compactCap, rowCap, by omega, byteCap, by omega⟩

theorem emit_indexed (written : emit limits input = .ok output) :
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits.file output.bytes input.name input.layout = .ok checked ∧
      Footer.readFooter limits.file.snapshot.footer output.bytes = .ok (output.footer, metadata input output) ∧
      checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        checked.readGroup limits.file i.val = .ok (input.groups.get i) ∧
        ∃ group, (metadata input output).rowGroups[i.val]? = some group ∧
          Plain.ByteArray.File.GroupWire checked limits.file i.val group (input.groups.get i) := by
  obtain ⟨_, _, _, certified⟩ := emit_checked written
  obtain ⟨checked, opened, footer, shape, read⟩ := certify_steps certified
  have snapshot := (Plain.ByteArray.File.openFile_wire opened).1
  have parsedFooter := Snapshot.check_footer snapshot
  rw [footer, shape] at parsedFooter
  have ordinal : checked.binding.columnOrdinal = 0 := by
    have leafAt := checked.binding.leafAt
    rw [shape] at leafAt
    cases column : checked.binding.columnOrdinal with
    | zero => rfl
    | succ index => simp [metadata, column] at leafAt
  have indices := List.mapM_eq_ok_iff_forall₂.mp read
  have count : checked.snapshot.groupCount = input.groups.length := by
    simpa using indices.length_eq
  refine ⟨checked, opened, parsedFooter, ordinal, count, fun i => ?_⟩
  have leftBound : i.val < (List.range checked.snapshot.groupCount).length := by
    simp [count]
  have atIndex : checked.readGroup limits.file i.val = .ok (input.groups.get i) := by
    simpa using indices.get leftBound i.isLt
  obtain ⟨group, wire⟩ := Plain.ByteArray.File.readGroup_wire atIndex
  have original : checked.snapshot.groupAt i.val = some group := by
    obtain ⟨_, _, _, _, groupAt, _⟩ := wire
    exact groupAt
  rw [(Snapshot.check_groups snapshot).2, shape] at original
  exact ⟨atIndex, group, original, wire⟩

theorem emit_group_extent (written : emit limits input = .ok output) {group : Group}
    (member : group ∈ output.groups) :
    group.Wire input limits output.bytes output.footer.start ∧
      (group.span.start : Int) = (group.chunk input).metadata.dataPageOffset ∧
      (group.span.stop : Int) = (group.chunk input).metadata.dataPageOffset +
        (group.chunk input).metadata.totalCompressedSize ∧
      4 ≤ group.span.start ∧ group.span.start < group.span.stop ∧
      group.span.stop ≤ output.footer.start ∧ group.span.stop < 2^63 := by
  have checked := (emit_checked written).2.2.1
  have wire := checked.2.2.2 group member
  obtain ⟨start, stop, lower, positive, beforeFooter⟩ := Footer.checkDataSpan_some_iff.mp wire.1
  obtain ⟨_, _, _, _, _, cap⟩ := emit_bounds written
  have upper := (Page.readChunk_chain wire.2.1).2.1
  exact ⟨wire, start, stop, lower, positive, beforeFooter, Nat.lt_of_le_of_lt upper cap⟩

theorem emit_footer_groups (written : emit limits input = .ok output) :
    (metadata input output).numRows = input.totalRows ∧
    ∀ i : Fin input.groups.length, ∃ group,
      output.groups[i.val]? = some group ∧
      (metadata input output).rowGroups[i.val]? = some (group.rowGroup input) ∧
      group.rows = (input.groups.get i).length ∧
      group.Wire input limits output.bytes output.footer.start := by
  have ⟨_, rows, _, extent⟩ := (emit_checked written).2.2.1
  have count := congrArg List.length rows
  simp only [List.length_map] at count
  refine ⟨?_, fun i => ?_⟩
  · simp [metadata, Input.totalRows, rows]
  · have bound : i.val < output.groups.length := count.symm ▸ i.isLt
    let group := output.groups[i.val]
    have selected : output.groups[i.val]? = some group := List.getElem?_eq_getElem bound
    have rowCount := congrArg (fun sizes : List Nat => sizes[i.val]?) rows
    rw [List.getElem?_map, List.getElem?_map, selected, List.getElem?_eq_getElem i.isLt] at rowCount
    refine ⟨group, selected, ?_, Option.some.inj rowCount, extent group (List.mem_of_getElem? selected)⟩
    simp [metadata, List.getElem?_map, selected]

end Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.File.Groups
