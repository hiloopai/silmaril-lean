module

public import Silmaril.Formats.Parquet.Footer.PageLessTimestamp.Defs
import Init.Data.List.Zip

public section

namespace Silmaril.Proofs.Formats.Parquet.Footer.PageLessTimestamp

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Footer
open Silmaril.Formats.Parquet.Footer.PageLessTimestamp
open Silmaril.Formats.ThriftCompact.Traversal (Reader Field)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem pageLess_zero {group : RowGroup} (empty : isPageLess group = true) :
    group.numRows = 0 ∧ group.totalByteSize = 0 ∧ group.fileOffset = some 0 ∧
      group.totalCompressedSize = some 0 ∧ group.columns ≠ [] ∧
      ∀ col ∈ group.columns,
        col.metadata.numValues = 0 ∧ col.metadata.totalCompressedSize = 0 ∧
        col.metadata.totalUncompressedSize = 0 ∧ col.metadata.dataPageOffset = 0 ∧
        col.metadata.dictionaryPageOffset = none ∧ col.metadata.indexPageOffset = none := by
  simp [isPageLess, Bool.and_eq_true, List.all_eq_true] at empty
  obtain ⟨⟨⟨⟨⟨rows, bytes⟩, offset⟩, stored⟩, present⟩, columns⟩ := empty
  refine ⟨rows, bytes, offset, stored, present, fun col member => ?_⟩
  have checked := columns col member
  simp [noFrames, Bool.and_eq_true] at checked
  grind

theorem validate_wire {limits : Limits} {depth : Nat} {source : Bytes}
    {span : Span} {metadata : Metadata}
    (admitted : PageLessTimestamp.validate limits depth source span metadata = .ok ()) :
    Footer.validate span.start depth { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) } = .ok () ∧
      let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
      ∃ raw, PageLessInt32.Internal.groups reader = .ok raw ∧ raw.length = metadata.rowGroups.length ∧
        Internal.layout reader span.start metadata.schema 0 4 (metadata.rowGroups.zip raw) = .ok span.start := by
  unfold PageLessTimestamp.validate at admitted
  cases profile : metadata.version == 2 && flatSchema metadata.schema with
  | false => simp [profile, Bind.bind, Except.bind] at admitted
  | true =>
    simp only [profile, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at admitted
    obtain ⟨checked, strict, admitted⟩ := bind_ok admitted
    cases checked
    obtain ⟨raw, read, admitted⟩ := bind_ok admitted
    by_cases count : raw.length = metadata.rowGroups.length
    · simp only [count, ne_eq, not_true_eq_false, ↓reduceIte] at admitted
      obtain ⟨stop, tiled, admitted⟩ := bind_ok admitted
      by_cases extent : stop = span.start
      · subst stop
        exact ⟨mapError_ok strict, raw, mapError_ok read, count, tiled⟩
      · simp [extent] at admitted
    · simp [count, Bind.bind, Except.bind] at admitted

theorem groupStop_empty {reader : Reader} {footerStart index cursor stop : Nat}
    {schema : List SchemaElement} {group : RowGroup} {raw : List Field}
    (empty : isPageLess group = true)
    (checked : Internal.groupStop reader footerStart schema index cursor group raw = .ok stop) :
    matchesColumns schema group = true ∧
      Internal.checkEmptyRaw reader index group.columns.length raw = .ok () ∧ stop = cursor := by
  unfold Internal.groupStop at checked
  obtain ⟨ignored, _, checked⟩ := bind_ok checked
  cases ignored
  by_cases columns : matchesColumns schema group = true
  · simp only [empty, columns, ↓reduceIte, Bool.not_true, Bool.false_eq_true, pure, Except.pure] at checked
    obtain ⟨ignored, rawCheck, checked⟩ := bind_ok checked
    cases ignored
    exact ⟨columns, mapError_ok rawCheck, (Except.ok.inj checked).symm⟩
  · simp [empty, columns, Bind.bind, Except.bind] at checked

theorem layout_group {reader : Reader} {footerStart base cursor stop index : Nat}
    {schema : List SchemaElement} {groups : List (RowGroup × List Field)}
    {group : RowGroup} {raw : List Field}
    (found : groups[index]? = some (group, raw))
    (checked : Internal.layout reader footerStart schema base cursor groups = .ok stop) :
    ∃ start finish, Internal.groupStop reader footerStart schema (base + index) start group raw = .ok finish := by
  induction groups generalizing base cursor index with
  | nil => simp at found
  | cons head tail ih =>
    obtain ⟨top, fields⟩ := head
    simp only [Internal.layout] at checked
    obtain ⟨next, step, checked⟩ := bind_ok checked
    cases index with
    | zero =>
      simp at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨cursor, next, step⟩
    | succ index =>
      rw [List.getElem?_cons_succ] at found
      obtain ⟨start, finish, groupChecked⟩ := ih found checked
      exact ⟨start, finish, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using groupChecked⟩

theorem validate_empty {limits : Footer.Limits} {depth : Nat} {source : Bytes}
    {span : Span} {metadata : Metadata} {index : Nat} {group : RowGroup}
    (admitted : PageLessTimestamp.validate limits depth source span metadata = .ok ())
    (found : metadata.rowGroups[index]? = some group) (empty : isPageLess group = true) :
    matchesColumns metadata.schema group = true ∧
      let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
      ∃ raw fields, PageLessInt32.Internal.groups reader = .ok raw ∧
        raw[index]? = some fields ∧ Internal.checkEmptyRaw reader index group.columns.length fields = .ok () := by
  obtain ⟨_, raw, original, count, tiled⟩ := validate_wire admitted
  have validIndex : index < metadata.rowGroups.length := (List.getElem?_eq_some_iff.mp found).1
  have rawIndex : index < raw.length := count.symm ▸ validIndex
  have rawFound : raw[index]? = some raw[index] := List.getElem?_eq_getElem rawIndex
  have paired : (metadata.rowGroups.zip raw)[index]? = some (group, raw[index]) := by
    exact List.getElem?_zip_eq_some.mpr ⟨found, rawFound⟩
  obtain ⟨_, _, checked⟩ := layout_group paired tiled
  obtain ⟨columns, rawChecked, _⟩ := groupStop_empty empty checked
  exact ⟨columns, raw, raw[index], original, rawFound, by simpa only [Nat.zero_add] using rawChecked⟩

end Silmaril.Proofs.Formats.Parquet.Footer.PageLessTimestamp
