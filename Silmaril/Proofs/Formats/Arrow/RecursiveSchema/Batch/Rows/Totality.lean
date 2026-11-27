module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows

open Silmaril.Formats.Arrow.RecursiveSchema hiding Limits Error readFrame
open Silmaril.Formats.Arrow.RecursiveSchema.Batch hiding readFirst
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics
  (Column ColumnWire ColumnsWire PresenceWire Presence SignedWords listVisibility listVisibility_window)

private theorem bitmap_size {body : KBytes} {node : Formats.Arrow.FieldNode}
    {bitmap : Formats.Arrow.Buffer} {nullable : Bool} {visible : Array Bool} {presence : Presence}
    (wire : PresenceWire body node bitmap nullable visible presence) :
    presence.valid.size = node.length := by
  simpa using wire.fromBitmap.length_eq.symm

private theorem signed_size {α : Type} {width count : Nat} {interpret : List UInt8 → α}
    {bytes : KBytes} {words : List α} (wire : SignedWords width count interpret bytes words) :
    words.length = count := by
  obtain ⟨_, _, extent, _, mapped⟩ := wire
  simpa [mapped] using extent

private theorem singleton_size {carrier : Carrier} {depth length : Nat} {fields start layouts next visible}
    {column : Column} (layout : FieldsWire carrier depth length fields start layouts next)
    (physical : ColumnsWire carrier.body visible fields layouts [column]) :
    (IndexedColumn.ofColumn column).length = length := by
  cases physical with
  | cons first rest =>
    cases layout with
    | cons head _ =>
      cases head with
      | field _ node _ _ _ _ =>
        cases first with
        | node bitmap _ _ =>
          simpa [IndexedColumn.ofColumn, IndexedColumn.length] using
            (bitmap_size bitmap).trans node.length_eq

private theorem mapM_total {α β ε : Type} {f : α → Except ε β} {items : List α}
    (total : ∀ item ∈ items, ∃ checked, f item = .ok checked) :
    ∃ checked, items.mapM f = .ok checked := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
    obtain ⟨first, readFirst⟩ := total head (by simp)
    obtain ⟨rest, readRest⟩ := ih (fun item member => total item (by simp [member]))
    exact ⟨first :: rest, by simp [List.mapM_cons, readFirst, readRest, bind, Except.bind, pure, Except.pure]⟩

private theorem row_total {carrier : Carrier} {depth length : Nat} {fields start layouts next}
    (layout : FieldsWire carrier depth length fields start layouts next) :
    ∀ {visible columns}, ColumnsWire carrier.body visible fields layouts columns →
      ∀ {slot}, visible[slot]? = some true →
      ∃ row, (columns.mapM fun column => readCell depth (IndexedColumn.ofColumn column) slot) = .ok row := by
  refine FieldsWire.rec
    (motive_1 := fun depth _ field _ layout _ _ =>
      ∀ {visible column}, ColumnWire carrier.body visible field layout column →
        ∀ {slot}, visible[slot]? = some true →
        ∃ value, readCell depth (IndexedColumn.ofColumn column) slot = .ok value)
    (motive_2 := fun depth _ fields _ layouts _ _ =>
      ∀ {visible columns}, ColumnsWire carrier.body visible fields layouts columns →
        ∀ {slot}, visible[slot]? = some true →
        ∃ row, (columns.mapM fun column => readCell depth (IndexedColumn.ofColumn column) slot) = .ok row)
    ?_ ?_ ?_ layout
  · intro depth length name nullable kind fields start node bitmap buffer childLength childStart
      childLayouts next arity nodeWire bitmapWire extent layoutPayload layoutChildren childTotal
      visible column physical slot reached
    cases physical with
    | node bits payloadWire childrenWire =>
      rename_i presence payload children
      have seen : presence.visible[slot]? = some true := bits.fromAncestors ▸ reached
      have bound := (Array.getElem?_eq_some_iff.mp reached).choose
      rw [bits.visibilityLength] at bound
      have inBitmap : slot < presence.valid.size := by simpa [bitmap_size bits] using bound
      cases bit : presence.valid[slot] with
      | false =>
        have absent := (Array.getElem?_eq_getElem inBitmap).trans (congrArg some bit)
        exact ⟨none, by simp [IndexedColumn.ofColumn, readCell, seen, absent, pure, Except.pure]⟩
      | true =>
        have valid := (Array.getElem?_eq_getElem inBitmap).trans (congrArg some bit)
        have present : presence.present[slot]? = some true := by
          simp [Presence.present, Array.getElem?_zipWith, seen, valid]
        cases payloadWire with
        | @int32 _ values words =>
          have inWords : slot < values.length := by simpa [signed_size words] using bound
          exact ⟨some (.int32 values[slot]), by
            simp [IndexedColumn.ofColumn, IndexedPayload.ofPayload, readCell, seen, valid,
              List.getElem?_eq_getElem inWords, pure, Except.pure]⟩
        | @int64 _ values words =>
          have inWords : slot < values.length := by simpa [signed_size words] using bound
          exact ⟨some (.int64 values[slot]), by
            simp [IndexedColumn.ofColumn, IndexedPayload.ofPayload, readCell, seen, valid,
              List.getElem?_eq_getElem inWords, pure, Except.pure]⟩
        | struct =>
          obtain ⟨values, decoded⟩ := childTotal childrenWire present
          exact ⟨some (.struct values), by simp [IndexedColumn.ofColumn, IndexedPayload.ofPayload,
            readCell, seen, valid, List.mapM_map, Function.comp_def, decoded, bind, Except.bind, pure, Except.pure]⟩
        | @list _ offsets offsetsWire =>
          cases layoutPayload with
          | values integer _ _ => rcases integer with h | h <;> cases h
          | offsets _ _ checked =>
            have observation := Semantics.PayloadWire.list offsetsWire
            obtain ⟨lo, hi, startWord, endWord, _, _, sorted, bounded⟩ := observation.list_window checked bound
            have sized : presence.present.size = node.length := by
              rw [Presence.present, Array.size_zipWith, bits.fromAncestors, bits.visibilityLength, bitmap_size bits]
              exact Nat.min_self _
            obtain ⟨initial, _⟩ := observation.list_endpoints checked
            have ordered : ∀ i < presence.present.size, offsets[i]?.getD 0 ≤ offsets[i + 1]?.getD 0 := by
              intro i validIndex
              obtain ⟨_, _, loWord, hiWord, _, _, order, _⟩ :=
                observation.list_window checked (sized ▸ validIndex)
              simpa [loWord, hiWord] using order
            cases childrenWire with
            | nil => simp [validArity] at arity
            | cons only tail =>
              cases tail with
              | cons _ _ => simp [validArity] at arity
              | nil =>
                rename_i child
                have childSized := singleton_size layoutChildren (.cons only .nil)
                have total : ∀ i ∈ List.range' lo (hi - lo),
                    ∃ value, readCell depth (IndexedColumn.ofColumn child) i = .ok value := by
                  intro i member
                  obtain ⟨index, indexBound, rfl⟩ := List.mem_range'.mp member
                  simp only [Nat.one_mul]
                  have inherited := listVisibility_window (present := presence.present) (offsets := offsets)
                    (parent := slot) (child := lo + index)
                    (by simp [initial]) ordered (by simpa [sized] using bound) (by simp [startWord])
                    (by simp only [endWord, Option.getD_some]; omega)
                  obtain ⟨values, decoded⟩ := childTotal (.cons only .nil) (inherited.trans present)
                  cases slotRead : readCell depth (IndexedColumn.ofColumn child) (lo + index) with
                  | error cause => simp [slotRead] at decoded
                  | ok value => exact ⟨value, rfl⟩
                obtain ⟨values, decoded⟩ := mapM_total total
                have fits : hi ≤ (IndexedColumn.ofColumn child).length := childSized ▸ bounded
                exact ⟨some (.list values), by
                  simp [IndexedColumn.ofColumn, IndexedPayload.ofPayload, readCell, seen, valid,
                    startWord, endWord, Nat.not_lt_of_ge sorted, Nat.not_lt_of_ge fits,
                    decoded, bind, Except.bind, pure, Except.pure]⟩
  · intro depth length cursor visible columns physical slot reached
    cases physical
    exact ⟨[], rfl⟩
  · intro depth length field fields start layout layouts middle next head tail headTotal tailTotal
      visible columns physical slot reached
    cases physical with
    | cons first rest =>
      obtain ⟨value, firstRead⟩ := headTotal first reached
      obtain ⟨values, restRead⟩ := tailTotal rest reached
      exact ⟨value :: values, by simp [List.mapM_cons, firstRead, restRead, bind, Except.bind, pure, Except.pure]⟩

theorem project_total {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    {frame : Frame limits schema input offset} {physical : Semantics.Observation}
    (wire : Semantics.ObservationWire frame physical) :
    ∃ logical, project limits.schema.depth physical = .ok logical := by
  have row : ∀ index ∈ List.range physical.rowCount,
      ∃ values, ((physical.columns.map IndexedColumn.ofColumn).mapM
        fun column => readCell limits.schema.depth column index).mapError (Formats.Arrow.RecursiveSchema.Batch.Rows.Error.row index) = .ok values := by
    intro index member
    rw [List.mapM_map]
    have bound := List.mem_range.mp member
    rw [wire.rowCount] at bound
    have reached : (Array.replicate frame.header.rowCount true)[index]? = some true := by
      simp [bound]
    obtain ⟨values, decoded⟩ := row_total frame.layout.fields.wire wire.columns reached
    exact ⟨values, by simp only [Function.comp_def, decoded, Except.mapError]⟩
  obtain ⟨rows, success⟩ := mapM_total row
  exact ⟨⟨physical.rowCount, rows⟩, by simp only [project, success, bind, Except.bind, pure, Except.pure]⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows
