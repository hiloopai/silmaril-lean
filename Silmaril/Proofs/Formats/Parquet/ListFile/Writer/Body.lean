module

public import Silmaril.Formats.Parquet.ListFile.Writer.Defs
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Prelude.Bytes.Digits.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Writer

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Writer.PageEncoding
open ListPage (Row Event rowEvents)

private theorem row_length (row : Row) : (rowEvents row).length = max 1 (row.getD []).length := by
  cases row with
  | none => rfl
  | some children =>
    cases children with
    | nil => rfl
    | cons item rest => simp [rowEvents]

public theorem entries_length (rows : List Row) : (entries rows).length = slotCount rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [entries, slotCount, List.flatMap_cons, List.map_append, List.length_append,
      List.length_map, List.map_cons, List.sum_cons, row_length] at ih ⊢
    rw [ih]

private theorem row_values (row : Row) :
    ((rowEvents row).map Event.wire).filterMap (·.2.2) = (row.getD []).filterMap id := by
  cases row with
  | none => rfl
  | some children =>
    cases children with
    | nil => rfl
    | cons item rest =>
      cases item <;> simp [rowEvents, Event.wire, List.filterMap_map, List.map_map, Function.comp_def, id] <;> rfl

/-- The scalar suffix uses the original present children, in row and child order. -/
public theorem entries_values (rows : List Row) :
    (entries rows).filterMap (·.2.2) = rows.flatMap (fun row => (row.getD []).filterMap id) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [entries, List.flatMap_cons, List.map_append, List.filterMap_append] at ih ⊢
    rw [row_values, ih]

private theorem scalar_count (rows : List Row) :
    ((entries rows).filterMap (·.2.2)).length = valueCount rows := by
  rw [entries_values]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [valueCount, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, List.length_filterMap_eq_countP]
    rfl

private theorem runs_length (width : Nat) (byte : Hybrid.repeatedByteCount width = 1)
    (values : List Nat) : (runs width values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [runs, Hybrid.Run.wire, Hybrid.uleb, byte, KBytes.length_unpack] at ih ⊢
    omega

private theorem encode_length (values : List Int32) :
    (Plain.encodeInt32 values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [Plain.encodeInt32, Plain.encodeWords, Plain.writeUInt32Word, KBytes.length_unpack] at ih ⊢
    omega

public theorem body_length (rows : List Row) : (body rows).length = bodySize rows := by
  have one : Hybrid.repeatedByteCount 1 = 1 := rfl
  have two : Hybrid.repeatedByteCount 2 = 1 := rfl
  simp only [body, Bytes.length_append, lengthPrefixed, Bytes.length_ofList, List.length_append,
    KBytes.length_unpack, runs_length 1 one, runs_length 2 two, List.length_map, entries_length,
    encode_length, scalar_count, bodySize]
  omega

private theorem runs_wire {width : Nat} {values : List Nat} (bounded : ∀ v ∈ values, v < 2 ^ width) :
    Hybrid.Wire width values.length (runs width values) values := by
  induction values with
  | nil => exact .empty
  | cons value rest ih =>
    let run := Hybrid.Run.repeated 1 value
    have valid : run.Valid width := ⟨by change 0 < 1; decide, by change 1 < 2^31; decide, bounded value (by simp)⟩
    have fits : run.Fits (value :: rest).length := by simp [run, Hybrid.Run.Fits]
    have tail := ih (fun v mem => bounded v (by simp [mem]))
    have next := Hybrid.Wire.next (run := run) (remaining := (value :: rest).length)
      (by simp) valid fits (show Hybrid.Wire width ((value :: rest).length - run.size) _ _ from tail)
    simpa [run, Hybrid.Run.values, runs, List.take] using next

private theorem event_levels (event : Event) :
    event.wire.1 < 2 ^ 1 ∧ event.wire.2.1 < 2 ^ 2 ∧
      event.wire.2.2.isSome = (event.wire.2.1 == 3) := by
  cases event with
  | nullList | emptyList => decide
  | first item | next item => cases item <;> simp [Event.wire]

private theorem zip_projections (slots : List (Nat × Nat × Option Int32)) :
    (slots.map Prod.fst).zip ((slots.map (·.2.1)).zip (slots.map (·.2.2))) = slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    obtain ⟨r, d, v⟩ := slot
    simp [ih]

/-- A direct wire witness for the canonical singleton runs and signed PLAIN suffix. -/
public theorem body_wire {rows : List Row} {limits : ListFile.Multi.Limits}
    (fits : Fits limits rows) : ListPage.SlotsWire (slotCount rows) (body rows) (entries rows) := by
  let slots := entries rows
  let reps := slots.map Prod.fst
  let defs := slots.map (·.2.1)
  let values := slots.map (·.2.2)
  let repBytes := Bytes.ofList (runs 1 reps)
  let defBytes := Bytes.ofList (runs 2 defs)
  let scalars := values.filterMap id
  let valuesBytes := Plain.encodeInt32 scalars
  have repBound : ∀ value ∈ reps, value < 2 ^ 1 := by
    intro value member
    simp only [reps, slots, entries, List.map_map] at member
    obtain ⟨event, _, rfl⟩ := List.mem_map.mp member
    exact (event_levels event).1
  have defBound : ∀ value ∈ defs, value < 2 ^ 2 := by
    intro value member
    simp only [defs, slots, entries, List.map_map] at member
    obtain ⟨event, _, rfl⟩ := List.mem_map.mp member
    exact (event_levels event).2.1
  have count : slots.length = slotCount rows := entries_length rows
  have mask : values.map Option.isSome = ListPage.valueMask defs := by
    simp only [values, defs, slots, entries, ListPage.valueMask, List.map_map]
    exact List.map_congr_left (fun event _ => (event_levels event).2.2)
  have plain : Plain.decodeInt32 ((ListPage.valueMask defs).count true) valuesBytes = .ok scalars := by
    rw [← mask]
    simpa [scalars, List.count_eq_countP, List.countP_map, Function.comp_def, List.length_filterMap_eq_countP]
      using Plain.decodeInt32_encodeInt32 scalars
  have length_word {octets : List UInt8} (bound : octets.length = 2 * slotCount rows) :
      KBytes.leVal (KBytes.unpack 4 octets.length) = (Bytes.ofList octets).length := by
    rw [Bytes.length_ofList, KBytes.leVal_unpack, Nat.mod_eq_of_lt]
    rw [bound]
    have cap := fits.2.2.2.2.2.1
    unfold bodySize at cap
    omega
  refine ⟨KBytes.unpack 4 (runs 1 reps).length, KBytes.unpack 4 (runs 2 defs).length,
    repBytes, defBytes, valuesBytes, reps, defs, scalars, values,
    KBytes.length_unpack _ _, KBytes.length_unpack _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    plain, mask, rfl, (zip_projections slots).symm⟩
  · apply length_word
    simp [runs_length 1 (by rfl), reps, count]
  · apply length_word
    simp [runs_length 2 (by rfl), defs, count]
  · simp [body, reps, defs, valuesBytes, scalars, values, slots, List.filterMap_map,
      repBytes, defBytes, lengthPrefixed, List.append_assoc]
  · simpa [repBytes, reps, count] using runs_wire repBound
  · simpa [defBytes, defs, count] using runs_wire defBound
  · simp [reps, count]
  · simp [defs, count]
  · simp [values, count]

public theorem measure_fits {limits : ListFile.Multi.Limits} {rows : List Row} {headerBytes : Bytes}
    (h : ListFile.Writer.PageEncoding.measure limits rows = .ok headerBytes) :
    Fits limits rows ∧ headerBytes.length ≤ limits.file.framing.maxHeaderBytes ∧
      PlainV1Writer.encodeHeader (slotCount rows) (bodySize rows) = some headerBytes := by
  unfold ListFile.Writer.PageEncoding.measure at h
  split at h
  · contradiction
  · rename_i fits
    cases built : PlainV1Writer.encodeHeader (slotCount rows) (bodySize rows) with
    | none => simp [built] at h
    | some bytes =>
      simp only [built] at h
      split at h
      · contradiction
      · rename_i bound
        obtain rfl := Except.ok.inj h
        exact ⟨not_not.mp fits, Nat.le_of_not_gt bound, rfl⟩

public theorem encode_wire {limits : ListFile.Multi.Limits} {rows : List Row} {headerBytes : Bytes}
    {page : PlainV1Writer.Encoded} (h : encode limits rows headerBytes = .ok page) :
    page.header = header rows ∧ page.headerBytes = headerBytes ∧ page.body = body rows ∧
      ListPage.decodeV1 limits.file.page 0 page.header rows.length page.body = .ok rows ∧
      ListPage.PageWire limits.file.page 0 page.header rows.length page.body rows := by
  unfold encode at h
  cases decoded : ListPage.decodeV1 limits.file.page 0 (header rows) rows.length (body rows) with
  | error e => simp [decoded, Except.mapError, Bind.bind, Except.bind] at h
  | ok output =>
    simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · rename_i same
      obtain rfl := Except.ok.inj h
      subst output
      exact ⟨rfl, rfl, rfl, decoded, ListPage.decodeV1_wire decoded⟩
    · contradiction

end Silmaril.Proofs.Formats.Parquet.ListFile.Writer
