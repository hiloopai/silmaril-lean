module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Thms
import Silmaril.Formats.Arrow.Body.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics

open Silmaril.Formats.Arrow (Buffer)
open Silmaril.Formats.Arrow.Body (sliceBuffer offsetAt offsetAt_iff)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (OffsetPrefix)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics

private theorem prefix_length (present : Array Bool) (offsets : Array Nat)
    (initial : offsets[0]?.getD 0 = 0)
    (ordered : ∀ i < present.size, offsets[i]?.getD 0 ≤ offsets[i + 1]?.getD 0)
    (count : Nat) (bound : count ≤ present.size) :
    ((List.range count).flatMap fun i =>
      List.replicate (offsets[i + 1]?.getD 0 - offsets[i]?.getD 0)
        (present[i]?.getD false)).length = offsets[count]?.getD 0 := by
  induction count with
  | zero => simpa using initial.symm
  | succ count ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_replicate]
    rw [ih (by omega)]
    have order := ordered count (by omega)
    omega

theorem window_visibility {present : Array Bool} {offsets : Array Nat}
    (initial : offsets[0]?.getD 0 = 0)
    (ordered : ∀ i < present.size, offsets[i]?.getD 0 ≤ offsets[i + 1]?.getD 0)
    {parent child : Nat} (bound : parent < present.size)
    (lower : offsets[parent]?.getD 0 ≤ child) (upper : child < offsets[parent + 1]?.getD 0) :
    (listVisibility present offsets)[child]? = present[parent]? := by
  let expand := fun i =>
    List.replicate (offsets[i + 1]?.getD 0 - offsets[i]?.getD 0) (present[i]?.getD false)
  have split : List.range present.size =
      List.range (parent + 1) ++ (List.range present.size).drop (parent + 1) := by
    conv => lhs; rw [← List.take_append_drop (parent + 1) (List.range present.size)]
    rw [List.take_range, Nat.min_eq_left (by omega)]
  have length : ((List.range parent).flatMap expand).length = offsets[parent]?.getD 0 :=
    prefix_length present offsets initial ordered parent (by omega)
  rw [listVisibility, List.getElem?_toArray, split, List.range_succ,
    List.flatMap_append, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (((List.range parent).flatMap expand ++ expand parent) ++
    ((List.range present.size).drop (parent + 1)).flatMap expand)[child]? = present[parent]?
  rw [List.getElem?_append_left (by simp only [List.length_append, length, expand, List.length_replicate]; omega),
    List.getElem?_append_right (by simpa only [length] using lower)]
  rw [length]
  dsimp only [expand]
  rw [List.getElem?_replicate_of_lt (by omega), Array.getElem?_eq_getElem bound]
  rfl

private theorem offset_entry {body : KBytes} {length : Nat} {buffer : Buffer} {offsets : Array Nat}
    (observed : PayloadWire body length .list (some buffer) (.list offsets))
    {i : Nat} (bound : i ≤ length) :
    ∃ value, offsets[i]? = some value ∧ offsetAt (sliceBuffer body buffer) i = some value := by
  cases observed with
  | list wire =>
    obtain ⟨size, entry⟩ := List.forall₂_iff_get.mp wire
    have source : i < (List.range (length + 1)).length := by simpa using Nat.lt_succ_of_le bound
    have target : i < offsets.toList.length := size ▸ source
    have atIndex := entry i source target
    simp only [List.get_eq_getElem, List.getElem_range] at atIndex
    exact ⟨offsets.toList[i], by rw [← Array.getElem?_toList, List.getElem?_eq_getElem target], atIndex⟩

theorem list_window {body : KBytes} {length final : Nat} {buffer : Buffer} {offsets : Array Nat}
    (observed : PayloadWire body length .list (some buffer) (.list offsets))
    (checked : OffsetPrefix (sliceBuffer body buffer) length final)
    {parent : Nat} (bound : parent < length) :
    ∃ lo hi, offsets[parent]? = some lo ∧ offsets[parent + 1]? = some hi ∧
      (sliceBuffer body buffer).readLE (4 * parent) 4 = some lo ∧
      (sliceBuffer body buffer).readLE (4 * (parent + 1)) 4 = some hi ∧ lo ≤ hi ∧ hi ≤ final := by
  obtain ⟨lo, originalLo, checkedLo⟩ := offset_entry observed (Nat.le_of_lt bound)
  obtain ⟨hi, originalHi, checkedHi⟩ := offset_entry observed (Nat.succ_le_of_lt bound)
  obtain ⟨left, right, leftWord, rightWord, ordered, bounded, _⟩ := checked.window bound
  have loWord := (offsetAt_iff _ _ _).mp checkedLo |>.1
  have hiWord := (offsetAt_iff _ _ _).mp checkedHi |>.1
  rw [loWord] at leftWord
  rw [hiWord] at rightWord
  cases Option.some.inj leftWord
  cases Option.some.inj rightWord
  exact ⟨lo, hi, originalLo, originalHi, loWord, hiWord, ordered, bounded⟩

private theorem offset_start {bytes : KBytes} {length final : Nat}
    (checked : OffsetPrefix bytes length final) : offsetAt bytes 0 = some 0 := by
  induction checked with
  | zero word => exact word
  | step _ _ _ ih => exact ih

theorem list_endpoints {body : KBytes} {length final : Nat} {buffer : Buffer} {offsets : Array Nat}
    (observed : PayloadWire body length .list (some buffer) (.list offsets))
    (checked : OffsetPrefix (sliceBuffer body buffer) length final) :
    offsets[0]? = some 0 ∧ offsets[length]? = some final := by
  obtain ⟨_, first, readFirst⟩ := offset_entry observed (Nat.zero_le length)
  obtain ⟨_, last, readLast⟩ := offset_entry observed (Nat.le_refl length)
  rw [offset_start checked] at readFirst
  rw [(offsetAt_iff _ _ _).mpr checked.last_word] at readLast
  exact ⟨first.trans readFirst.symm, last.trans readLast.symm⟩

theorem list_visibility_size {body : KBytes} {length final : Nat} {buffer : Buffer}
    {offsets : Array Nat} {present : Array Bool} (size : present.size = length)
    (observed : PayloadWire body length .list (some buffer) (.list offsets))
    (checked : OffsetPrefix (sliceBuffer body buffer) length final) :
    (listVisibility present offsets).size = final := by
  obtain ⟨first, last⟩ := list_endpoints observed checked
  have ordered : ∀ i < present.size, offsets[i]?.getD 0 ≤ offsets[i + 1]?.getD 0 := by
    intro i bound
    obtain ⟨lo, hi, loWord, hiWord, _, _, order, _⟩ :=
      list_window observed checked (size ▸ bound)
    simpa [loWord, hiWord] using order
  have exactLength := prefix_length present offsets (by simp [first]) ordered present.size (Nat.le_refl _)
  rw [size, last] at exactLength
  simpa [listVisibility, size] using exactLength

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Semantics
