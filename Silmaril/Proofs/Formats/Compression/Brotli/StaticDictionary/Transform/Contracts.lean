module

public import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Defs
import Silmaril.Formats.Compression.Brotli.StaticDictionary.Thms
import Init.Data.ByteArray.Lemmas
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.StaticDictionary.Transform

open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.StaticDictionary
open Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform

theorem fermentStep_sound (word : List UInt8) :
    StepWire word (fermentStep word).1 (fermentStep word).2 := by
  cases word with
  | nil => exact .empty
  | cons head tail =>
    simp only [fermentStep]
    split
    · exact .single ‹head < 0xc0›
    · rename_i notSingle
      split
      · rename_i two
        cases tail with
        | nil => exact .twoShort (UInt8.not_lt.mp notSingle) two
        | cons second rest => exact .two (UInt8.not_lt.mp notSingle) two
      · rename_i notTwo
        cases tail with
        | nil => exact .threeShortOne (UInt8.not_lt.mp notTwo)
        | cons second rest =>
          cases rest with
          | nil => exact .threeShortTwo (UInt8.not_lt.mp notTwo)
          | cons third tail => exact .three (UInt8.not_lt.mp notTwo)

theorem StepWire.extent {word leading trailing : List UInt8}
    (step : StepWire word leading trailing) :
    leading.length + trailing.length = word.length ∧ (word ≠ [] → trailing.length < word.length) := by
  cases step <;> simp <;> omega

private theorem fermentAllWithFuel_sound {fuel : Nat} {word : List UInt8} (enough : word.length ≤ fuel) :
    FermentAllWire word (Internal.fermentAllWithFuel fuel word) := by
  induction fuel generalizing word with
  | zero =>
    have empty : word = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    subst word
    exact .empty
  | succ fuel ih =>
    cases word with
    | nil => exact .empty
    | cons head tail =>
      have step := fermentStep_sound (head :: tail)
      have shorter := (StepWire.extent step).2 (List.cons_ne_nil _ _)
      have enough' : (fermentStep (head :: tail)).2.length ≤ fuel := by omega
      exact .next (List.cons_ne_nil _ _) step (ih enough')

theorem fermentAll_sound (word : List UInt8) : FermentAllWire word (fermentAll word) :=
  fermentAllWithFuel_sound (Nat.le_refl _)

private theorem FermentAllWire.length {word result : List UInt8} (wire : FermentAllWire word result) :
    result.length = word.length := by
  induction wire with
  | empty => rfl
  | next _ step _ ih => rw [List.length_append, ih, (StepWire.extent step).1]

theorem middle_sound (action : Action) (word : List UInt8) : MiddleWire action word (middle action word) := by
  cases action with
  | identity => exact .identity word
  | fermentFirst => exact .fermentFirst (fermentStep_sound word)
  | fermentAll => exact .fermentAll (fermentAll_sound word)
  | omitFirst count => exact .omitFirst word count
  | omitLast count => exact .omitLast word count

theorem MiddleWire.size {action : Action} {word result : List UInt8} (wire : MiddleWire action word result) :
    result.length = middleSize action word.length := by
  cases wire with
  | identity => rfl
  | fermentFirst step => rw [List.length_append, (StepWire.extent step).1]; rfl
  | fermentAll whole => exact FermentAllWire.length whole
  | omitFirst => exact List.length_drop
  | omitLast =>
    rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
    rfl

private theorem table_affixes_fit :
    table.toList.all (fun row => row.leading.length + row.trailing.length ≤ 13) = true := by decide +kernel

theorem entry_affix_bound {ordinal : Nat} {row : Entry} (chosen : table[ordinal]? = some row) :
    row.leading.length + row.trailing.length ≤ 13 := by
  have mem : row ∈ table.toList := Vector.mem_toList_iff.mpr (Vector.mem_of_getElem? chosen)
  exact of_decide_eq_true ((List.all_eq_true.mp table_affixes_fit) row mem)

theorem table_total {ordinal : Nat} : (∃ row, table[ordinal]? = some row) ↔ ordinal < transformCount := by
  constructor
  · rintro ⟨row, chosen⟩
    exact (Vector.getElem?_eq_some_iff.mp chosen).1
  · intro fits
    exact ⟨table[ordinal]'fits, getElem?_pos table ordinal fits⟩

theorem applyTransform_iff {ordinal : Nat} {word result : ByteArray} :
    applyTransform ordinal word = .ok result ↔
      WordLength word.size ∧ ∃ row, table[ordinal]? = some row ∧
        result = ⟨(row.leading ++ middle row.action word.data.toList ++ row.trailing).toArray⟩ := by
  unfold applyTransform
  by_cases valid : WordLength word.size
  · cases chosen : table[ordinal]? <;> simp [valid, eq_comm]
  · simp [valid]

theorem baseLength_iff {ordinal : Nat} {word : ByteArray} :
    applyTransform ordinal word = .error .baseLength ↔ ¬WordLength word.size := by
  unfold applyTransform
  by_cases valid : WordLength word.size
  · cases table[ordinal]? <;> simp [valid]
  · simp [valid]

theorem transformOrdinal_iff {ordinal : Nat} {word : ByteArray} :
    applyTransform ordinal word = .error .transformOrdinal ↔ WordLength word.size ∧ transformCount ≤ ordinal := by
  unfold applyTransform
  by_cases valid : WordLength word.size
  · have absent : table[ordinal]? = none ↔ transformCount ≤ ordinal := by
      by_cases fits : ordinal < transformCount
      · simp [getElem?_pos table ordinal fits, Nat.not_le_of_lt fits]
      · simp [Nat.le_of_not_gt fits]
    cases chosen : table[ordinal]? <;> simp_all
  · simp [valid]

theorem applyTransform_sound {ordinal : Nat} {word result : ByteArray}
    (parsed : applyTransform ordinal word = .ok result) : Wire ordinal word result := by
  obtain ⟨_, row, source, rfl⟩ := applyTransform_iff.mp parsed
  exact ⟨row, _, source, middle_sound row.action word.data.toList, by simp⟩

theorem Wire.size {ordinal : Nat} {word result : ByteArray} {row : Entry}
    (wire : Wire ordinal word result) (chosen : table[ordinal]? = some row) :
    result.size = outputSize row word.size ∧ result.size ≤ word.size + 13 := by
  obtain ⟨actual, middleBytes, source, meaning, out⟩ := wire
  have same : actual = row := Option.some.inj (source.symm.trans chosen)
  subst actual
  have extent := congrArg List.length out
  simp only [Array.length_toList, List.length_append, MiddleWire.size meaning] at extent
  change result.size = outputSize row word.size at extent
  have reduced : middleSize row.action word.size ≤ word.size := by
    cases row.action <;> simp [middleSize]
  have affix := entry_affix_bound source
  exact ⟨extent, by simp only [outputSize] at extent; omega⟩

theorem materialize_resolved {bounds : Distance.Bounds} {ring after : Distance.Ring}
    {length code distance wordId : Nat}
    (resolved : Distance.Resolved bounds ring length code distance (.staticDictionary distance length wordId) after) :
    ∃ address word row result,
      splitAddress length wordId = .ok address ∧ lookup length address.index = .ok word ∧
      table[address.transform]? = some row ∧ materialize length wordId = .ok result ∧
      Wire address.transform word result ∧ result.size = outputSize row length ∧ result.size ≤ 37 := by
  obtain ⟨address, word, split, base⟩ := StaticDictionary.resolved_lookup resolved
  obtain ⟨valid, _, _, _, _, ordinalFits, _⟩ := StaticDictionary.splitAddress_sound split
  have size := StaticDictionary.lookup_size base
  have wordLength : WordLength word.size := size.symm ▸ valid
  obtain ⟨row, chosen⟩ := table_total.mpr ordinalFits
  let result : ByteArray := ⟨(row.leading ++ middle row.action word.data.toList ++ row.trailing).toArray⟩
  have rendered : applyTransform address.transform word = .ok result :=
    applyTransform_iff.mpr ⟨wordLength, row, chosen, rfl⟩
  have wire := applyTransform_sound rendered
  obtain ⟨extent, fits⟩ := Wire.size wire chosen
  refine ⟨address, word, row, result, split, base, chosen, ?_, wire, size ▸ extent, ?_⟩
  · simpa [materialize, split, base, Except.mapError, bind, Except.bind] using rendered
  · have short := valid.2
    omega

end Silmaril.Proofs.Formats.Compression.Brotli.StaticDictionary.Transform
