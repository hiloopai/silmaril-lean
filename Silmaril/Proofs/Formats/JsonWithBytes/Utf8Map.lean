module

public import Silmaril.Formats.JsonWithBytes.Utf8Map.Defs

public section
namespace Silmaril.Proofs.Formats.JsonWithBytes.Utf8Map

open Silmaril.Data Silmaril.Formats Silmaril.Formats.JsonWithBytes
open Silmaril.Formats.JsonWithBytes.Utf8Map

private theorem key_injective : Function.Injective keyBytes := by
  intro key other eq
  apply String.toByteArray_inj.mp
  change key.toUTF8 = other.toUTF8
  exact ByteArray.ext (Array.toList_inj.mp eq)

theorem find_insert {Value : Type} (acc : Map Value) (key query : String) (value : Value) :
    (acc.insert key value).find? query = if query = key then some value else acc.find? query := by
  simp [Map.find?, Map.insert, BytesMap.find?_insert, key_injective.eq_iff]

private theorem lookup_none {Value : Type} {entries : List (String × Value)} {key : String}
    (absent : key ∉ entries.map Prod.fst) : entries.lookup key = none := by
  apply List.lookup_eq_none_iff.mpr
  intro entry belongs
  have different : key ≠ entry.1 := fun equal => absent (List.mem_map.mpr ⟨_, belongs, equal.symm⟩)
  simp [different]

theorem build_sound {Value : Type} {entries : List (String × Value)} {acc result : Map Value}
    (built : acc.build entries = .ok result) :
    (entries.map Prod.fst).Nodup ∧
      ∀ key, (key ∈ entries.map Prod.fst → acc.find? key = none) ∧
        result.find? key = (entries.lookup key).or (acc.find? key) := by
  induction entries generalizing acc with
  | nil => cases built; simp
  | cons entry tail ih =>
    obtain ⟨key, value⟩ := entry
    by_cases present : (acc.find? key).isSome = true
    · simp [Map.build, present] at built
    · have absent : acc.find? key = none := by simpa using present
      have builtTail : (acc.insert key value).build tail = .ok result := by
        simpa [Map.build, present] using built
      obtain ⟨nodup, read⟩ := ih builtTail
      have fresh : key ∉ tail.map Prod.fst := by
        intro member
        have noneAt := (read key).1 member
        simp [find_insert] at noneAt
      refine ⟨List.nodup_cons.mpr ⟨fresh, nodup⟩, fun query => ⟨?_, ?_⟩⟩
      · simp only [List.map_cons, List.mem_cons]
        rintro (rfl | member)
        · exact absent
        · have notKey : query ≠ key := fun same => fresh (same ▸ member)
          simpa [find_insert, notKey] using (read query).1 member
      · rw [(read query).2, find_insert]
        by_cases same : query = key
        · subst query
          have noneInTail : tail.lookup key = none := lookup_none fresh
          simp [noneInTail]
        · simp [List.lookup_cons, show (query == key) = false by simpa using same, same]

theorem ofEntries_sound {Value : Type} {entries : List (String × Value)} {result : Map Value}
    (built : Map.ofEntries entries = .ok result) :
    (entries.map Prod.fst).Nodup ∧ ∀ key, result.find? key = entries.lookup key := by
  obtain ⟨unique, read⟩ := build_sound built
  exact ⟨unique, fun key => by simpa [Map.find?, Map.empty, BytesMap.find?_empty] using (read key).2⟩

private theorem build_exists {Value : Type} {entries : List (String × Value)} {acc : Map Value}
    (unique : (entries.map Prod.fst).Nodup)
    (fresh : ∀ key ∈ entries.map Prod.fst, acc.find? key = none) : ∃ map, acc.build entries = .ok map := by
  induction entries generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons entry tail ih =>
    obtain ⟨key, value⟩ := entry
    obtain ⟨notInTail, tailUnique⟩ := List.nodup_cons.mp unique
    have keyFresh := fresh key (by simp)
    obtain ⟨map, built⟩ := ih (acc := acc.insert key value) tailUnique (fun query member => by
      have different : query ≠ key := fun same => notInTail (same ▸ member)
      rw [find_insert, ite_eq_right different, fresh query (by simp [member])])
    exact ⟨map, by simpa [Map.build, keyFresh] using built⟩

theorem ofEntries_accepts {Value : Type} (entries : List (String × Value)) :
    (∃ map, Map.ofEntries entries = .ok map) ↔ (entries.map Prod.fst).Nodup :=
  ⟨fun ⟨_, built⟩ => (ofEntries_sound built).1,
    fun unique => build_exists (acc := Map.empty) unique (fun key _ => BytesMap.find?_empty (keyBytes key))⟩

theorem map_ext {Value : Type} {first second : Map Value} (agrees : ∀ key, first.find? key = second.find? key) :
    first = second := by
  classical
  obtain ⟨keysFirst, suppFirst⟩ := first.property
  obtain ⟨keysSecond, suppSecond⟩ := second.property
  apply Subtype.ext
  apply BytesMap.ext
  intro bytes
  by_cases utf8 : ∃ key, keyBytes key = bytes
  · obtain ⟨key, rfl⟩ := utf8
    exact agrees key
  · rw [suppFirst _ (fun member => utf8 (List.mem_map.mp member |>.imp fun _ h => h.2)),
      suppSecond _ (fun member => utf8 (List.mem_map.mp member |>.imp fun _ h => h.2))]

theorem object_ext {Number : Type} {first second : Object Number}
    (agrees : ∀ key, first.val.get? [.key key] = second.val.get? [.key key]) : first = second := by
  obtain ⟨keysFirst, valuesFirst, shapeFirst⟩ := first.property
  obtain ⟨keysSecond, valuesSecond, shapeSecond⟩ := second.property
  apply Subtype.ext
  rw [shapeFirst, shapeSecond]
  have sameKeys : keysFirst = keysSecond := by
    ext key
    specialize agrees key
    rw [shapeFirst, shapeSecond] at agrees
    by_cases inFirst : key ∈ keysFirst <;> by_cases inSecond : key ∈ keysSecond <;>
      simp_all [Json.get?]
  refine Json.map_congr sameKeys fun key inFirst inSecond => ?_
  have same := agrees key
  rw [shapeFirst, shapeSecond] at same
  simpa [Json.get?, inFirst, inSecond] using same

theorem exists_object {Number : Type} (map : Map (Unordered Number)) : ∃ object, Agrees map object := by
  classical
  obtain ⟨keyList, support⟩ := map.property
  let keys := keyList.toFinset.filter (fun key => (map.find? key).isSome = true)
  have mem (key : String) : key ∈ keys ↔ (map.find? key).isSome = true := by
    refine ⟨fun isIn => (Finset.mem_filter.mp isIn).2, fun someValue => ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr ?_, someValue⟩
    by_contra absent
    have notEncoded : keyBytes key ∉ keyList.map keyBytes := by
      intro found
      obtain ⟨other, belongs, equal⟩ := List.mem_map.mp found
      exact absent (key_injective equal ▸ belongs)
    have noneAt : map.find? key = none := support _ notEncoded
    simp [noneAt] at someValue
  let values (key : {key // key ∈ keys}) : Unordered Number :=
    (map.find? key.val).get ((mem key.val).mp key.property)
  refine ⟨⟨.map keys values, ⟨keys, values, rfl⟩⟩, fun key => ?_⟩
  by_cases isIn : key ∈ keys
  · simp [Json.get?, isIn, values]
  · have noneAt : map.find? key = none := by simpa using (not_congr (mem key)).mp isIn
    simp [Json.get?, isIn, noneAt]

theorem exists_map {Number : Type} (object : Object Number) : ∃ map, Agrees map object := by
  classical
  obtain ⟨keys, vals, shape⟩ := object.property
  let lookup (bytes : List UInt8) : Option (Unordered Number) :=
    if utf8 : ∃ key, keyBytes key = bytes then object.val.get? [.key utf8.choose] else none
  have supported (bytes : List UInt8) (absent : bytes ∉ keys.toList.map keyBytes) : lookup bytes = none := by
    dsimp only [lookup]
    split
    · rename_i utf8
      have notMember : utf8.choose ∉ keys := by
        intro member
        exact absent (List.mem_map.mpr ⟨_, Finset.mem_toList.mpr member, utf8.choose_spec⟩)
      simp [shape, Json.get?, notMember]
    · rfl
  obtain ⟨map, read⟩ := BytesMap.exists_of_finite lookup (keys.toList.map keyBytes) supported
  refine ⟨⟨map, ⟨keys.toList, fun bytes absent => (read bytes).trans (supported bytes absent)⟩⟩, fun key => ?_⟩
  change map.find? (keyBytes key) = _
  rw [read]
  dsimp only [lookup]
  split
  · rename_i utf8
    rw [key_injective utf8.choose_spec]
  · rename_i notUtf8
    exact False.elim (notUtf8 ⟨key, rfl⟩)

noncomputable def equiv {Number : Type} : Map (Unordered Number) ≃ Object Number where
  toFun map := (exists_object map).choose
  invFun object := (exists_map object).choose
  left_inv map := map_ext fun key =>
    ((exists_map (exists_object map).choose).choose_spec key).trans ((exists_object map).choose_spec key).symm
  right_inv object := object_ext fun key =>
    ((exists_object (exists_map object).choose).choose_spec key).symm.trans ((exists_map object).choose_spec key)

theorem agrees_equiv {Number : Type} (map : Map (Unordered Number)) : Agrees map (equiv map) :=
  (exists_object map).choose_spec

private theorem lookup_pair {Value : Type} (entries : List (String × Value)) (key : String) :
    entries.lookup key = (entries.find? (fun entry => decide (entry.1 = key))).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, value⟩ := entry
    by_cases same : key = name
    · subst key; simp
    · simp [List.lookup_cons, show (key == name) = false by simpa using same, Ne.symm same, ih]

private theorem map_get {Input Value : Type} (output : Option Input) (found : output.isSome)
    (project : Input → Value) : output.map project = some (project (output.get found)) := by
  cases output with
  | none => cases found
  | some => rfl

theorem agrees_ofEntries {Number : Type} {entries : List (String × Unordered Number)}
    {map : Map (Unordered Number)} (built : Map.ofEntries entries = .ok map)
    (unique : (entries.map Prod.fst).Nodup) :
    Agrees map ⟨Json.ofEntries entries unique, ⟨_, _, rfl⟩⟩ := by
  intro key
  rw [(ofEntries_sound built).2]
  change entries.lookup key = (Json.ofEntries entries unique).get? [.key key]
  unfold Json.ofEntries
  rw [Json.get?]
  split
  · rw [lookup_pair, Json.get?]
    exact map_get _ _ Prod.snd
  · rename_i absent
    exact lookup_none (fun member => absent (Multiset.mem_coe.mpr member))

theorem equiv_ofEntries {Number : Type} {entries : List (String × Unordered Number)}
    {map : Map (Unordered Number)} (built : Map.ofEntries entries = .ok map) :
    (equiv map).val = Json.ofEntries entries (ofEntries_sound built).1 := by
  let unique := (ofEntries_sound built).1
  have same := object_ext fun key => ((agrees_equiv map) key).symm.trans ((agrees_ofEntries built unique) key)
  exact congrArg Subtype.val same

end Silmaril.Proofs.Formats.JsonWithBytes.Utf8Map
