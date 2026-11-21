module

public import Silmaril.Semantics.Naming.ByteRange.Extension.Defs
public import Silmaril.Semantics.Naming.ByteRange.Thms

public section

namespace Silmaril.Proofs.Semantics.Naming.ByteRange.Extension

open Silmaril.Semantics.Naming
open Silmaril.Semantics.Naming.ByteRange

theorem range_iff {whole fragment : Bytes} {offset : Nat} :
    (Fact.range offset fragment).Holds whole ↔ Slice whole offset fragment := by
  rw [slice_iff]
  constructor
  · rintro ⟨bound, _, read⟩
    refine ⟨bound, List.ext_getElem? fun index => ?_⟩
    by_cases inside : index < fragment.length
    · rw [List.getElem?_take_of_lt inside, List.getElem?_drop]
      exact (read (offset + index) _ ⟨index, rfl, List.getElem?_eq_getElem inside⟩).trans
        (List.getElem?_eq_getElem inside).symm
    · rw [List.getElem?_eq_none (by simp [List.length_take]; omega), List.getElem?_eq_none (by omega)]
  · rintro ⟨bound, slice⟩
    refine ⟨bound, by simp [Fact.end?], ?_⟩
    rintro _ byte ⟨index, rfl, hit⟩
    have inside : index < fragment.length := (List.getElem?_eq_some_iff.mp hit).choose
    rwa [← List.getElem?_drop, ← List.getElem?_take_of_lt inside, slice]

theorem whole_iff {expected bytes : Bytes} : (Fact.whole expected).Holds bytes ↔ bytes = expected := by
  constructor
  · rintro ⟨_, ends, read⟩
    have length := ends expected.length rfl
    apply List.ext_getElem?
    intro pos
    by_cases inside : pos < expected.length
    · exact (read pos _ (List.getElem?_eq_getElem inside)).trans (List.getElem?_eq_getElem inside).symm
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · rintro rfl
    exact ⟨Nat.le_refl _, fun _ eq => Option.some.inj eq, fun _ _ read => read⟩

theorem eof_iff {length : Nat} {bytes : Bytes} : (Fact.eof length).Holds bytes ↔ bytes.length = length := by
  constructor
  · exact fun holds => holds.2.1 length rfl
  · intro eq
    exact ⟨Nat.le_of_eq eq.symm, fun _ hit => eq.trans (Option.some.inj hit), fun _ _ read => read.elim⟩

private theorem read_lt_bound {fact : Fact} {pos : Nat} {byte : UInt8} (hit : fact.reads pos byte) :
    pos < fact.bound := by
  cases fact with
  | range offset fragment =>
    obtain ⟨index, rfl, h⟩ := hit
    exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.mp h).choose offset
  | whole bytes => exact (List.getElem?_eq_some_iff.mp hit).choose
  | eof length => exact False.elim hit

private theorem end_eq_bound {fact : Fact} {length : Nat} (ending : fact.end? = some length) :
    fact.bound = length := by
  cases fact <;> simp_all [Fact.end?, Fact.bound]

variable {Name : Type} {seen : Observations Name} {base rel : Relation Name Bytes} {name : Name}

theorem fits_filling (length : Nat) (gap : Nat → UInt8) (agrees : seen.Agrees name)
    (bound : ∀ fact, seen name fact → fact.bound ≤ length)
    (ending : ∀ fact actual, seen name fact → fact.end? = some actual → length = actual) :
    ∃ bytes, bytes.length = length ∧ seen.Fits name bytes ∧
      ∀ pos, pos < length → (¬ ∃ byte, seen.ByteAt name pos byte) → bytes[pos]? = some (gap pos) := by
  classical
  let value (pos : Nat) : UInt8 :=
    if covered : ∃ byte, seen.ByteAt name pos byte then covered.choose else gap pos
  refine ⟨List.ofFn fun pos : Fin length => value pos, by simp, ?_, ?_⟩
  · intro fact hit
    refine ⟨by simpa using bound fact hit, fun actual hend => by simpa using ending fact actual hit hend, ?_⟩
    intro pos byte read
    have inside := Nat.lt_of_lt_of_le (read_lt_bound read) (bound fact hit)
    rw [List.getElem?_eq_getElem (by simpa using inside), List.getElem_ofFn]
    have covered : ∃ byte, seen.ByteAt name pos byte := ⟨byte, fact, hit, read⟩
    simp only [value, dite_eq_left covered, Option.some.injEq]
    exact agrees pos _ _ covered.choose_spec ⟨fact, hit, read⟩
  · intro pos inside absent
    rw [List.getElem?_eq_getElem (by simpa using inside), List.getElem_ofFn]
    simp only [value, dite_eq_right absent]

theorem exists_fits_iff : (∃ bytes, seen.Fits name bytes) ↔ seen.Compatible name := by
  constructor
  · rintro ⟨bytes, fits⟩
    refine ⟨?_, ⟨bytes.length, fun fact hit => (fits fact hit).1⟩, ?_⟩
    · rintro pos left right ⟨lhs, lh, lread⟩ ⟨rhs, rh, rread⟩
      exact Option.some.inj (((fits lhs lh).2.2 pos left lread).symm.trans ((fits rhs rh).2.2 pos right rread))
    · intro ending fact length he hf hend
      exact (fits ending he).2.1 length hend ▸ (fits fact hf).1
  · classical
    rintro ⟨agrees, bounded, ends⟩
    have possible : ∃ length, (∀ fact, seen name fact → fact.bound ≤ length) ∧
        ∀ ending actual, seen name ending → ending.end? = some actual → length = actual := by
      by_cases ended : ∃ ending actual, seen name ending ∧ ending.end? = some actual
      · obtain ⟨ending, length, seenEnd, hend⟩ := ended
        refine ⟨length, fun fact hit => ends ending fact length seenEnd hit hend, ?_⟩
        intro other actual seenOther hother
        have forward := ends other ending actual seenOther seenEnd hother
        have backward := ends ending other length seenEnd seenOther hend
        rw [end_eq_bound hend] at forward
        rw [end_eq_bound hother] at backward
        exact Nat.le_antisymm forward backward
      · obtain ⟨length, bound⟩ := bounded
        exact ⟨length, bound, fun ending actual hit h => (ended ⟨ending, actual, hit, h⟩).elim⟩
    obtain ⟨length, bound, ending⟩ := possible
    obtain ⟨bytes, _, fits, _⟩ := fits_filling length (fun _ => 0) agrees bound ending
    exact ⟨bytes, fits⟩

theorem model_of_pick (binding : Binding base)
    (old : ∀ ⦃name bytes⦄, base name bytes → seen.Fits name bytes)
    (pick : Name → Bytes)
    (new : ∀ name, seen.Queried name → (¬ ∃ bytes, base name bytes) → seen.Fits name (pick name)) :
    seen.Model base (fillMissing base fun name bytes => seen.Queried name ∧ bytes = pick name) := by
  refine ⟨?_, fun {_ _} hit => Or.inl hit, ?_, ?_⟩
  · rintro name lhs rhs (left | ⟨noLeft, _, rfl⟩) (right | ⟨noRight, _, rfl⟩)
    · exact binding left right
    · exact (noRight ⟨_, left⟩).elim
    · exact (noLeft ⟨_, right⟩).elim
    · rfl
  · rintro _ _ (hit | ⟨_, asked, _⟩)
    · exact Or.inl hit
    · exact Or.inr asked
  · intro name asked
    classical
    by_cases existsOld : ∃ bytes, base name bytes
    · obtain ⟨bytes, hit⟩ := existsOld
      exact ⟨bytes, Or.inl hit, old hit⟩
    · exact ⟨pick name, Or.inr ⟨existsOld, asked, rfl⟩, new name asked existsOld⟩

theorem model_preserves_fiber {bytes : Bytes} (model : seen.Model base rel) (old : base name bytes) :
    ∀ payload, rel name payload ↔ base name payload := by
  intro payload
  exact ⟨fun hit => model.1 (model.2.1 old) hit ▸ old, fun hit => model.2.1 hit⟩

theorem exists_model_iff : (∃ rel, seen.Model base rel) ↔ Binding base ∧
    (∀ ⦃name bytes⦄, base name bytes → seen.Fits name bytes) ∧
    (∀ name, seen.Queried name → seen.Compatible name) := by
  constructor
  · rintro ⟨rel, model⟩
    refine ⟨fun {_ _ _} left right => model.1 (model.2.1 left) (model.2.1 right), ?_, ?_⟩
    · intro name bytes hit fact observed
      obtain ⟨witness, known, fits⟩ := model.2.2.2 name ⟨fact, observed⟩
      exact model.1 known (model.2.1 hit) ▸ fits fact observed
    · intro name query
      obtain ⟨bytes, _, fits⟩ := model.2.2.2 name query
      exact exists_fits_iff.mp ⟨bytes, fits⟩
  · classical
    rintro ⟨binding, old, compatible⟩
    let pick (name : Name) : Bytes := if asked : seen.Queried name then
      (exists_fits_iff.mpr (compatible name asked)).choose else []
    refine ⟨_, model_of_pick binding old pick ?_⟩
    intro name asked _
    simpa only [pick, dite_eq_left asked] using (exists_fits_iff.mpr (compatible name asked)).choose_spec

theorem exists_unique_model_iff : (∃ rel, seen.Model base rel ∧ UniqueNames rel) ↔
    Binding base ∧ UniqueNames base ∧ (∀ ⦃name bytes⦄, base name bytes → seen.Fits name bytes) ∧
    ∃ pick, seen.FreshAssignment base pick := by
  classical
  constructor
  · rintro ⟨rel, model, unique⟩
    have conditions := exists_model_iff.mp ⟨rel, model⟩
    let pick (name : Name) : Bytes := if asked : seen.Queried name then
      (model.2.2.2 name asked).choose else []
    have picked : ∀ name, seen.Queried name → rel name (pick name) ∧ seen.Fits name (pick name) := by
      intro name asked
      simpa only [pick, dite_eq_left asked] using (model.2.2.2 name asked).choose_spec
    refine ⟨conditions.1, fun {_ _ _} left right => unique (model.2.1 left) (model.2.1 right), conditions.2.1,
      pick, fun name fresh => (picked name fresh.1).2, ?_, ?_⟩
    · intro name fresh old hit
      have eq := unique (model.2.1 hit) (picked name fresh.1).1
      exact fresh.2 ⟨pick name, eq ▸ hit⟩
    · intro left right lh rh eq
      exact unique (eq ▸ (picked left lh.1).1) (picked right rh.1).1
  · rintro ⟨binding, unique, old, pick, fits, avoids, distinct⟩
    refine ⟨_, model_of_pick binding old pick (fun name asked absent => fits name ⟨asked, absent⟩), ?_⟩
    rintro bytes left right (lh | ⟨labsent, lasked, rfl⟩) (rh | ⟨rabsent, rasked, eq⟩)
    · exact unique lh rh
    · exact (avoids right ⟨rasked, rabsent⟩ left (eq ▸ lh)).elim
    · exact (avoids left ⟨lasked, labsent⟩ right rh).elim
    · exact distinct left right ⟨lasked, labsent⟩ ⟨rasked, rabsent⟩ eq

end Silmaril.Proofs.Semantics.Naming.ByteRange.Extension
