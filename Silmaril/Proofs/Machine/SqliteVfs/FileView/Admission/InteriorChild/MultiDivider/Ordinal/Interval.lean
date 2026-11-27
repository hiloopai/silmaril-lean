module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.Defs

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal

open Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

theorem childAt_ordinal (page : Interior) (key : Int) :
    page.childAt? (page.childOrdinal key) = some (page.choose key) := by
  unfold Interior.childAt? Interior.choose Interior.childOrdinal
  rw [List.find?_eq_getElem?_findIdx]
  cases located : page.dividers[page.dividers.findIdx (fun divider => decide (key ≤ divider.upperKey))]? with
  | some _ => rfl
  | none =>
    have endIndex := List.getElem?_eq_none_iff.mp located
    have bound := List.findIdx_le_length (xs := page.dividers)
      (p := fun divider => decide (key ≤ divider.upperKey))
    simp only [Nat.le_antisymm bound endIndex, ite_true]

/-- The selected ordinal always satisfies its adjacent signed bounds. -/
theorem ordinal_interval (page : Interior) (key : Int) :
    page.ChildInterval key (page.childOrdinal key) := by
  refine ⟨List.findIdx_le_length, ?_, ?_⟩
  · intro prev adjacent lower located
    obtain ⟨_, found⟩ := List.getElem_of_getElem? located
    have before : prev < page.childOrdinal key := by omega
    have missed := List.not_of_lt_findIdx (p := fun divider : Divider => decide (key ≤ divider.upperKey)) before
    rw [found] at missed
    simpa using missed
  · intro upper located
    have found := List.findIdx_of_getElem?_eq_some
      (p := fun divider : Divider => decide (key ≤ divider.upperKey)) located
    simpa using found

/-- Strict pointer-order sorting gives the converse: the unique ordinal
whose adjacent bounds contain the key is the selected ordinal. -/
theorem ordinal_eq_iff_interval (page : Interior) (key : Int) (ordinal : Nat)
    (sorted : page.dividers.Pairwise (fun left right => left.upperKey < right.upperKey)) :
    page.childOrdinal key = ordinal ↔ page.ChildInterval key ordinal := by
  constructor
  · rintro rfl
    exact ordinal_interval page key
  · rintro ⟨inRange, lowerBound, upperBound⟩
    have preceding (j : Nat) (earlier : j < ordinal) :
        let valid := Nat.lt_of_lt_of_le earlier inRange
        page.dividers[j]'valid |>.upperKey < key := by
      let prev := ordinal - 1
      have adjacent : prev + 1 = ordinal := by dsimp [prev]; omega
      have validPrev : prev < page.dividers.length := by omega
      have atLower := lowerBound prev adjacent _ (List.getElem?_eq_getElem validPrev)
      have beforeOrAt : j ≤ prev := by omega
      rcases Nat.eq_or_lt_of_le beforeOrAt with rfl | before
      · exact atLower
      · exact Int.lt_trans (sorted.rel_getElem_of_lt _ validPrev before) atLower
    by_cases hasUpper : ordinal < page.dividers.length
    · apply (List.findIdx_eq hasUpper).2
      refine ⟨?_, ?_⟩
      · simpa using upperBound _ (List.getElem?_eq_getElem hasUpper)
      · intro j hj
        simpa using preceding j hj
    · have rightmost : ordinal = page.dividers.length := by omega
      rw [rightmost, Interior.childOrdinal]
      apply List.findIdx_eq_length_of_false
      intro divider present
      obtain ⟨j, located⟩ := List.getElem?_of_mem present
      obtain ⟨valid, found⟩ := List.getElem_of_getElem? located
      have before : j < ordinal := rightmost.symm ▸ valid
      have earlier := preceding j before
      dsimp only at earlier
      rw [found] at earlier
      simpa using earlier

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal
