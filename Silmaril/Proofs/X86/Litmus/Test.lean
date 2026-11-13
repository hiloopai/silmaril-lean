module

public import Silmaril.X86.Litmus.Test.Defs
public import Silmaril.X86.Litmus.Extract.Thms

/-!
# Litmus tests: soundness of whole-test extraction

* `sound_of_views`: if the views of a test compute (so every thread's extraction succeeded),
  the test is `Test.Sound`.
* `nonVacuous_of_placed`: a `placed` test is `Test.NonVacuous`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Litmus

open Silmaril.X86.Litmus

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = some rs → ∀ x ∈ l, ∃ r, f x = some r
  | [], _, _, x, hx => by simp at hx
  | y :: l, rs, h, x, hx => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hy, rs', hl, -⟩ := h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨r, hy⟩
    · exact mapM_some hl x hx

theorem sound_of_views {T : Test} {v : List (List View)} (h : T.views = some v) : T.Sound := by
  intro k hk
  unfold Test.views at h
  obtain ⟨trss, he, -⟩ := Option.map_eq_some_iff.mp h
  unfold Test.extractAll at he
  obtain ⟨trs, hg⟩ := mapM_some he k (List.mem_range.mpr hk)
  obtain ⟨t, ht, hx⟩ := Option.bind_eq_some_iff.mp hg
  exact ⟨t, trs, ht, hx, Silmaril.X86.Litmus.extract_sound hx⟩

theorem nonVacuous_of_placed {T : Test} (h : T.placed = true) : T.NonVacuous := by
  intro k hk
  unfold Test.placed at h
  have hk' := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  split at hk'
  · cases hk'
  · rename_i t ht
    split at hk'
    · rename_i trs hx
      exact ⟨t, trs, ht, hx, Silmaril.X86.Litmus.allPlaced_satisfiable hk'⟩
    · cases hk'

end Silmaril.Proofs.X86.Litmus
