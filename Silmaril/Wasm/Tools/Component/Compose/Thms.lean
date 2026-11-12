module

public import Silmaril.Wasm.Tools.Component.Compose.Defs
public import Silmaril.Wasm.Wac.Types.Thms

/-!
# Theorems of `compose`'s resolution

* `argTarget_whole`, `argTarget_export`: an import is given the whole instance only when the
  instance's type is a WIT subtype of the import's, and an export only when that export is.
* `order_deps`: in the dependency order, every instance comes after the instances its arguments
  use, so the WAC document defines every instance before using it.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Compose

open Silmaril.Wasm.Wac (Kind Externs)

theorem argTarget_whole {es : Externs} {k : Kind} (h : argTarget es k = some none) :
    Wac.sub (.inst none es) k = true := by
  unfold argTarget at h
  split at h
  · assumption
  · split at h <;> cases h

theorem argTarget_export {es : Externs} {k : Kind} {e : String}
    (h : argTarget es k = some (some e)) : ∃ k', (e, k') ∈ es ∧ Wac.sub k' k = true := by
  unfold argTarget at h
  split at h
  · cases h
  · cases hf : es.find? (fun (_, k') => Wac.sub k' k) with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h
      obtain ⟨e', k'⟩ := p
      cases h
      have hm := List.find?_some hf
      exact ⟨k', List.mem_of_find?_eq_some hf, by simpa using hm⟩

theorem order_go_deps (xs : List Inst) : ∀ (fuel : Nat) (done todo out : List Nat),
    (∀ j ∈ done, ∀ i ∈ (xs.getD j default).deps, i ∈ done.take (done.idxOf j)) →
    order.go xs fuel done todo = some out →
    ∀ j ∈ out, ∀ i ∈ (xs.getD j default).deps, i ∈ out.take (out.idxOf j)
  | _, done, [], out, hd, h => by
    unfold order.go at h
    cases h
    exact hd
  | 0, _, _ :: _, _, _, h => by
    unfold order.go at h
    cases h
  | fuel + 1, done, t :: ts, out, hd, h => by
    unfold order.go at h
    split at h
    · rename_i i hi
      apply order_go_deps xs fuel (done ++ [i]) _ out _ h
      have hall := List.find?_some hi
      simp only [List.all_eq_true] at hall
      intro j hj a ha
      rcases List.mem_append.mp hj with hj | hj
      · have hl : (done ++ [i]).idxOf j = done.idxOf j := List.idxOf_append_of_mem hj
        rw [hl, List.take_append_of_le_length (List.idxOf_le_length)]
        exact hd j hj a ha
      · rw [List.mem_singleton.mp hj] at ha ⊢
        by_cases hin : i ∈ done
        · rw [List.idxOf_append_of_mem hin, List.take_append_of_le_length (List.idxOf_le_length)]
          exact hd i hin a ha
        · rw [List.idxOf_append_of_notMem hin]
          simp only [List.idxOf_cons_self, Nat.add_zero, List.take_left']
          have := hall a ha
          simpa using this
    · cases h

/-- **Dependencies come first**: each instance of the order comes after the instances its
arguments use. -/
theorem order_deps {xs : List Inst} {out : List Nat} (h : order xs = some out) :
    ∀ j ∈ out, ∀ i ∈ (xs.getD j default).deps, i ∈ out.take (out.idxOf j) :=
  order_go_deps xs _ [] _ out (by intro j hj; cases hj) h

end Silmaril.Wasm.Tools.Component.Compose
