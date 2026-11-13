module

public import Silmaril.Wasm.Tools.Component.Budget.Defs

/-!
# The type-size budget: wasmparser's `TypeInfo` rules as equations

* `combine_ok`: a successful `combine` adds the sizes, takes the depth `max a (o + 1)`, and
  stays within both limits;
* `combineAll_ok`: a successful `combineAll` has size one plus the sum of the members' sizes,
  below `MAX_WASM_TYPE_SIZE`; `combineAll_error`: when one plus the sum reaches the limit,
  `combineAll` refuses (whatever the depths);
* `defType_val_ok`, `defType_func_ok`: the size of a value or function type definition is one
  plus the sizes of its members (`Sc.members`, `Sc.funcMembers`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Budget

open Silmaril.Wasm.Component.Binary (DefValType FuncType)

theorem combine_ok {a o c : TI} (h : combine a o = .ok c) :
    c.size = a.size + o.size ∧ c.depth = max a.depth (o.depth + 1) ∧ c.size < maxSize ∧
      c.depth ≤ maxDepth := by
  unfold combine at h
  by_cases hd : maxDepth < max a.depth (o.depth + 1)
  · rw [ite_eq_left hd] at h
    cases h
  · rw [ite_eq_right hd] at h
    by_cases hs : a.size + o.size < maxSize
    · rw [ite_eq_left hs] at h
      have hc : (⟨a.size + o.size, max a.depth (o.depth + 1)⟩ : TI) = c := Except.ok.inj h
      rw [← hc]
      exact ⟨rfl, rfl, hs, Nat.le_of_not_lt hd⟩
    · rw [ite_eq_right hs] at h
      cases h

/-- The fold of `combine` from `acc`: size `acc.size` plus the members' sizes. -/
theorem foldlM_combine_ok : ∀ (os : List TI) (acc c : TI), os.foldlM combine acc = .ok c →
    c.size = acc.size + (os.map TI.size).sum ∧ c.size < maxSize ∨ (os = [] ∧ c = acc)
  | [], acc, c, h => by
    have hc : acc = c := Except.ok.inj h
    exact Or.inr ⟨rfl, hc.symm⟩
  | o :: os, acc, c, h => by
    rw [List.foldlM_cons] at h
    cases hco : combine acc o with
    | error e =>
      rw [hco] at h
      cases h
    | ok d =>
      rw [hco] at h
      have hd := combine_ok hco
      have ih := foldlM_combine_ok os d c h
      refine Or.inl ⟨?_, ?_⟩
      · rcases ih with ⟨hs, _⟩ | ⟨_, rfl⟩
        · rw [hs, hd.1, List.map_cons, List.sum_cons, Nat.add_assoc]
        · rw [hd.1]
          subst_vars
          simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.add_zero]
      · rcases ih with ⟨_, hs⟩ | ⟨_, rfl⟩
        · exact hs
        · exact hd.2.2.1

/-- **`combineAll`**: one plus the members' sizes, below the limit. -/
theorem combineAll_ok {os : List TI} {c : TI} (h : combineAll os = .ok c) :
    c.size = 1 + (os.map TI.size).sum ∧ c.size < maxSize := by
  rcases foldlM_combine_ok os TI.new c h with ⟨hs, hl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hs, hl⟩
  · exact ⟨rfl, by decide⟩

/-- **The refusal**: when one plus the members' sizes reaches `MAX_WASM_TYPE_SIZE`, the
aggregate is refused. -/
theorem combineAll_error {os : List TI} (h : maxSize ≤ 1 + (os.map TI.size).sum) :
    ∃ e, combineAll os = .error e := by
  cases hc : combineAll os with
  | error e => exact ⟨e, rfl⟩
  | ok c =>
    have hk := combineAll_ok hc
    omega

theorem defType_val_ok {outer : List Sc} {sc : Sc} {d : DefValType} {e : TEnt}
    (h : defType outer sc (.val d) = .ok e) :
    e.info.size = 1 + ((sc.members d).map TI.size).sum := by
  unfold defType at h
  cases hc : combineAll (sc.members d) with
  | error x =>
    rw [hc] at h
    cases h
  | ok c =>
    rw [hc] at h
    have he : (⟨c, []⟩ : TEnt) = e := Except.ok.inj h
    rw [← he]
    exact (combineAll_ok hc).1

theorem defType_func_ok {outer : List Sc} {sc : Sc} {f : Silmaril.Wasm.Component.Binary.FuncType} {e : TEnt}
    (h : defType outer sc (.func f) = .ok e) :
    e.info.size = 1 + ((sc.funcMembers f).map TI.size).sum := by
  unfold defType at h
  cases hc : combineAll (sc.funcMembers f) with
  | error x =>
    rw [hc] at h
    cases h
  | ok c =>
    rw [hc] at h
    have he : (⟨c, []⟩ : TEnt) = e := Except.ok.inj h
    rw [← he]
    exact (combineAll_ok hc).1

end Silmaril.Wasm.Tools.Component.Budget
