module

public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Determinism toolkit: values and the first non-value

List lemmas about `vals` and `Val.toAdmin`: injectivity, and uniqueness of the
decomposition `vals vs ++ e :: rest` of a code at its first non-value `e`.
These only need Core reduction, not the single-threaded layer.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core

theorem val?_eq_some {a : Admin} {v : Val} : a.val? = some v ↔ a = v.toAdmin := by
  constructor
  · intro h
    rcases a with (_ | _ | _ | _ | _ | _ | _ | _)
    all_goals try (simp [Admin.val?] at h; done)
    · rename_i i
      cases i <;> simp [Admin.val?] at h <;> subst h <;> rfl
    · simp [Admin.val?] at h; subst h; rfl
  · rintro rfl; simp

@[simp] theorem toAdmin_inj {v w : Val} : v.toAdmin = w.toAdmin ↔ v = w := by
  constructor
  · intro h
    have := congrArg Admin.val? h
    simpa using this
  · rintro rfl; rfl

theorem toAdmin_eq_iff {v : Val} {a : Admin} : v.toAdmin = a ↔ a.val? = some v := by
  rw [val?_eq_some]; exact eq_comm

theorem eq_toAdmin_iff {v : Val} {a : Admin} : a = v.toAdmin ↔ a.val? = some v := by
  rw [val?_eq_some]

@[simp] theorem vals_nil : vals [] = [] := rfl
@[simp] theorem vals_cons (v : Val) (vs : List Val) : vals (v :: vs) = v.toAdmin :: vals vs := rfl

@[simp] theorem vals_inj {xs ys : List Val} : vals xs = vals ys ↔ xs = ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
        simp only [vals_cons, List.cons.injEq, toAdmin_inj] at h
        rw [h.1, ih h.2]
  · rintro rfl; rfl

@[simp] theorem vals_eq_nil {xs : List Val} : vals xs = [] ↔ xs = [] := by
  cases xs <;> simp

theorem mem_vals {a : Admin} {vs : List Val} (h : a ∈ vals vs) : a.val? ≠ none := by
  simp only [vals, List.mem_map] at h
  obtain ⟨v, -, rfl⟩ := h
  simp

/-- Uniqueness of the first non-value. -/
theorem vals_append_cons_inj : ∀ {k₁ k₂ : List Val} {e₁ e₂ : Admin} {t₁ t₂ : List Admin},
    vals k₁ ++ e₁ :: t₁ = vals k₂ ++ e₂ :: t₂ → e₁.val? = none → e₂.val? = none →
    k₁ = k₂ ∧ e₁ = e₂ ∧ t₁ = t₂
  | [], [], _, _, _, _, h, _, _ => by simpa using h
  | [], v :: _, _, _, _, _, h, h₁, _ => by
    simp only [vals_nil, List.nil_append, vals_cons, List.cons_append, List.cons.injEq] at h
    rw [h.1] at h₁; simp at h₁
  | v :: _, [], _, _, _, _, h, _, h₂ => by
    simp only [vals_nil, List.nil_append, vals_cons, List.cons_append, List.cons.injEq] at h
    rw [← h.1] at h₂; simp at h₂
  | v :: k₁, w :: k₂, _, _, _, _, h, h₁, h₂ => by
    simp only [vals_cons, List.cons_append, List.cons.injEq, toAdmin_inj] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := vals_append_cons_inj h h₁ h₂
    exact ⟨rfl, rfl, rfl⟩

theorem vals_ne_append_cons {vs k : List Val} {e : Admin} {t : List Admin} (he : e.val? = none) :
    vals vs ≠ vals k ++ e :: t := by
  intro h
  have : e ∈ vals vs := by rw [h]; simp
  exact mem_vals this he

theorem vals_eq_append {W : List Val} {A B : List Admin} (h : vals W = A ++ B) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ A = vals W₁ ∧ B = vals W₂ := by
  simp only [vals] at h
  obtain ⟨W₁, W₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp h
  exact ⟨W₁, W₂, rfl, rfl, rfl⟩

/-- Two value lists with a common extension: one is a suffix of the other. -/
theorem append_eq_append_suffix {α : Type _} {a b c d : List α} (h : a ++ b = c ++ d) :
    (∃ p, b = p ++ d) ∨ (∃ p, d = p ++ b) := by
  rcases List.append_eq_append_iff.mp h with ⟨p, rfl, hp⟩ | ⟨p, rfl, hp⟩
  · exact .inl ⟨p, hp⟩
  · exact .inr ⟨p, hp⟩

/-- The first non-value decomposition (a copy of `splitVals` that does not need
the single-threaded layer). -/
def fnv : List Admin → List Val × List Admin
  | [] => ([], [])
  | a :: as =>
    match a.val? with
    | some v => (v :: (fnv as).1, (fnv as).2)
    | none => ([], a :: as)

@[simp] theorem fnv_nil : fnv [] = ([], []) := rfl

theorem fnv_cons_of_none {a : Admin} (h : a.val? = none) (l : List Admin) :
    fnv (a :: l) = ([], a :: l) := by
  simp [fnv, h]

@[simp] theorem fnv_toAdmin_cons (v : Val) (l : List Admin) :
    fnv (v.toAdmin :: l) = (v :: (fnv l).1, (fnv l).2) := by
  simp [fnv]

@[simp] theorem fnv_vals_append (vs : List Val) (l : List Admin) :
    fnv (vals vs ++ l) = (vs ++ (fnv l).1, (fnv l).2) := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih]

@[simp] theorem fnv_vals (vs : List Val) : fnv (vals vs) = (vs, []) := by
  simpa using fnv_vals_append vs []

theorem append_singleton_inj {α : Type _} {l₁ l₂ : List α} {a b : α} :
    l₁ ++ [a] = l₂ ++ [b] ↔ l₁ = l₂ ∧ a = b := by
  constructor
  · intro h
    have := List.append_inj' h rfl
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

end Silmaril.Wasm.SingleThreaded.Det
