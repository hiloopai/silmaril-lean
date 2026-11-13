module

public import Silmaril.Wasm.Tools.Gen.Cmd.SmithConfig.Defs

/-!
# `smith --config`: specification

`fromJson_sound`: every option value read from a configuration document belongs to a field
of the table (so `deny_unknown_fields` holds: an unknown key is an error, never a value).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.SmithConfig

open Lean (Json)

theorem step_inv (fields : List (String × Field)) (acc res : List (String × Args.Val))
    (kv : String × Json) (hacc : ∀ p ∈ acc, (fields.lookup p.1).isSome)
    (h : step fields acc kv = .ok res) : ∀ p ∈ res, (fields.lookup p.1).isSome := by
  obtain ⟨k, v⟩ := kv
  unfold step at h
  cases hl : fields.lookup k with
  | none => simp [hl] at h
  | some f =>
    simp only [hl] at h
    by_cases hn : (v == .null) = true
    · simp only [hn, ↓reduceIte, Except.ok.injEq] at h
      exact h ▸ hacc
    · simp only [hn] at h
      cases hv : value f v with
      | error e => simp [hv] at h
      | ok x =>
        simp only [hv, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
        intro p hp
        rw [← h] at hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hacc p hp
        · simp only [List.mem_singleton] at hp; subst hp; simp [hl]

theorem fold_inv (fields : List (String × Field)) :
    ∀ (l : List (String × Json)) (acc res : List (String × Args.Val)),
      (∀ p ∈ acc, (fields.lookup p.1).isSome) → l.foldlM (step fields) acc = .ok res →
      ∀ p ∈ res, (fields.lookup p.1).isSome
  | [], acc, res, hacc, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hacc
  | kv :: l, acc, res, hacc, h => by
    simp only [List.foldlM_cons] at h
    cases hs : step fields acc kv with
    | error e => simp [hs, bind, Except.bind] at h
    | ok acc' =>
      simp only [hs, bind, Except.bind] at h
      exact fold_inv fields l acc' res (step_inv fields acc acc' kv hacc hs) h

/-- **Every value read from a configuration is for a field of the table.** -/
theorem fromJson_sound {fields : List (String × Field)} {j : Json}
    {vals : List (String × Args.Val)} (h : fromJson fields j = .ok vals) :
    ∀ p ∈ vals, (fields.lookup p.1).isSome := by
  unfold fromJson at h
  split at h
  · exact fold_inv fields _ [] vals (by simp) h
  · cases h
  · cases h

end Silmaril.Wasm.Tools.Gen.Cmd.SmithConfig
