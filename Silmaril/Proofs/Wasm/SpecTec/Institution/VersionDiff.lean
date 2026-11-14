module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount

/-!
# The exact set of rules a script drops, checked in pieces

`VersionCount` decides `φ ∈ theoryOf env` (`inTheoryB`) and counts the retained rules
(`retainedCount`). This module names the dropped rules instead. A rule sentence has a *key*,
the name of its relation and the name of the rule (`SSen.key`). For a list `ks` of keys,
`keepsExcept env₂ ks φ` says that `env₂` keeps `φ` exactly when `φ`'s key is not in `ks`. If
that holds of every rule of `env₁`:

* `dropped_eq_of_all`: `dropped env₁ env₂` is the set of rules of `env₁` whose key is in `ks`;
* `retainedCount_eq_of_all`: `retainedCount env₁ env₂` is the number of entries of
  `ruleList env₁` whose key is not in `ks`, which the kernel evaluates without printing a rule.

The check over all rules can be split into chunks `chunkOk env₁ env₂ ks i n` (the rules
`i, …, i + n - 1`), each evaluated in its own module (`all_drop_of_chunk`,
`all_drop_of_length_le`, `all_of_all_drop_zero`), so that no module evaluates more than its share.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The relation name and rule name of a rule sentence (`("", "")` for a fact, which is never
in a theory). -/
def SSen.key : SSen → IL.Id × IL.Id
  | .rule d r => (d.1, ruleName r)
  | .fact .. => ("", "")

/-- `env₂` keeps `φ` exactly when the key of `φ` is not in `ks`. -/
def keepsExcept (env₂ : Env) (ks : List (IL.Id × IL.Id)) (φ : SSen) : Bool :=
  inTheoryB env₂ φ == !(ks.contains φ.key)

/-- `keepsExcept` on the rules `i, …, i + n - 1` of `env₁`. -/
def chunkOk (env₁ env₂ : Env) (ks : List (IL.Id × IL.Id)) (i n : Nat) : Bool :=
  (((ruleList env₁).drop i).take n).all (keepsExcept env₂ ks)

/-- A chunk and the rest after it give the rest from the chunk's start. The index `j` of the
rest is given separately (and `i + n = j` checked by `decide`), so that no unification has to
look inside `ruleList`. -/
theorem all_drop_of_chunk {env₁ env₂ : Env} {ks : List (IL.Id × IL.Id)} {i n j : Nat}
    (hc : chunkOk env₁ env₂ ks i n = true)
    (hr : ((ruleList env₁).drop j).all (keepsExcept env₂ ks) = true)
    (hj : i + n = j := by decide) :
    ((ruleList env₁).drop i).all (keepsExcept env₂ ks) = true := by
  subst hj
  rw [← List.take_append_drop n ((ruleList env₁).drop i), List.all_append, List.drop_drop]
  exact Bool.and_eq_true _ _ ▸ ⟨hc, hr⟩

/-- The check from index `0` is the check of every rule. -/
theorem all_of_all_drop_zero {env₁ env₂ : Env} {ks : List (IL.Id × IL.Id)}
    (h : ((ruleList env₁).drop 0).all (keepsExcept env₂ ks) = true) :
    (ruleList env₁).all (keepsExcept env₂ ks) = true := by
  rwa [List.drop_zero] at h

/-- Past the end there is nothing to check. -/
theorem all_drop_of_length_le {env₁ env₂ : Env} {ks : List (IL.Id × IL.Id)} {i : Nat}
    (h : (ruleList env₁).length ≤ i) :
    ((ruleList env₁).drop i).all (keepsExcept env₂ ks) = true := by
  simp [List.drop_eq_nil_of_le h]

/-- **The dropped rules are the rules with a key in `ks`.** -/
theorem dropped_eq_of_all {env₁ env₂ : Env} {ks : List (IL.Id × IL.Id)}
    (h : (ruleList env₁).all (keepsExcept env₂ ks) = true) :
    dropped env₁ env₂ = {φ | φ ∈ theoryOf env₁ ∧ φ.key ∈ ks} := by
  ext φ
  simp only [dropped, Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hl : φ ∈ ruleList env₁ := by rw [theoryOf_eq_ruleList] at h₁; exact h₁
    have hk := List.all_eq_true.mp h φ hl
    rw [← inTheoryB_iff] at h₂
    simp only [keepsExcept, Bool.not_eq_true] at hk h₂
    rw [h₂] at hk
    exact ⟨h₁, by simpa using hk⟩
  · rintro ⟨h₁, hk⟩
    have hl : φ ∈ ruleList env₁ := by rw [theoryOf_eq_ruleList] at h₁; exact h₁
    have he := List.all_eq_true.mp h φ hl
    refine ⟨h₁, fun h₂ => ?_⟩
    rw [← inTheoryB_iff] at h₂
    simp [keepsExcept, h₂, hk] at he

/-- **The retained count, read off the keys.** -/
theorem retainedCount_eq_of_all {env₁ env₂ : Env} {ks : List (IL.Id × IL.Id)}
    (h : (ruleList env₁).all (keepsExcept env₂ ks) = true) :
    retainedCount env₁ env₂ = (ruleList env₁).countP (fun φ => !(ks.contains φ.key)) := by
  unfold retainedCount
  refine List.countP_congr fun φ hφ => ?_
  have he := List.all_eq_true.mp h φ hφ
  simp only [keepsExcept, beq_iff_eq] at he
  rw [he]

/-- If exactly one entry of a list satisfies `p`, the entries satisfying `p` are one element. -/
theorem exists_unique_of_countP_eq_one {α : Type _} {l : List α} {p : α → Bool}
    (h : l.countP p = 1) : ∃ x, ∀ y, y ∈ l ∧ p y = true ↔ y = x := by
  rw [List.countP_eq_length_filter, List.length_eq_one_iff] at h
  obtain ⟨x, hx⟩ := h
  refine ⟨x, fun y => ?_⟩
  rw [← List.mem_filter, hx, List.mem_singleton]

/-- The keys of the entries of `ruleList env₁` with a key in `ks`, in order and with
multiplicity. `droppedKeys env₁ ks = ks` says each key of `ks` names exactly one entry. -/
def droppedKeys (env₁ : Env) (ks : List (IL.Id × IL.Id)) : List (IL.Id × IL.Id) :=
  ((ruleList env₁).filter fun φ => ks.contains φ.key).map SSen.key

/-- **A single dropped rule.** If the check holds and exactly one entry has a key in `ks`, the
dropped set is that one rule. -/
theorem dropped_eq_singleton {env₁ env₂ : Env} {ks : List (IL.Id × IL.Id)} {k : IL.Id × IL.Id}
    (h : (ruleList env₁).all (keepsExcept env₂ ks) = true) (hk : droppedKeys env₁ ks = [k]) :
    ∃ φ, dropped env₁ env₂ = {φ} ∧ φ.key = k := by
  have h1 : (ruleList env₁).countP (fun φ => ks.contains φ.key) = 1 := by
    rw [List.countP_eq_length_filter, ← List.length_map (f := SSen.key)]
    exact (congrArg List.length hk).trans rfl
  obtain ⟨x, hx⟩ := exists_unique_of_countP_eq_one h1
  have hxk : x.key = k := by
    have hm : x ∈ (ruleList env₁).filter fun φ => ks.contains φ.key :=
      List.mem_filter.mpr ((hx x).mpr rfl)
    have := List.mem_map_of_mem (f := SSen.key) hm
    rw [show List.map SSen.key _ = droppedKeys env₁ ks from rfl, hk] at this
    exact List.mem_singleton.mp this
  refine ⟨x, ?_, hxk⟩
  rw [dropped_eq_of_all h]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, theoryOf_eq_ruleList, ← hx y,
    List.contains_iff_mem]

/-- The entries of `ruleList env₁` without a key in `ks` are the others: their number is the
length minus that of `droppedKeys env₁ ks`. -/
theorem keptCount_eq (env₁ : Env) (ks : List (IL.Id × IL.Id)) :
    (ruleList env₁).countP (fun φ => !(ks.contains φ.key)) =
      (ruleList env₁).length - (droppedKeys env₁ ks).length := by
  rw [droppedKeys, List.length_map, ← List.countP_eq_length_filter,
    List.length_eq_countP_add_countP (fun φ => ks.contains φ.key)]
  simp

end Silmaril.Wasm.SpecTec.Institution
