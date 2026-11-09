module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs

/-!
# Litmus models: list helpers and the breadth-first search

Membership facts for the structural list functions of `Litmus.Models.Defs` (`memB`, `uniq`,
`nodupB`, `seqL`, `arrangements`, `memBy`, `uniqBy`) and the correctness of `collect`: what it
returns is exactly `fin` over the states reachable from the start.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Litmus

variable {α β : Type}

theorem memB_iff [DecidableEq α] (a : α) (l : List α) : memB a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons b l ih =>
    by_cases h : a = b
    · subst h; simp [memB]
    · simp [memB, h, ih]

theorem mem_addU [DecidableEq α] (a b : α) (l : List α) : b ∈ addU a l ↔ b = a ∨ b ∈ l := by
  unfold addU
  split
  · rename_i h
    rw [memB_iff] at h
    constructor
    · exact Or.inr
    · rintro (rfl | h') <;> assumption
  · simp

theorem mem_uniq [DecidableEq α] (a : α) (l : List α) : a ∈ uniq l ↔ a ∈ l := by
  unfold uniq
  induction l with
  | nil => simp
  | cons b l ih => simp [List.foldr_cons, mem_addU, ih]

theorem nodupB_iff [DecidableEq α] (l : List α) : nodupB l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupB]
  | cons a l ih =>
    have h := memB_iff a l
    cases hm : memB a l
    · simp only [nodupB, hm, Bool.not_false, Bool.true_and, ih, List.nodup_cons]
      simp only [hm, Bool.false_eq_true, false_iff] at h
      simp [h]
    · simp only [hm, true_iff] at h
      simp [nodupB, hm, h]

theorem mem_seqL (l : List α) (ls : List (List α)) :
    l ∈ seqL ls ↔ List.Forall₂ (· ∈ ·) l ls := by
  induction ls generalizing l with
  | nil =>
    simp only [seqL, List.mem_singleton]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons m ls ih =>
    simp only [seqL, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, l', hl', rfl⟩
      exact .cons ha ((ih l').mp hl')
    · intro h
      cases h with
      | cons ha hrest => exact ⟨_, ha, _, (ih _).mpr hrest, rfl⟩

theorem forall₂_mem_replicate {w l : List α} (n : Nat) :
    List.Forall₂ (· ∈ ·) l (List.replicate n w) ↔ l.length = n ∧ ∀ a ∈ l, a ∈ w := by
  induction n generalizing l with
  | zero =>
    simp only [List.replicate_zero]
    constructor
    · intro h; cases h; simp
    · rintro ⟨hl, -⟩
      rw [List.eq_nil_of_length_eq_zero hl]; exact .nil
  | succ n ih =>
    simp only [List.replicate_succ]
    constructor
    · intro h
      cases h with
      | cons ha hr =>
        obtain ⟨hl, hall⟩ := ih.mp hr
        refine ⟨by simp [hl], ?_⟩
        intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact ha
        · exact hall b hb
    · rintro ⟨hl, hall⟩
      cases l with
      | nil => simp at hl
      | cons a l' =>
        exact .cons (hall a (by simp))
          (ih.mpr ⟨by simpa using hl, fun b hb => hall b (by simp [hb])⟩)

/-- `arrangements w` holds exactly the repetition-free lists of `w`'s length over `w`'s
elements. -/
theorem mem_arrangements [DecidableEq α] (w l : List α) :
    l ∈ arrangements w ↔ l.Nodup ∧ l.length = w.length ∧ ∀ a ∈ l, a ∈ w := by
  unfold arrangements
  rw [List.mem_filter, mem_seqL, List.map_const', forall₂_mem_replicate, nodupB_iff]
  tauto

theorem memBy_iff {eq : α → α → Bool} (heq : ∀ a b, eq a b = true ↔ a = b) (a : α) (l : List α) :
    memBy eq a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memBy]
  | cons b l ih =>
    by_cases h : a = b
    · subst h; simp [memBy, (heq a a).mpr rfl]
    · have : eq a b = false := by
        cases hb : eq a b
        · rfl
        · exact absurd ((heq a b).mp hb) h
      simp [memBy, this, ih, h]

theorem mem_uniqBy {eq : α → α → Bool} (heq : ∀ a b, eq a b = true ↔ a = b) (a : α)
    (l : List α) : a ∈ uniqBy eq l ↔ a ∈ l := by
  unfold uniqBy
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons]
    split
    · rename_i h
      rw [memBy_iff heq] at h
      rw [ih]
      constructor
      · exact List.mem_cons_of_mem b
      · intro h'
        simp only [List.mem_cons] at h'
        rcases h' with rfl | h'
        · rwa [ih] at h
        · exact h'
    · simp [ih]

/-! ## The breadth-first search -/

/-- **`collect` is exactly `fin` over the reachable states** (when it succeeds). -/
theorem collect_spec {eq : α → α → Bool} (heq : ∀ a b, eq a b = true ↔ a = b)
    {succ : α → List α} {fin : α → List β} :
    ∀ (k : Nat) (L : List α) (out : List β), collect eq succ fin k L = some out →
      ∀ b, b ∈ out ↔ ∃ a ∈ L, ∃ c, Relation.ReflTransGen (fun x y => y ∈ succ x) a c ∧ b ∈ fin c := by
  intro k
  induction k with
  | zero =>
    intro L out h b
    simp only [collect] at h
    split at h
    · rename_i hL
      cases h
      simp only [List.isEmpty_iff] at hL
      subst hL
      simp
    · cases h
  | succ k ih =>
    intro L out h b
    simp only [collect] at h
    obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
    have hrec := ih _ _ h' b
    simp only [List.mem_append, List.mem_flatMap, hrec, stepL, mem_uniqBy heq]
    constructor
    · rintro (⟨a, ha, hb⟩ | ⟨a', ha', c, hc, hb⟩)
      · exact ⟨a, ha, a, .refl, hb⟩
      · obtain ⟨a, ha, hs⟩ := ha'
        exact ⟨a, ha, c, Relation.ReflTransGen.head hs hc, hb⟩
    · rintro ⟨a, ha, c, hc, hb⟩
      rcases Relation.ReflTransGen.cases_head hc with rfl | ⟨a', hs, hc'⟩
      · exact Or.inl ⟨a, ha, hb⟩
      · exact Or.inr ⟨a', ⟨a, ha, hs⟩, c, hc', hb⟩

end Silmaril.Proofs.X86.MemoryModel.Litmus
