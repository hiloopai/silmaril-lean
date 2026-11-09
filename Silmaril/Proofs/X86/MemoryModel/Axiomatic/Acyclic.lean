module

public import Silmaril.X86.MemoryModel.Axiomatic.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WellFounded

/-!
# Acyclicity of finite Boolean relations: proofs

Correctness of `BRel.acyclicB` (Kahn's algorithm) against `BRel.Acyclic` (no `TransGen`
cycle), monotonicity, and the cycle-shape lemma behind "x86-TSO implies no-thin-air".
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Relation

namespace BRel
variable {n : Nat}

/-- `r` restricted to `S`. -/
def restrict (r : Axiomatic.BRel n) (S : List (Fin n)) (a b : Fin n) : Prop :=
  a ∈ S ∧ b ∈ S ∧ r a b = true

theorem source?_mem (r : Axiomatic.BRel n) (S : List (Fin n)) :
    ∀ (l : List (Fin n)) (b : Fin n), Axiomatic.BRel.source? r S l = some b →
      b ∈ l ∧ ∀ a ∈ S, r a b = false := by
  intro l
  induction l with
  | nil => intro b h; simp [Axiomatic.BRel.source?] at h
  | cons c l ih =>
    intro b h
    simp only [Axiomatic.BRel.source?] at h
    split at h
    · rename_i hall
      cases h
      refine ⟨List.mem_cons_self, fun a ha => ?_⟩
      have := List.all_eq_true.mp hall a ha
      simpa using this
    · have := ih b h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem source?_none (r : Axiomatic.BRel n) (S : List (Fin n)) :
    ∀ (l : List (Fin n)), Axiomatic.BRel.source? r S l = none →
      ∀ b ∈ l, ∃ a ∈ S, r a b = true := by
  intro l
  induction l with
  | nil => intro _ b hb; simp at hb
  | cons c l ih =>
    intro h b hb
    simp only [Axiomatic.BRel.source?] at h
    split at h
    · cases h
    · rename_i hall
      rcases List.mem_cons.mp hb with rfl | hb
      · simp only [List.all_eq_true, Bool.not_eq_true', not_forall] at hall
        obtain ⟨a, ha, hr⟩ := hall
        exact ⟨a, ha, by simpa using hr⟩
      · exact ih h b hb

theorem tg_head {r : Fin n → Fin n → Prop} {a b : Fin n} (h : TransGen r a b) : ∃ c, r a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem tg_last {r : Fin n → Fin n → Prop} {a b : Fin n} (h : TransGen r a b) : ∃ c, r c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

/-- Removing a source keeps every cycle. -/
theorem restrict_erase (r : Axiomatic.BRel n) (S : List (Fin n)) (b : Fin n)
    (hb : ∀ a ∈ S, r a b = false) {c d : Fin n} (h : TransGen (restrict r S) c d)
    (hc : c ≠ b) : TransGen (restrict r (S.erase b)) c d := by
  have notb : ∀ {e f}, restrict r S e f → f ≠ b := by
    rintro e f ⟨he, -, hr⟩ rfl
    simp [hb e he] at hr
  induction h with
  | single h =>
    exact .single ⟨(List.mem_erase_of_ne hc).mpr h.1, (List.mem_erase_of_ne (notb h)).mpr h.2.1,
      h.2.2⟩
  | @tail e f hce hef ih =>
    have he : e ≠ b := by
      obtain ⟨g, hg⟩ := tg_last hce
      exact notb hg
    exact .tail ih ⟨(List.mem_erase_of_ne he).mpr hef.1,
      (List.mem_erase_of_ne (notb hef)).mpr hef.2.1, hef.2.2⟩

theorem peel_sound (r : Axiomatic.BRel n) :
    ∀ (k : Nat) (S : List (Fin n)), Axiomatic.BRel.peel r k S = true →
      ∀ a, ¬ TransGen (restrict r S) a a := by
  have base : ∀ S : List (Fin n), S.isEmpty = true → ∀ a, ¬ TransGen (restrict r S) a a := by
    intro S hS a h
    obtain ⟨c, hc, -⟩ := tg_head h
    simp [List.isEmpty_iff.mp hS] at hc
  intro k
  induction k with
  | zero => intro S h; exact base S h
  | succ k ih =>
    intro S h a ha
    simp only [Axiomatic.BRel.peel] at h
    split at h
    · exact base S h a ha
    · rename_i b hsrc
      obtain ⟨_, hb⟩ := source?_mem r S S b hsrc
      have hab : a ≠ b := by
        rintro rfl
        obtain ⟨c, ⟨hc, -, hr⟩⟩ := tg_last ha
        simp [hb c hc] at hr
      exact ih _ h a (restrict_erase r S b hb ha hab)

/-- A nonempty set in which every node has a predecessor carries a cycle. -/
theorem cycle_of_pred (r : Axiomatic.BRel n) (S : List (Fin n)) (hS : S ≠ [])
    (hp : ∀ b ∈ S, ∃ a ∈ S, r a b = true) : ∃ a, TransGen r.Holds a a := by
  by_contra hno
  have : IsTrans (Fin n) (TransGen r.Holds) := ⟨fun _ _ _ => TransGen.trans⟩
  have : Std.Irrefl (TransGen r.Holds) := ⟨fun a h => hno ⟨a, h⟩⟩
  have wf : WellFounded (TransGen r.Holds) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨b0, hb0⟩ := List.exists_mem_of_ne_nil S hS
  obtain ⟨m, hm, hmin⟩ := wf.has_min {b | b ∈ S} ⟨b0, hb0⟩
  obtain ⟨a, ha, hr⟩ := hp m hm
  exact hmin a ha (.single hr)

theorem peel_complete (r : Axiomatic.BRel n) :
    ∀ (k : Nat) (S : List (Fin n)), S.length ≤ k → Axiomatic.BRel.peel r k S = false →
      ∃ a, TransGen r.Holds a a := by
  intro k
  induction k with
  | zero =>
    intro S hl h
    have : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    simp [Axiomatic.BRel.peel, this] at h
  | succ k ih =>
    intro S hl h
    simp only [Axiomatic.BRel.peel] at h
    split at h
    · rename_i hsrc
      have hS : S ≠ [] := by intro hS; simp [hS] at h
      exact cycle_of_pred r S hS (source?_none r S S hsrc)
    · rename_i b hsrc
      obtain ⟨hbS, -⟩ := source?_mem r S S b hsrc
      refine ih _ ?_ h
      rw [List.length_erase_of_mem hbS]
      omega

theorem restrict_univ (r : Axiomatic.BRel n) :
    restrict r (List.finRange n) = r.Holds := by
  funext a b
  simp [restrict, Axiomatic.BRel.Holds]

/-- `acyclicB` decides `Acyclic`. -/
theorem acyclic_iff (r : Axiomatic.BRel n) : r.Acyclic ↔ r.acyclicB = true := by
  constructor
  · intro h
    cases hb : r.acyclicB
    · obtain ⟨a, ha⟩ := peel_complete r n (List.finRange n) (by simp) hb
      exact absurd ha (h a)
    · rfl
  · intro h a
    have := peel_sound r n (List.finRange n) h a
    rwa [restrict_univ] at this

/-- Monotonicity of acyclicity: if every `r` edge is an `s` path, `s` acyclic gives `r`
acyclic. -/
theorem acyclic_mono {r s : Axiomatic.BRel n}
    (h : ∀ a b, r a b = true → TransGen s.Holds a b) (hs : s.Acyclic) : r.Acyclic := by
  intro a ha
  apply hs a
  have key : ∀ {c d}, TransGen r.Holds c d → TransGen s.Holds c d := by
    intro c d hcd
    induction hcd with
    | single hcd => exact h _ _ hcd
    | tail _ hef ih => exact ih.trans (h _ _ hef)
  exact key ha

theorem emptyB_iff (r : Axiomatic.BRel n) : r.emptyB = true ↔ r.Empty := by
  simp [Axiomatic.BRel.emptyB, Axiomatic.BRel.Empty]

/-- The shape lemma for no-thin-air. Let `po` be a strict order, `E` edges from `isW` nodes to
`isR` nodes (disjoint kinds), and `G` a relation containing `E` and every `po` edge from an
`isR` node to an `isW` node. If `G` is acyclic, so is `po ∪ E`. -/
theorem acyclic_po_union (po E G : Axiomatic.BRel n) (isR isW : Fin n → Bool)
    (trans : ∀ a b c, po a b = true → po b c = true → po a c = true)
    (irr : ∀ a, po a a = false)
    (hE : ∀ a b, E a b = true → isW a = true ∧ isR b = true)
    (hRW : ∀ a, isR a = true → isW a = true → False)
    (hEG : ∀ a b, E a b = true → G a b = true)
    (hRM : ∀ a b, isR a = true → isW b = true → po a b = true → G a b = true)
    (hG : G.Acyclic) : (po.union E).Acyclic := by
  -- every path is a `po` edge, or `po?` to a write `w`, then a `G` path to a read `r`,
  -- then `po?`
  have claim : ∀ {a b}, TransGen (po.union E).Holds a b →
      po a b = true ∨ ∃ w r, (a = w ∨ po a w = true) ∧ isW w = true ∧ TransGen G.Holds w r ∧
        isR r = true ∧ (r = b ∨ po r b = true) := by
    intro a b h
    induction h with
    | single h =>
      simp only [Axiomatic.BRel.Holds, Axiomatic.BRel.union, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨a, _, .inl rfl, (hE _ _ h).1, .single (hEG _ _ h), (hE _ _ h).2, .inl rfl⟩
    | @tail c b _ hcb ih =>
      simp only [Axiomatic.BRel.Holds, Axiomatic.BRel.union, Bool.or_eq_true] at hcb
      rcases ih with hac | ⟨w, r, haw, hw, hwr, hr, hrc⟩
      · rcases hcb with hcb | hcb
        · exact .inl (trans _ _ _ hac hcb)
        · exact .inr ⟨c, b, .inr hac, (hE _ _ hcb).1, .single (hEG _ _ hcb), (hE _ _ hcb).2,
            .inl rfl⟩
      · rcases hcb with hcb | hcb
        · refine .inr ⟨w, r, haw, hw, hwr, hr, .inr ?_⟩
          rcases hrc with rfl | hrc
          · exact hcb
          · exact trans _ _ _ hrc hcb
        · have hcW := (hE _ _ hcb).1
          have hrc' : po r c = true := by
            rcases hrc with rfl | hrc
            · exact (hRW _ hr hcW).elim
            · exact hrc
          refine .inr ⟨w, b, haw, hw, ?_, (hE _ _ hcb).2, .inl rfl⟩
          exact (hwr.tail (hRM _ _ hr hcW hrc')).tail (hEG _ _ hcb)
  intro a ha
  rcases claim ha with h | ⟨w, r, haw, hw, hwr, hr, hra⟩
  · simp [irr a] at h
  · -- close the cycle `w -G+-> r -po?-> a -po?-> w`
    apply hG w
    have hrw : r = w ∨ po r w = true := by
      rcases hra with rfl | hra
      · exact haw
      · rcases haw with rfl | haw
        · exact .inr hra
        · exact .inr (trans _ _ _ hra haw)
    rcases hrw with rfl | hrw
    · exact (hRW _ hr hw).elim
    · exact hwr.tail (hRM _ _ hr hw hrw)

end BRel

end Silmaril.X86.MemoryModel.Axiomatic.Proofs
