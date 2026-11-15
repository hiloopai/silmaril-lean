module

public import Silmaril.Semantics.Accept.Items.Defs
public import Silmaril.Semantics.Accept.Bounded.Thms
import Silmaril.Proofs.Semantics.Accept.Items.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Item sequences: laws

* `everyItem`: membership on `[]`, `::`, `++`, monotonicity, intersections, and Mathlib's
  Kleene star as flattening of item lists (`kstar_eq_image_flatten`);
* per-item vs whole-list bounds: a whole-list bound implies the per-item bound when each item
  weighs at least its measure (`totalWithin_subset_itemsWithin`); a per-item bound and a
  count bound imply a whole-list bound (`itemsWithin_inter_countWithin_subset`); and a per-item
  bound alone implies **no** whole-list bound (`itemsWithin_not_subset_totalWithin`);
* checkers: `List.all` lifts a checker for items to item lists (`Decides.everyItem`), and
  correctness on a per-item bounded domain lifts to the per-item bounded lists, of any
  length and total size (`DecidesOn.everyItem`);
* infinite sequences: membership is membership of every finite prefix
  (`mem_everyItemω_iff_take`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u

variable {ι : Type u} {L M : Set ι}

/-! ## Every item -/

@[simp] theorem mem_everyItem {s : List ι} : s ∈ everyItem L ↔ ∀ x ∈ s, x ∈ L := Iff.rfl

@[simp] theorem nil_mem_everyItem : ([] : List ι) ∈ everyItem L := fun _ h => absurd h (by simp)

@[simp] theorem cons_mem_everyItem {x : ι} {s : List ι} :
    x :: s ∈ everyItem L ↔ x ∈ L ∧ s ∈ everyItem L := List.forall_mem_cons

@[simp] theorem append_mem_everyItem {s t : List ι} :
    s ++ t ∈ everyItem L ↔ s ∈ everyItem L ∧ t ∈ everyItem L := List.forall_mem_append

theorem everyItem_mono (h : L ⊆ M) : everyItem L ⊆ everyItem M := fun _ hs x hx => h (hs x hx)

theorem everyItem_inter : everyItem (L ∩ M) = everyItem L ∩ everyItem M := by
  ext s; simp only [mem_everyItem, Set.mem_inter_iff]; exact ⟨fun h => ⟨fun x hx => (h x hx).1,
    fun x hx => (h x hx).2⟩, fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩

/-- Mathlib's Kleene star is the flattening of item lists whose items are in the language. -/
theorem kstar_eq_image_flatten {α : Type u} (L : Language α) :
    (KStar.kstar L : Language α) = List.flatten '' everyItem (L : Set (List α)) := by
  ext x; rw [Language.mem_kstar]; exact ⟨fun ⟨S, h, hS⟩ => ⟨S, hS, h.symm⟩,
    fun ⟨S, hS, h⟩ => ⟨S, h.symm, hS⟩⟩

/-! ## Per-item and whole-list bounds -/

section Bounds

variable {μ w : ι → ℕ} {m n k : ℕ}

theorem itemsWithin_mono (h : m ≤ n) : itemsWithin μ m ⊆ itemsWithin μ n :=
  everyItem_mono (within_mono h)

theorem totalWithin_mono (h : m ≤ n) : totalWithin w m ⊆ totalWithin w n := within_mono h

@[simp] theorem totalWeight_cons {x : ι} {s : List ι} :
    totalWeight w (x :: s) = w x + totalWeight w s := by simp [totalWeight]

@[simp] theorem totalWeight_append {s t : List ι} :
    totalWeight w (s ++ t) = totalWeight w s + totalWeight w t := by simp [totalWeight]

@[simp] theorem totalWeight_replicate {x : ι} :
    totalWeight w (List.replicate k x) = k * w x := by
  simp [totalWeight, List.map_replicate, List.sum_replicate]

/-- A whole-list bound bounds each item, if each item weighs at least its measure. -/
theorem totalWithin_subset_itemsWithin (h : ∀ x, μ x ≤ w x) :
    totalWithin w n ⊆ itemsWithin μ n := fun _ hs x hx =>
  (h x).trans ((List.le_sum_of_mem (List.mem_map_of_mem hx)).trans hs)

/-- A per-item bound and an item count bound give a whole-list bound. -/
theorem itemsWithin_inter_countWithin_subset :
    itemsWithin μ n ∩ countWithin k ⊆ totalWithin μ (k * n) :=
  Proofs.Semantics.Accept.Items.itemsWithin_inter_countWithin_subset

/-- A per-item bound alone bounds no whole-list weight: repeating one admissible item of
positive weight exceeds every bound. -/
theorem itemsWithin_not_subset_totalWithin {x : ι} (hx : μ x ≤ n) (hw : 0 < w x) (m : ℕ) :
    ¬ itemsWithin μ n ⊆ totalWithin w m :=
  Proofs.Semantics.Accept.Items.itemsWithin_not_subset_totalWithin hx hw m

end Bounds

/-! ## Checkers on item lists -/

section Checkers

variable {c : ι → Bool}

/-- `List.all` lifts a checker for items to finite item lists. -/
theorem Decides.everyItem (h : Decides c L) :
    Decides (fun s => s.all c) (everyItem L) := fun s => by
  simp only [List.all_eq_true, mem_everyItem, h _]

/-- Correctness on a domain of items lifts to the item lists inside that domain, whatever
their length and total weight: per-item bounded completeness is complete on unboundedly
large lists. -/
theorem DecidesOn.everyItem {D : Set ι} (h : DecidesOn D c L) :
    DecidesOn (Accept.everyItem D) (fun s => s.all c) (Accept.everyItem L) := fun s hs => by
  simp only [List.all_eq_true, mem_everyItem]
  exact ⟨fun hc x hx => (h x (hs x hx)).1 (hc x hx), fun hl x hx => (h x (hs x hx)).2 (hl x hx)⟩

theorem DecidesOn.itemsWithin {μ : ι → ℕ} {n : ℕ} (h : DecidesOn (within μ n) c L) :
    DecidesOn (Accept.itemsWithin μ n) (fun s => s.all c) (Accept.everyItem L) :=
  DecidesOn.everyItem h

end Checkers

/-! ## Infinite item sequences -/

section Omega

open Cslib

@[simp] theorem mem_everyItemω {s : ωSequence ι} : s ∈ everyItemω L ↔ ∀ k, s k ∈ L := Iff.rfl

/-- An infinite sequence has every item in `L` iff all its finite prefixes do. -/
theorem mem_everyItemω_iff_take {s : ωSequence ι} :
    s ∈ everyItemω L ↔ ∀ n, s.take n ∈ everyItem L :=
  Proofs.Semantics.Accept.Items.mem_everyItemω_iff_take

theorem itemsWithinω_mono {μ : ι → ℕ} {m n : ℕ} (h : m ≤ n) :
    itemsWithinω μ m ⊆ itemsWithinω μ n := fun _ hs k => within_mono h (hs k)

end Omega

end Silmaril.Accept
