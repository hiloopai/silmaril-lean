module

public import Silmaril.Wasm.Models.Features.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Data.Bool.Basic

/-!
# Feature sets: the lattice and the version facts

* `FeatureSet` is a distributive lattice with `⊥` and `⊤` (intersections and unions of closed
  sets are closed); `leB_iff`: the order is the Boolean check `leB`, so it is decidable;
* `le_close`, `close_min` (and `close_closed` in `Defs`): `close` is the least closed superset;
* the version facts, by kernel evaluation (`decide`): `v10 ≤ v20 ≤ v30 ≤ wasmFX`,
  `lime1 ≤ v30`, `¬ lime1 ≤ v20` (extended constants arrived in 3.0),
  `functional ≤ functionalMutGC ≤ v30`, `¬ wasmi200 ≤ v30` (wide arithmetic, custom page
  sizes), `micro S ≤ S`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open FeatureSet

theorem closed_sup {S T : Cap → Bool} (hS : Closed S) (hT : Closed T) : Closed (S ⊔ T) := by
  intro c hc d hd
  have hc' : S c = true ∨ T c = true := by simpa [Bool.or_eq_true] using hc
  show (S d || T d) = true
  rcases hc' with h | h
  · simp [hS c h d hd]
  · simp [hT c h d hd]

theorem closed_inf {S T : Cap → Bool} (hS : Closed S) (hT : Closed T) : Closed (S ⊓ T) := by
  intro c hc d hd
  have hc' : S c = true ∧ T c = true := by simpa [Bool.and_eq_true] using hc
  show (S d && T d) = true
  simp [hS c hc'.1 d hd, hT c hc'.2 d hd]

instance : DistribLattice FeatureSet :=
  Subtype.distribLattice (fun _ _ => closed_sup) (fun _ _ => closed_inf)

instance : BoundedOrder FeatureSet where
  top := ⟨fun _ => true, fun _ _ _ _ => rfl⟩
  le_top S c := Bool.le_true (S.1 c)
  bot := ⟨fun _ => false, fun _ h => absurd h Bool.false_ne_true⟩
  bot_le S c := Bool.false_le (S.1 c)

theorem le_iff {S T : FeatureSet} : S ≤ T ↔ ∀ c, S.has c = true → T.has c = true := by
  refine ⟨fun h c hc => ?_, fun h c => ?_⟩
  · have : S.1 c ≤ T.1 c := h c
    exact Bool.eq_true_of_true_le (hc ▸ this)
  · show S.1 c ≤ T.1 c
    cases hS : S.1 c
    · exact Bool.false_le _
    · exact (h c hS).symm ▸ le_refl true

theorem leB_iff {S T : FeatureSet} : S.leB T = true ↔ S ≤ T := by
  rw [le_iff]
  simp only [FeatureSet.leB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨fun h c hc => ?_, fun h c _ => ?_⟩
  · rcases h c (Cap.mem_all c) with h' | h'
    · exact absurd hc (by simp [FeatureSet.has, h'])
    · exact h'
  · cases hS : S.1 c
    · exact Or.inl rfl
    · exact Or.inr (h c hS)

instance : DecidableRel (α := FeatureSet) (· ≤ ·) :=
  fun _ _ => decidable_of_iff _ leB_iff

/-! ## Closure -/

theorem le_close (S : Cap → Bool) (c : Cap) (h : S c = true) : close S c = true := by
  simp [close, h]

theorem close_min {S T : Cap → Bool} (hST : ∀ c, S c = true → T c = true) (hT : Closed T)
    (c : Cap) (h : close S c = true) : T c = true := by
  have h' : S c = true ∨ ∃ d ∈ Cap.all, S d = true ∧ c ∈ Cap.pre d := by
    simpa [close, List.any_eq_true, List.contains_iff_mem] using h
  rcases h' with h' | ⟨d, -, hd, hcd⟩
  · exact hST c h'
  · exact hT d (hST d hd) c hcd

/-- A prerequisite of a capability of a feature set is in it. -/
theorem has_pre {S : FeatureSet} {c d : Cap} (h : S.has c = true) (hd : d ∈ Cap.pre c) :
    S.has d = true :=
  S.2 c h d hd

theorem has_of_le {S T : FeatureSet} (h : S ≤ T) {c : Cap} (hc : S.has c = true) :
    T.has c = true :=
  le_iff.mp h c hc

theorem remove_le (S : FeatureSet) (c : Cap) : S.remove c ≤ S :=
  le_iff.mpr fun d hd => by
    simp only [FeatureSet.has, FeatureSet.remove, Bool.and_eq_true] at hd
    exact hd.1

theorem not_has_remove (S : FeatureSet) (c : Cap) : (S.remove c).has c = false := by
  simp [FeatureSet.has, FeatureSet.remove]

theorem micro_le (S : FeatureSet) : micro S ≤ S := remove_le S _

theorem micro_no_float (S : FeatureSet) : (micro S).has .floatNum = false :=
  not_has_remove S _

/-! ## Version facts -/

theorem v10_le_v20 : v10 ≤ v20 := leB_iff.mp (by decide)
theorem v20_le_v30 : v20 ≤ v30 := leB_iff.mp (by decide)
theorem v30_le_wasmFX : v30 ≤ wasmFX := leB_iff.mp (by decide)
theorem lime1_le_v30 : lime1 ≤ v30 := leB_iff.mp (by decide)
/-- Lime1 is not a 2.0 profile: extended constant expressions arrived in 3.0. -/
theorem lime1_not_le_v20 : ¬ lime1 ≤ v20 := fun h => absurd (leB_iff.mpr h) (by decide)
theorem functional_le_functionalMutGC : functional ≤ functionalMutGC := leB_iff.mp (by decide)
theorem functionalMutGC_le_v30 : functionalMutGC ≤ v30 := leB_iff.mp (by decide)
/-- wasmi 2.0.0 is not a 3.0 profile: wide arithmetic and custom page sizes are not 3.0. -/
theorem wasmi200_not_le_v30 : ¬ wasmi200 ≤ v30 := fun h => absurd (leB_iff.mpr h) (by decide)
theorem v20_le_wasmi200 : v20 ≤ wasmi200 := leB_iff.mp (by decide)
theorem v10_lt_v20 : v10 < v20 :=
  lt_of_le_not_ge v10_le_v20 fun h => absurd (leB_iff.mpr h) (by decide)

end Silmaril.Wasm.Models
