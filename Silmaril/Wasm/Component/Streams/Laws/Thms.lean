module

public import Silmaril.Wasm.Component.Streams.Spec.Thms

/-!
# Pipeline laws of stream transformers

The transformers of `Silmaril.Wasm.Component.Streams.Spec` under sequential composition `⟫` and
observational equivalence `≈ₜ` (the same output so far after every finite input and the same
whole output at its end):

**Equivalence and congruence.** `Equiv.refl`, `Equiv.symm`, `Equiv.trans`, and
**`comp_congr`**: composing equivalent transformers gives equivalent composites. This is the
stream instance of "the composition of equivalent components is equivalent"; it holds because
both observations of a composite are functions of the parts' observations (`runP_comp`,
`run_comp`).

**Category laws.** `comp_assoc`, `id_comp`, `comp_id`.

**Fusion and commutation laws.**

* `map_map`: `map f ⟫ map g ≈ₜ map (g ∘ f)` (map fusion);
* `filter_filter`: `filter p ⟫ filter q ≈ₜ filter (p && q)`;
* `map_filter`: `map f ⟫ filter p ≈ₜ filter (p ∘ f) ⟫ map f` (filter moves before a map);
* `map_filterMap`, `filterMap_map`: fusion into `filterMap`;
* `map_take`: `map f ⟫ take n ≈ₜ take n ⟫ map f` (take after map);
* `take_take`: `take m ⟫ take n ≈ₜ take (min m n)`;
* `tee_chan`: either output of `tee` followed by any `T` is `T`.

**Where commutation fails.** `not_filter_take`: `filter p ⟫ take n` and `take n ⟫ filter p` are
not equivalent in general (a concrete counterexample).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Tr

variable {σ σ' τ τ' ρ α β γ δ : Type}

/-! ## Equivalence -/

theorem Equiv.refl (T : Tr σ α β) : T ≈ₜ T := fun _ => ⟨rfl, rfl⟩

theorem Equiv.symm {T : Tr σ α β} {U : Tr τ α β} (h : T ≈ₜ U) : U ≈ₜ T :=
  fun xs => ⟨(h xs).1.symm, (h xs).2.symm⟩

theorem Equiv.trans {T : Tr σ α β} {U : Tr τ α β} {V : Tr ρ α β} (h₁ : T ≈ₜ U) (h₂ : U ≈ₜ V) :
    T ≈ₜ V := fun xs => ⟨(h₁ xs).1.trans (h₂ xs).1, (h₁ xs).2.trans (h₂ xs).2⟩

theorem Equiv.equivF {T : Tr σ α β} {U : Tr τ α β} (h : T ≈ₜ U) : T.EquivF U :=
  fun xs => (h xs).2

/-- **Congruence**: composing equivalent transformers gives equivalent composites. -/
theorem comp_congr {T : Tr σ α β} {T' : Tr σ' α β} {U : Tr τ β γ} {U' : Tr τ' β γ}
    (hT : T ≈ₜ T') (hU : U ≈ₜ U') : (T ⟫ U) ≈ₜ (T' ⟫ U') := by
  intro xs
  refine ⟨?_, ?_⟩
  · rw [runP_comp', runP_comp', (hT xs).1, (hU _).1]
  · rw [run_comp', run_comp', (hT xs).2, (hU _).2]

/-- Congruence for the whole outputs. -/
theorem comp_congrF {T : Tr σ α β} {T' : Tr σ' α β} {U : Tr τ β γ} {U' : Tr τ' β γ}
    (hT : T.EquivF T') (hU : U.EquivF U') : (T ⟫ U).EquivF (T' ⟫ U') := by
  intro xs
  rw [run_comp', run_comp', hT xs, hU _]

/-! ## Category laws -/

theorem comp_assoc (T : Tr σ α β) (U : Tr τ β γ) (V : Tr ρ γ δ) :
    ((T ⟫ U) ⟫ V) ≈ₜ (T ⟫ (U ⟫ V)) := fun xs =>
  ⟨by simp only [runP_comp'], by simp only [run_comp']⟩

theorem id_comp (T : Tr σ α β) : ((Tr.id : Tr Unit α α) ⟫ T) ≈ₜ T := fun xs =>
  ⟨by rw [runP_comp', runP_id], by rw [run_comp', run_id]⟩

theorem comp_id (T : Tr σ α β) : (T ⟫ (Tr.id : Tr Unit β β)) ≈ₜ T := fun xs =>
  ⟨by rw [runP_comp', runP_id], by rw [run_comp', run_id]⟩

/-! ## Fusion and commutation -/

theorem map_map (f : α → β) (g : β → γ) : (map f ⟫ map g) ≈ₜ map (g ∘ f) := fun xs =>
  ⟨by rw [runP_comp', runP_map, runP_map, runP_map, List.map_map],
   by rw [run_comp', run_map, run_map, run_map, List.map_map]⟩

theorem filter_filter (p q : α → Bool) :
    (filter p ⟫ filter q) ≈ₜ filter (fun x => p x && q x) := fun xs =>
  ⟨by rw [runP_comp', runP_filter, runP_filter, runP_filter, List.filter_filter, Bool.and_comm'],
   by rw [run_comp', run_filter, run_filter, run_filter, List.filter_filter, Bool.and_comm']⟩
where
  Bool.and_comm' : (fun x => q x && p x) = (fun x => p x && q x) := by
    funext x
    exact Bool.and_comm _ _

theorem map_filter (f : α → β) (p : β → Bool) :
    (map f ⟫ filter p) ≈ₜ (filter (p ∘ f) ⟫ map f) := fun xs =>
  ⟨by rw [runP_comp', runP_comp', runP_map, runP_filter, runP_filter, runP_map, List.filter_map],
   by rw [run_comp', run_comp', run_map, run_filter, run_filter, run_map, List.filter_map]⟩

theorem map_filterMap (f : α → β) (g : β → Option γ) :
    (map f ⟫ filterMap g) ≈ₜ filterMap (g ∘ f) := fun xs =>
  ⟨by rw [runP_comp', runP_map, runP_filterMap, runP_filterMap, List.filterMap_map],
   by rw [run_comp', run_map, run_filterMap, run_filterMap, List.filterMap_map]⟩

theorem filterMap_map (f : α → Option β) (g : β → γ) :
    (filterMap f ⟫ map g) ≈ₜ filterMap (fun x => (f x).map g) := fun xs =>
  ⟨by rw [runP_comp', runP_map, runP_filterMap, runP_filterMap, List.map_filterMap],
   by rw [run_comp', run_map, run_filterMap, run_filterMap, List.map_filterMap]⟩

/-- **Take after map.** -/
theorem map_take (f : α → β) (n : Nat) :
    (map f ⟫ (take n : Tr Nat β β)) ≈ₜ ((take n : Tr Nat α α) ⟫ map f) := fun xs =>
  ⟨by rw [runP_comp', runP_comp', runP_map, runP_take, runP_take, runP_map, List.map_take],
   by rw [run_comp', run_comp', run_map, run_take, run_take, run_map, List.map_take]⟩

theorem take_take (m n : Nat) :
    ((take m : Tr Nat α α) ⟫ (take n : Tr Nat α α)) ≈ₜ (take (min m n) : Tr Nat α α) :=
  fun xs =>
  ⟨by rw [runP_comp', runP_take, runP_take, runP_take, List.take_take, Nat.min_comm],
   by rw [run_comp', run_take, run_take, run_take, List.take_take, Nat.min_comm]⟩

/-- Either output of `tee` followed by `T` is `T`. -/
theorem tee_chan (b : Bool) (T : Tr σ α β) (xs : List α) :
    T.run (chan b ((tee : Tr Unit α (Bool × α)).run xs)) = T.run xs := by
  rw [chan_run_tee]

/-- **Filter and take do not commute**: with `p = (· ≠ 0)` and `n = 1`, on `[0, 1]` the first
gives `[1]` and the second `[]`. -/
theorem not_filter_take :
    ¬ ((filter (fun x : Nat => x != 0) ⟫ (take 1 : Tr Nat Nat Nat)) ≈ₜ
        ((take 1 : Tr Nat Nat Nat) ⟫ filter (fun x : Nat => x != 0))) := by
  intro h
  have h2 := (h [0, 1]).2
  rw [run_comp', run_comp', run_filter, run_take, run_take, run_filter] at h2
  exact absurd h2 (by decide)

end Silmaril.Wasm.Component.Streams.Tr
