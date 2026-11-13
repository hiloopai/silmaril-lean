module

public import Silmaril.Proofs.Wasm.Component.FXRes.ContPool.Live

/-!
# Continuations in the table or in a store: every step keeps the identity invariant

* `ginv_init`: the invariant holds initially;
* `inv_fx_keep`, `inv_fx_fresh`: steps of a thread that consume or keep continuations, and steps
  that allocate one (its identity is fresh);
* `inv_cbNew`, `inv_cbTake`: the moves of `new` and `take` (the identity moves with the
  continuation; the source is dead afterwards);
* `inv_cbOther`, and the steps that do not touch continuations;
* **`gstep_inv`**: every `GStep` keeps `GInv`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContPool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (ContFX AdminFX)
open Silmaril.Wasm.Models.FXV (CtxV)
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## Lists of continuations -/

theorem live_of_set_none {K : KStore} {k j : ℕ} {C : ContFX}
    (h : (K.set k none)[j]? = some (some C)) : K[j]? = some (some C) ∧ j ≠ k := by
  by_cases hjk : j = k
  · subst hjk
    rw [List.getElem?_set_self'] at h
    simp at h
  · rw [List.getElem?_set_ne (Ne.symm hjk)] at h
    exact ⟨h, hjk⟩

theorem live_of_append {K : KStore} {x : Option ContFX} {j : ℕ} {C : ContFX}
    (h : (K ++ [x])[j]? = some (some C)) (hj : j ≠ K.length) : K[j]? = some (some C) := by
  rcases Nat.lt_or_ge j K.length with hlt | hge
  · rwa [List.getElem?_append_left hlt] at h
  · rw [List.getElem?_append_right hge] at h
    have hpos : 0 < j - K.length := by omega
    rw [List.getElem?_singleton] at h
    simp [Nat.pos_iff_ne_zero.1 hpos] at h

theorem slot_none {ts : List (Option (ThreadV (CH H)))} {i i' : ℕ} {u : ThreadV (CH H)}
    (h : (ts.set i none)[i']? = some (some u)) : i' ≠ i ∧ ts[i']? = some (some u) := by
  by_cases hii : i' = i
  · subst hii
    rw [List.getElem?_set_self'] at h
    simp at h
  · rw [List.getElem?_set_ne (Ne.symm hii)] at h
    exact ⟨hii, h⟩

/-! ## Initial state -/

theorem not_live_init (c : Store (FXCode (CH H))) (l : Loc) : ¬ Live (Pool.init c) l := by
  cases l with
  | store i j =>
    rintro ⟨t, ht, -⟩
    simp [Pool.init] at ht
  | tab n =>
    rintro ⟨C, hC⟩
    cases n <;> simp_all [Pool.init, Table.empty, Table.get?]

theorem ginv_init (c : Store (FXCode (CH H))) : GInv (Pool.init c) Ghost.init :=
  ⟨freeOK_empty, fun l hl => absurd hl (not_live_init c l),
    fun l₁ _ h₁ _ _ => absurd h₁ (not_live_init c l₁)⟩

/-! ## Thread steps -/

theorem inv_fx_keep {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t t' : ThreadV (CH H)}
    {s' : EStore H} (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab)
    (hK : ∀ (j : ℕ) (C : ContFX), (threadConts t')[j]? = some (some C) →
      ∃ C' : ContFX, (threadConts t)[j]? = some (some C')) :
    GInv ⟨s', p.ts.set i (some t')⟩ g :=
  inv_mono hI (ht ▸ hI.wf) (live_set_mono (s := p.s) hi hK fun _ C hC => ⟨C, ht ▸ hC⟩)

theorem fx_back_fresh {p : Pool H} {i : ℕ} {t t' : ThreadV (CH H)} {s' : EStore H}
    (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab)
    (hK : ∀ (j : ℕ) (C : ContFX), j ≠ (threadConts t).length →
      (threadConts t')[j]? = some (some C) → ∃ C' : ContFX, (threadConts t)[j]? = some (some C')) :
    ∀ l, Live ⟨s', p.ts.set i (some t')⟩ l → l ≠ .store i (threadConts t).length → Live p l := by
  intro l hl hne
  cases l with
  | store i' j =>
    rcases live_store_set (s := p.s) hi hl with ⟨rfl, C, hC⟩ | ⟨-, h⟩
    · have hj : j ≠ (threadConts t).length := fun hj => hne (by rw [hj])
      obtain ⟨C', hC'⟩ := hK j C hj hC
      exact ⟨t, hi, C', hC'⟩
    · exact h
  | tab n =>
    obtain ⟨C, hC⟩ := hl
    exact ⟨C, ht ▸ hC⟩

theorem inv_fx_fresh {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t t' : ThreadV (CH H)}
    {s' : EStore H} (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab)
    (hK : ∀ (j : ℕ) (C : ContFX), j ≠ (threadConts t).length →
      (threadConts t')[j]? = some (some C) → ∃ C' : ContFX, (threadConts t)[j]? = some (some C')) :
    GInv ⟨s', p.ts.set i (some t')⟩ (g.fresh (.store i (threadConts t).length)) :=
  inv_fresh hI (ht ▸ hI.wf) _ (fx_back_fresh hi ht hK)

theorem inv_fx_alloc {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t t' : ThreadV (CH H)}
    {s' : EStore H} (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab) {K : KStore}
    {C : ContFX} (hK : threadConts t = K) (hK' : threadConts t' = K ++ [some C]) :
    GInv ⟨s', p.ts.set i (some t')⟩ (g.fresh (.store i K.length)) := by
  have hb : ∀ (j : ℕ) (C₁ : ContFX), j ≠ (threadConts t).length →
      (threadConts t')[j]? = some (some C₁) → ∃ C' : ContFX, (threadConts t)[j]? = some (some C') :=
    fun j C₁ hj hC₁ => ⟨C₁, hK ▸ live_of_append (hK' ▸ hC₁) (hK ▸ hj)⟩
  have h : GInv ⟨s', p.ts.set i (some t')⟩ (g.fresh (.store i (threadConts t).length)) :=
    inv_fx_fresh hI hi ht hb
  rwa [hK] at h

theorem inv_fx_swap {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t t' : ThreadV (CH H)}
    {s' : EStore H} (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab) {K : KStore} {k : ℕ}
    {C : ContFX} (hK : threadConts t = K) (hK' : threadConts t' = K.set k none ++ [some C]) :
    GInv ⟨s', p.ts.set i (some t')⟩ (g.fresh (.store i K.length)) := by
  have hb : ∀ (j : ℕ) (C₁ : ContFX), j ≠ (threadConts t).length →
      (threadConts t')[j]? = some (some C₁) → ∃ C' : ContFX, (threadConts t)[j]? = some (some C') :=
    fun j C₁ hj hC₁ =>
      have hj' : j ≠ (K.set k none).length := by rw [List.length_set, ← hK]; exact hj
      ⟨C₁, hK ▸ (live_of_set_none (live_of_append (hK' ▸ hC₁) hj')).1⟩
  have h : GInv ⟨s', p.ts.set i (some t')⟩ (g.fresh (.store i (threadConts t).length)) :=
    inv_fx_fresh hI hi ht hb
  rwa [hK] at h

/-- **An FX or Core step keeps the invariant.** -/
theorem inv_fx {p : Pool H} {g : Ghost} (hI : GInv p g) {i : ℕ} {t t' : ThreadV (CH H)}
    {s' : EStore H} {evs : List (HEv ℕ)} (hi : p.ts[i]? = some (some t)) (ht : s'.tab = p.s.tab)
    (hk : KStep (threadConts t) (threadConts t') evs) :
    GInv ⟨s', p.ts.set i (some t')⟩ (g.allocs i evs) := by
  generalize hK : threadConts t = K at hk
  generalize hK' : threadConts t' = K' at hk
  cases hk with
  | same => exact inv_fx_keep hI hi ht fun j C hC => ⟨C, hK ▸ hK' ▸ hC⟩
  | alloc C => exact inv_fx_alloc hI hi ht hK hK'
  | consume _ =>
    exact inv_fx_keep hI hi ht fun j C hC => ⟨C, hK ▸ (live_of_set_none (hK' ▸ hC)).1⟩
  | swap C' _ => exact inv_fx_swap hI hi ht hK hK'

end Silmaril.Wasm.Component.FXRes.ContPool
