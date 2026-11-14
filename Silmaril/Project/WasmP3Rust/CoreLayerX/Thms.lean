module

public import Silmaril.Project.WasmP3Rust.CoreLayerX.Defs

/-!
# The re-entrant `realloc`: the step bound does not matter

PROVED (standard axioms), namespace `Silmaril.Project.WasmP3Rust.CoreLayerX`.

* `runTo_succ`, `runTo_mono`: a run that returned within `n` steps returns the same within
  more (the interpreter is deterministic).
* `allocFuel_mono`; **`allocExact_of_fuel`**: whenever `realloc` returns within some step bound
  (`allocFuel`, what `tools/cli-core-trace` runs), the faithful `allocExact` (and so `coreKsX`)
  gives the same store and pointer.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.CoreLayerX

open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.CoreLayer
open Silmaril.Wasm.SingleThreaded (Thread)

/-- One more step of fuel does not change a returned run. -/
theorem runTo_succ : ∀ {n : Nat} {s : St} {t : Thread} {r : St × Nat},
    runTo s t n = some r → runTo s t (n + 1) = some r
  | 0, _, _, _, h => absurd h (by simp [runTo])
  | n + 1, s, t, r, h => by
    unfold runTo at h ⊢
    split at h
    · exact h
    · split at h
      · exact runTo_succ h
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **More fuel does not change a returned run.** -/
theorem runTo_mono {n m : Nat} {s : St} {t : Thread} {r : St × Nat} (h : runTo s t n = some r)
    (hnm : n ≤ m) : runTo s t m = some r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => exact h
  | succ k ih => exact runTo_succ (ih (Nat.le_add_right _ _))

/-- More fuel does not change a returned `realloc`. -/
theorem allocFuel_mono {L : Layer} {ra n m : Nat} {x : Conf} {size align : Nat}
    {r : Conf × Nat} (h : allocFuel L ra n x size align = some r) (hnm : n ≤ m) :
    allocFuel L ra m x size align = some r := by
  unfold allocFuel at h ⊢
  split at h
  · next a _ =>
    obtain ⟨vs, hvs, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    rw [hvs, Option.bind_some, runTo_mono hr' hnm]; rfl
  · exact absurd h (by simp)

/-- **The faithful `realloc` agrees with every step bound under which it returns.** -/
theorem allocExact_of_fuel {L : Layer} {ra n : Nat} {x : Conf} {size align : Nat}
    {r : Conf × Nat} (h : allocFuel L ra n x size align = some r) :
    allocExact L ra x size align = some r := by
  have hex : ∃ n, (allocFuel L ra n x size align).isSome := ⟨n, by simp [h]⟩
  have hmin : Nat.find hex ≤ n := Nat.find_min' hex (by simp [h])
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  have hrr : r' = r := Option.some.inj ((allocFuel_mono hr' hmin).symm.trans h)
  unfold allocExact
  rw [dite_eq_left_of_eq_true (eq_true hex), hr', hrr]

end Silmaril.Project.WasmP3Rust.CoreLayerX

end
