module

public import Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.Beh
public import Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.List

/-!
# Relational stuttering simulations: results

The header of `Defs`.

* **`beh_eq_of_rsim`**: if `RSim R s t` (every step of `s` is matched by a positive number of
  steps of `t` from every related configuration), then `R`-related configurations have the same
  behaviours under `s` and `t`: returned values, trap and divergence.
* `beh_eq_of_lock`: the same for a lock-step relation.
* `runN_one`, `runN_two`: one and two steps of a run; `beh_of_stop`: a run that stops has one
  behaviour.
* `forall₂_getElem?`, `forall₂_set`, `forall₂_append_one`, `forall₂_reverse`: `List.Forall₂`
  facts for heaps and buffers.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.RelSim

open Silmaril.Wasm.Models.FXAsync

variable {C D V : Type}

/-- **Equal behaviours under a relational stuttering simulation.** -/
theorem beh_eq_of_rsim {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (hsim : RSim R s t) {x : C} {y : D} (hxy : R x y) : beh s x = beh t y :=
  Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.beh_eq_of_rsim hsim hxy

/-- **Equal behaviours under a lock-step relation.** -/
theorem beh_eq_of_lock {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (h : LockStep R s t) {x : C} {y : D} (hxy : R x y) : beh s x = beh t y :=
  beh_eq_of_rsim (Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.rsim_of_lock h) hxy

/-- One step of a run. -/
theorem runN_one (step : C → Res C V) (c : C) : runN step 1 c = step c := by
  simp only [runN]
  cases step c <;> rfl

/-- Two steps of a run, the first continuing. -/
theorem runN_two {step : C → Res C V} {c c' : C} (h : step c = .next c') :
    runN step 2 c = step c' := by
  rw [Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.runN_succ_next h, runN_one]

/-- A run that stops has exactly one behaviour. -/
theorem beh_of_stop {step : C → Res C V} {n : Nat} {c : C} {o : Outcome V}
    (h : runN step n c = .stop o) : beh step c = {o.toObs} :=
  Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.beh_of_stop h

section Lists

variable {α β : Type} {S : α → β → Prop}

theorem forall₂_getElem? {l : List α} {l' : List β} (h : List.Forall₂ S l l') (k : Nat) :
    Option.Rel S l[k]? l'[k]? :=
  Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.forall₂_getElem? h k

theorem forall₂_set {l : List α} {l' : List β} (h : List.Forall₂ S l l') {a : α} {b : β}
    (hab : S a b) (k : Nat) : List.Forall₂ S (l.set k a) (l'.set k b) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.forall₂_set h hab k

theorem forall₂_append_one {l : List α} {l' : List β} (h : List.Forall₂ S l l') {a : α} {b : β}
    (hab : S a b) : List.Forall₂ S (l ++ [a]) (l' ++ [b]) :=
  Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.forall₂_append_one h hab

theorem forall₂_reverse {l : List α} {l' : List β} (h : List.Forall₂ S l l') :
    List.Forall₂ S l.reverse l'.reverse :=
  Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.forall₂_reverse h

end Lists

end Silmaril.Wasm.FX.Asyncify.RelSim
