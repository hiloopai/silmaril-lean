module

public import Silmaril.Wasm.Models.FXV.Defs
public import Silmaril.Wasm.Resource.Handle.Defs

/-!
# Continuations as resources: the continuation store as a handle protocol (definitions)

The WasmFX semantics (`StepFX`, `Silmaril.Wasm.Models.FX`, and the corrected `StepFX'` with
continuation values, `Silmaril.Wasm.Models.FXV`) keeps continuations in a **continuation store**
`K : List (Option ContFX)`: `cont.new` and `suspend` append a continuation, `resume` and
`resume_throw` consume one (the entry becomes `none`), `cont.bind` and `switch` consume one and
append another. Consumed entries are never filled again, and a `resume`/`cont.bind` of a consumed
continuation traps (`resumeUsed`, `contBindUsed`).

This module reads those store changes as events of the handle protocols of
`Silmaril.Wasm.Resource.Handle` (`HEv ℕ`): appending at index `K.length` is `alloc K.length`,
consuming `k` is `free k`.

* `KStore`: continuation stores.
* `KStep K K' evs`: the four shapes of a store change of one step, with their handle events
  (`same`, `alloc`, `consume`, `swap`); `KSteps`: their concatenation.
* `KRel L K`: the protocol state `L` (live handles) lists exactly the live (unconsumed) indices
  of `K`, without duplicates.
* `budget K k`: how many more times index `k` may still be consumed: `1` if `k` is live or not yet
  allocated, `0` once consumed.

Theorems (`Silmaril.Wasm.Component.FXRes.Thms`): every `StepFX` and `StepFX'` step changes the
store by a `KStep`; the handle protocol accepts every run's history in both orientations
(fresh allocation, consumption only of live continuations); a consumed continuation stays
consumed; **every continuation is consumed at most once** along any run.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm.Models.FX Silmaril.Wasm.Resource

/-- Continuation stores. -/
abbrev KStore := List (Option ContFX)

/-- **How one step changes the continuation store**, with its handle events. -/
inductive KStep : KStore → KStore → List (HEv ℕ) → Prop where
  /-- No change. -/
  | same (K : KStore) : KStep K K []
  /-- A new continuation at index `K.length` (`cont.new`, `suspend`). -/
  | alloc (K : KStore) (C : ContFX) : KStep K (K ++ [some C]) [.alloc K.length]
  /-- A live continuation `k` is consumed (`resume`, `resume_throw`). -/
  | consume {K : KStore} {k : ℕ} {C : ContFX} (hk : K[k]? = some (some C)) :
      KStep K (K.set k none) [.free k]
  /-- A live continuation `k` is consumed and a new one appended (`cont.bind`, `switch`). -/
  | swap {K : KStore} {k : ℕ} {C : ContFX} (C' : ContFX) (hk : K[k]? = some (some C)) :
      KStep K (K.set k none ++ [some C']) [.free k, .alloc K.length]

/-- Sequences of store changes, with the concatenation of their events. -/
inductive KSteps : KStore → KStore → List (HEv ℕ) → Prop where
  | refl (K : KStore) : KSteps K K []
  | cons {K₁ K₂ K₃ : KStore} {e₁ e₂ : List (HEv ℕ)} (h : KStep K₁ K₂ e₁) (t : KSteps K₂ K₃ e₂) :
      KSteps K₁ K₃ (e₁ ++ e₂)

/-- The protocol state `L` lists exactly the live indices of `K`, without duplicates. -/
def KRel (L : List ℕ) (K : KStore) : Prop :=
  L.Nodup ∧ ∀ i, i ∈ L ↔ ∃ C, K[i]? = some (some C)

/-- Index `k` is consumed. -/
def Consumed (K : KStore) (k : ℕ) : Prop := K[k]? = some none

/-- How many more times index `k` may be consumed: `0` once consumed, `1` otherwise. -/
def budget (K : KStore) (k : ℕ) : ℕ :=
  match K[k]? with
  | some none => 0
  | _ => 1

end Silmaril.Wasm.Component.FXRes
