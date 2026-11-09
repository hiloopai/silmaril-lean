module

public import Silmaril.X86.SegVC

/-!
# Machine extensions

`I.Extends J` says that the machine `J` (states `τ`) **extends** the machine `I` (states
`σ`): every step of `I` is a step of `J`. It is the one mechanism by which runs and function
contracts move up the x86 machine tower (`docs/x86.md`): `Open.isa` to `Open9.isa`, and
later `Open9.isa` to the machines with string, SSE or atomic forms.

A `J` state has an `I` state as its **view** (`view`), which `put` replaces; the rest of the
`J` state (for instance a vector register file) is a frame that `I` steps do not touch.
`view` and `put` form a lawful lens. The core and memory of a `J` state are those of its
view, `J`'s update of core and memory updates the view, and a live `J` state has a live view.
When `σ = τ` the lens is the identity (`Extends.ofStep`).

The generic transfers are in `Extends/Thms.lean` (`Extends.run`, `Extends.reaches`,
`Extends.trans`) and `FnContract/Thms.lean` (`FnContract.Spec.Total.lift`,
`FnContract.lift`). Extensions point upward only: there is no transfer from `J` to `I`.
-/

@[expose] public section

namespace Silmaril.X86.SegVC

open Silmaril.X86 (State)
open Silmaril.Process (Memory)

/-- **`J` extends `I`**: along the lens `view`/`put`, every `I` step of the view is a `J`
step that changes only the view. -/
structure Isa.Extends {σ τ : Type} (I : Isa σ) (J : Isa τ) where
  /-- The `I` state inside a `J` state. -/
  view : τ → σ
  /-- Replace the `I` state inside a `J` state, keeping the rest. -/
  put : τ → σ → τ
  view_put : ∀ x s, view (put x s) = s
  put_put : ∀ x s s', put (put x s) s' = put x s'
  put_view : ∀ x, put x (view x) = x
  /-- Core and memory are those of the view. -/
  core : ∀ x, J.core x = I.core (view x)
  mem : ∀ x, J.mem x = I.mem (view x)
  /-- Updating core and memory updates the view. -/
  upd : ∀ x c m, J.upd x c m = put x (I.upd (view x) c m)
  /-- A live state has a live view. -/
  live : ∀ x, J.live x → I.live (view x)
  /-- **Every `I` step of the view is a `J` step.** -/
  step : ∀ {x s}, I.step (view x) = some s → J.step x = some (put x s)

namespace Isa.Extends

variable {σ τ υ : Type} {I : Isa σ} {J : Isa τ} {K : Isa υ}

/-- An extension on the same states: same core, memory, update; every `I` step is a `J`
step. -/
@[reducible] def ofStep {I J : Isa σ} (core : ∀ s, J.core s = I.core s)
    (mem : ∀ s, J.mem s = I.mem s) (upd : ∀ s c m, J.upd s c m = I.upd s c m)
    (live : ∀ s, J.live s → I.live s)
    (step : ∀ {s t}, I.step s = some t → J.step s = some t) : I.Extends J where
  view := id
  put _ s := s
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core := core
  mem := mem
  upd := upd
  live := live
  step := step

/-- Every machine extends itself. -/
@[reducible] def refl (I : Isa σ) : I.Extends I :=
  ofStep (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) id

end Isa.Extends

end Silmaril.X86.SegVC
