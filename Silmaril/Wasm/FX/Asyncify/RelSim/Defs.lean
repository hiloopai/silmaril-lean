module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# Relational stuttering simulations of deterministic machines

The asyncify strategies of `Silmaril.Wasm.FX.Asyncify` are compared on the step functions of
`Silmaril.Wasm.Models.FXAsync` (`Res`, `runN`, `beh`). The functional simulation `SimStep` used
there needs a *map* from source to target configurations. Two strategies of this family are
related by relations that are not functions: the shadow-stack strategy keeps dead cells in its
linear memory, and the selective strategy has frames whose missing checks the uninstrumented
code still has. So this module states the relational form:

* `RRes R a b`: both results continue with `R`-related configurations, or both stop with the
  same outcome;
* `RSim R s t`: every step of `s` from `x` is matched by a positive number of steps of `t`
  from every `y` with `R x y` (stuttering on the `t` side only);
* `LockStep R s t`: the special case of exactly one step each.

The results (`Thms`) show that `R`-related configurations have the same behaviours.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.RelSim

open Silmaril.Wasm.Models.FXAsync

variable {C D V : Type}

/-- Related step results: both continue with related configurations, or both stop alike. -/
inductive RRes (R : C → D → Prop) : Res C V → Res D V → Prop where
  | next {c : C} {d : D} (h : R c d) : RRes R (.next c) (.next d)
  | stop (o : Outcome V) : RRes R (.stop o) (.stop o)

/-- **A relational stuttering simulation**: each step of `s` is matched by `n > 0` steps of
`t`. -/
def RSim (R : C → D → Prop) (s : C → Res C V) (t : D → Res D V) : Prop :=
  ∀ x y, R x y → ∃ n, 0 < n ∧ RRes R (s x) (runN t n y)

/-- **A lock-step relation**: related configurations step to related results. -/
def LockStep (R : C → D → Prop) (s : C → Res C V) (t : D → Res D V) : Prop :=
  ∀ x y, R x y → RRes R (s x) (t y)

end Silmaril.Wasm.FX.Asyncify.RelSim
