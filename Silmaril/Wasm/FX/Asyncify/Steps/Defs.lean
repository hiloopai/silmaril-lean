module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# Step counts of asyncify strategies and optimizations

The correctness theorems of the asyncify family compare behaviours (results, traps,
divergence), not speed. This module states the comparison of speed used by the results
(`Thms`): a machine is **never slower** than another from a pair of configurations when every
run of the second that stops within `m` steps is matched by a run of the first that stops within
`m` steps, with the same outcome.

* `NoSlower s t x y`: `s` from `x` is never slower than `t` from `y`;
* `SameSteps s t x y`: both directions: the two runs stop after the same numbers of steps.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Steps

open Silmaril.Wasm.Models.FXAsync

variable {C D V : Type}

/-- **`s` from `x` is never slower than `t` from `y`.** -/
def NoSlower (s : C → Res C V) (t : D → Res D V) (x : C) (y : D) : Prop :=
  ∀ m o, runN t m y = .stop o → runN s m x = .stop o

/-- The two runs stop within the same numbers of steps, alike. -/
def SameSteps (s : C → Res C V) (t : D → Res D V) (x : C) (y : D) : Prop :=
  NoSlower s t x y ∧ NoSlower t s y x

end Silmaril.Wasm.FX.Asyncify.Steps
