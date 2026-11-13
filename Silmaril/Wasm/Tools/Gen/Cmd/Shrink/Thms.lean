module

public import Silmaril.Wasm.Tools.Gen.Cmd.Shrink.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms

/-!
# `wasm-tools shrink`: specification

For a decidable interestingness predicate `P`:

* `shrink_sat`: if the input is interesting, so is the output;
* `shrink_validIn`: if the input is valid in `S`, so is the output;
* `shrink_size_le`: the output is no larger (`msize`);
* `shrink_fixed`: the output is a local minimum: no candidate of it is interesting.

These are the API's laws (`Silmaril.Wasm.Tools.Gen.API.Thms`: `shrink_pred`, `shrink_inv`,
`shrink_size_le`, `shrink_step_none`) at `shrinker S seed`. `wasm-tools shrink` runs the same
loop with the predicate script in `IO` (`Shrinker.shrinkM`, equal to `shrink` in `Id` with fuel
above the size: `shrinkM_id`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Shrink

open Silmaril.Wasm Silmaril.Wasm.Models

theorem shrinker_cands (S : FeatureSet) (seed : Nat) :
    (shrinker S seed).cands = candidates S seed := rfl

variable {S : FeatureSet} {seed : Nat} {P : Module → Bool} {m : Module}

theorem shrink_sat (h : P m = true) : P (shrink S seed P m) = true :=
  (shrinker S seed).shrink_pred P h

theorem shrink_validIn (h : ValidIn S m) : ValidIn S (shrink S seed P m) :=
  (shrinker S seed).shrink_inv P (ValidIn S)
    (fun _ _ _ hc _ => (Core.featCheck_iff S _).mp (candidates_spec hc).2) m h

theorem shrink_size_le : msize (shrink S seed P m) ≤ msize m :=
  (shrinker S seed).shrink_size_le P m

theorem shrink_fixed : (shrinker S seed).step P (shrink S seed P m) = none :=
  (shrinker S seed).shrink_step_none P m

end Silmaril.Wasm.Tools.Gen.Cmd.Shrink
