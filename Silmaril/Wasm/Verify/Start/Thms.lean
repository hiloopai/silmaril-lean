module

public import Silmaril.Wasm.Verify.Start.Defs
public import Silmaril.Proofs.Wasm.Verify.Start.Plays

@[expose] public section

/-!
# Reachability with an instantiation phase: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Start.Plays`. Under `StartIn I s t₀ G fs i`, every profile `P`:

* `step_sInv`: every transition of `(I.instSysT P s t₀).toLTS` keeps `SInv` and never asks
  import `i`; `run_no_icall`: no run does;
* **`instStrategyT_no_icall`**: no play of `I.instStrategyT P s t₀` asks import `i`; with
  `s = c₀.store`, `t₀ = configThread c₀` this is `I.specStrategy P c₀`, the strategy with the
  specification's instantiation phase (`Silmaril.Wasm.Game.SpecInst`);
* **`inst_closed_world`**, **`export_closed_world`**: every Core run of the instantiation
  configuration against every environment, and every Core run of an export call from a store
  it leaves, never reaches a callout of `i`.

The verifier's side (`Silmaril.Wasm.Verify.Check.Thms`): `check_start_sound`, `checkSpec_sound`.
-/
