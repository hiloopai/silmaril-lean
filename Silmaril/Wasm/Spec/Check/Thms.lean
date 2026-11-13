module

public import Silmaril.Wasm.Spec.Check.Defs
public import Silmaril.Proofs.Wasm.Spec.Check.GameLink
public import Silmaril.Proofs.Wasm.Spec.Check.Inc

@[expose] public section

/-!
# Verification conditions for the simple Wasm specifications: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Check.{GameLink,Inc}`. Every profile `P`.

* `ag_moves_good`, `opp_good`: with an unconstrained Opponent side, an assume/guarantee correct
  play has only allowed Proponent moves.
* `gameSat_icall`, `gameSat_ret`: from `GameSat P p.inst Inv Ii Ie` (one Hoare triple per export
  in the every-run logic of `Silmaril.Wasm.Logic`, under the most general environment meeting
  `Ii`) and `Inv p.store`, when every export question and import answer is allowed, every import
  call of every trace satisfies `Ii.pre` and every export return satisfies `Ie.post`
  (`Silmaril.Wasm.Logic.GameLink.strategy_sound`).
* **Soundness of the verification conditions**: `callPre_of_gameSat`, `neverCall_of_gameSat`,
  `assertNeverFalse_of_gameSat`, `retPost_of_gameSat` (with the guards `importGuard`,
  `exportGuard`).
* Litmus on real Core 3.0 code (the increment function `local.get 0; i32.const 1; i32.add`):
  `incProvider_neverCall` (it never calls an import) and `incProvider_retPost` (every return is a
  single `i32`), from `Silmaril.Wasm.Logic.GameLink.Examples.incProvider_sat`.
-/
