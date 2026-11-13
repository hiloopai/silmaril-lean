module

public import Silmaril.Proofs.Wasm.Logic.OpenTotal.Stub

/-!
# Open Wasm modules with total correctness: the divergence-aware game link

For an open module `M` with import stubs bound by `bind`
(`Silmaril.Wasm.Logic.Open.Defs`) and its divergence-observing strategy
`dmodStrat P M bind` (`Silmaril.Wasm.Logic.OpenTotal.Defs`):

* `dmodStrat_sound`: `TModuleSat P M bind Γi Γe → dmodStrat P M bind ≤
  dagStrat (ctxSpec Γi) (ctxSpec Γe)`: finite plays are assume/guarantee
  correct, the module diverges only after a play in which Opponent broke the
  specifications (`dmodStrat_div`), and its infinite plays are plays;
* `tgood_not_diverges`, `diverges_of_silent`: a silent infinite run of the
  module is an infinite closed-world run, which total correctness
  (`Hoare.TSafe.not_diverges`) excludes.

* `dlink_refines` (`Silmaril.Proofs.Wasm.Logic.OpenTotal.Link`): linked totally
  correct modules, `(dmodStrat M₁).comp (dmodStrat M₂) ≤ dagStrat (ctxSpec Γi)
  (ctxSpec Γe)` (`Silmaril.Games.DStrategy.comp`, which also observes divergence
  from infinite hidden interaction), **given** that the upper module is
  `Productive`; `opp_zip` (good Opponent moves reach both components),
  `no_chatter`, `dlink_div`;
* `dmodStrat_productive` (`Silmaril.Proofs.Wasm.Logic.OpenTotal.Productive`):
  totally correct modules are productive (an infinite play with good Opponent
  moves has infinitely many upper moves: within one question, the module's
  calls and their answers would be an infinite closed-world run under
  `specHostT`); hence **`dlink_refines_total`**: `TModuleSat P M₁ bind₁ Γi Γm →
  TModuleSat P M₂ bind₂ Γm Γe → (dmodStrat P M₁ bind₁).comp (dmodStrat P M₂ bind₂)
  ≤ dagStrat (ctxSpec Γi) (ctxSpec Γe)`.

Proofs are total-correctness versions of those of `Silmaril.Wasm.Logic.Open.Thms`.

A Silmaril addition.
-/
