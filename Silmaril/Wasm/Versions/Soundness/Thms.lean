module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness

/-!
# Wasm versions: the copied 2.0 type-soundness proof

The public header of the copy `Silmaril/Raw/Wasm/Versions/V2/Soundness{,/*}.lean`
(an earlier development, `Silmaril/Wasm/V2/Soundness{,/*}.lean`; provenance in
`Silmaril.Wasm.Versions.Thms` so that importers of the simulations do not load it.

* `StoreOk`, `Extend`, `ConfigOk`, `HostOk`: store typing, store extension, configuration
  typing and the host contract. SpecTec 2.0 has no soundness file, so these are rebuilt from
  the W3C 2.0 appendix and Core 3.0's `7.1-soundness`;
* `Step.preservation`, `Config.progress`, `Steps.safe`: preservation, progress and type safety
  at every profile;
* `invoke_ok`, `invoke_safe`: `$invoke` of a typed call;
* `Instantiate.ok`, `Instantiate.safe`, `Module.safe`: `$instantiate` of a valid module against
  typed imports;
* `vcvtop_badShape_stuck`, `cvtop_badOp_stuck`: the literal SpecTec 2.0 rules (without the
  definedness premises silmaril adds) admit typed stuck configurations.

Model statements: `Silmaril.Wasm.Models.V2Sound.Thms`.
-/
