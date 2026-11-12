module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Host

/-!
# SpecTec ↔ Core 3.0, round 7: the encoder lemma for `ExpFree`

Ingredient 1 of what `Round7.Task.envAgreeNE` still needs (`docs/projects/spectec/README.md`):

* `expFree_configV : Round5.Pos.NoExports c → TypAgree.ExpFree (configV hn c)`: the image of
  an export-free configuration has no non-empty `EXPORTS` field, so
  `Round7.TypAgree.hasTyp_config_iff` applies to it.

It is proved through a boolean check (`efB`, sound by `expFree_of_efB`) and a sweep over every
encoder `configV` uses: the type encoders (`Encode.toValue` at the source types, `tyV`), the
instruction encoders (`Equiv.instrV`, `Vec.vecInstrV?`, `schemaInstrV`, `instrToV`), the value
encoders and the runtime records. Only `moduleInstToValue` has an `EXPORTS` field.

The `$hostcall` case of determination (`docs/projects/spectec/README.md`) is also proved
here:

* `hostcall_storeNE`: an export-blind host (`Round7.HostExportBlind`) called in an export-free
  store has only outcomes with export-free stores;
* `efB_hostcallCall`: so round 4's `$hostcall` primitive, at arguments that pass `efB`, answers
  a value that passes `efB` (with the converse `storeNE_of_efB` of the store encoder lemma).

Still open for `Task.envAgreeNE`: determination (every quantifier value of a derivation from an
`ExpFree` configuration is `ExpFree`) and the `otherwise` transfer.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.expFree_configV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expFree_configV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.expFree_of_efB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expFree_of_efB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.efB_hostcallCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms efB_hostcallCall

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
