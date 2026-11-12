module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxQuant.Typ4

/-!
# Round 7, REH route 2: values of a checked type conform (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant`; see `docs/projects/spectec/README.md`. Definitions are in `Round7/NxQuant/Defs.lean`.

* `typVtItems_fixed` (kernel, ten slices) and `aliasFuelOk_sigX`: the type side conditions hold
  on the fixed script and on `sigX`.
* `vtB_of_HasTyp`: by induction on `Sem.hasTyp`'s fuel, a value of type `t` conforms to
  `toAT t` under `sigX`, at every type, in a scope whose type variables are export-free, in an
  environment whose types pass `typVt` and whose export-free types are export-free.
* `vtB_of_HasTyp_utf8Env`, `vtB_of_quantsOk`: the same in `utf8Env B`; so the rule quantifiers
  of `Step` (typed at runtime by `Sim.QuantsOk`) hold conforming values at the ten types that may
  hold a module record as well. This generalises round 6's `NxSites.nxB_of_quantsOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.vtB_of_quantsOk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms vtB_of_quantsOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.typVtItems_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms typVtItems_fixed

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
