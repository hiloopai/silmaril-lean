module

public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Game.Adequacy.Thms
import Silmaril.Proofs.Wasm.Game.Instantiate.Basic

/-!
# Instances of modules: theorems

* `IsInstance.ok`: the instance of a module (validated, function imports
  only, no start function, instantiated by `instantiateOnce?`) is well formed
  at its initial store.
* `IsInstance.unique`: a module has at most one instance, so `I.σ P` is *the*
  strategy of the module, for every profile `P`.
* `IsInstance.adequacy_profile` (every profile `P`): M2 for modules: the
  closed-world behaviours of an export call of the instantiated module, under
  the host induced by any environment that throws only existing exceptions,
  are the observations of `K.strategy ≫ I.σ P` together with may-divergence;
  the terminating ones are exactly the answers (`IsInstance.adequacy_answers`).
* `IsInstance.adequacy` (deterministic profiles `profile o`): the behaviours
  are exactly the observations of `K.strategy ≫ I.σ (profile o)`, divergence
  being the absence of an answer.

Instantiation (`instantiateOnce?`) is a function of the module and the base store,
independent of `P`; the profile `P` is the one of the
export calls that follow.

Proofs: `Silmaril.Proofs.Wasm.Game.Instantiate.Basic`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- **Instances of modules are well formed.** -/
theorem IsInstance.ok {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : IsInstance m mt I) : I.Ok :=
  Silmaril.Proofs.Wasm.Game.IsInstance.ok h

/-- A module has at most one instance. -/
theorem IsInstance.unique {m : Module} {mt : CModuleType} {I J : ScalarInstance}
    (hI : IsInstance m mt I) (hJ : IsInstance m mt J) : I = J :=
  Silmaril.Proofs.Wasm.Game.IsInstance.unique hI hJ

/-- **M2 for modules, every profile.** The closed-world behaviours of an export call of the
instantiated module `m` under an arbitrary profile `P` and the host induced by `K` are the
observations of `K.strategy ≫ I.σ P` together with may-divergence. -/
theorem IsInstance.adequacy_profile {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : IsInstance m mt I) (P : Profile) (K : Env I.E)
    (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
      compositeObs (K.strategy.comp (I.σ P)) f ∪
        {b | b = .diverges ∧
          Diverges P (hostOf I.imports K) (invoke I.store (I.addr f.1) f.2.1)} :=
  ScalarInstance.adequacy_profile h.ok K hK f

/-- **M2 for modules, every profile, terminating observations.** -/
theorem IsInstance.adequacy_answers {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : IsInstance m mt I) (P : Profile) (K : Env I.E)
    (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) (b : Behaviour Val)
    (hb : b ≠ .diverges) :
    b ∈ behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 ↔
      b ∈ compositeObs (K.strategy.comp (I.σ P)) f :=
  ScalarInstance.adequacy_answers h.ok K hK f b hb

/-- **M2 for modules, deterministic profiles.** The closed-world behaviours of an export call
of the instantiated module `m` under the host induced by `K` are the observations of
`K.strategy ≫ I.σ (profile o)`. -/
theorem IsInstance.adequacy {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : IsInstance m mt I) (o : GrowOracle) (K : Env I.E)
    (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) :
    behaviours (profile o) (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
      compositeObs (K.strategy.comp (I.σ (profile o))) f :=
  ScalarInstance.adequacy h.ok K hK f

end Silmaril.Wasm.Game
