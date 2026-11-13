module

public import Silmaril.Wasm.Atlas.Core.Defs
public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Wasm.Game.Env.Defs

/-!
# The game charts

* `Games.chart P I`: the game semantics of a scalar instance `I` (`Silmaril.Wasm.Game`). Points
  are a store and an environment `K` (a strategy-definable host); calls are the export calls of
  `I`'s interface signature; the observations of a call are `compositeObs` of the closed program
  `K.strategy ≫ I.strategy P s` (answers, and `diverges` for no answer). Domain: well-formed
  stores and environments throwing only existing exceptions (M2's hypotheses).
* `Games.call I`: the signature morphism from `I`'s export calls into Core calls,
  `f ↦ (I.addr f.1, args)`; `Games.corePt I`: `(s, K) ↦ (s, hostOf I.imports K)`.
* `Games.linkChart P S`: the composite of the strategies of the provider and consumer of a
  static-linking setup (`Silmaril.Wasm.Game.Linking`), against an environment of the empty
  interface. Its observations are `compositeObs (K.strategy ≫ (σ_provider ≫ σ_consumer))`.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Games

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game

/-- Game points of `I`: a store and an environment. -/
abbrev Pt (I : ScalarInstance) : Type := Store Nat × Env I.E

/-- M2's domain: a well-formed store and an environment throwing only existing exceptions. -/
def Dom (I : ScalarInstance) (x : Pt I) : Prop :=
  I.WellFormed x.1 ∧ ThrowsBelow x.2 x.1.exns.length

/-- The observations of an export call: those of the closed program. -/
noncomputable def obs (P : Profile) (I : ScalarInstance) (x : Pt I) (f : I.F.Op) : Set (Behaviour Val) :=
  compositeObs (I.closedWith P x.1 x.2) f

/-- **The game chart** of `I` at profile `P`. -/
noncomputable def chart (P : Profile) (I : ScalarInstance) : Chart :=
  BChart (Pt I) I.F.Op (Behaviour Val) (Dom I) (obs P I)

/-- The signature morphism into Core calls. -/
def call (I : ScalarInstance) (f : I.F.Op) : Core.Call := (I.addr f.1, f.2.1)

/-- The point map into Core. -/
def corePt (I : ScalarInstance) (x : Pt I) : Core.Pt Nat := (x.1, hostOf I.imports x.2)

/-- The divergence that Core may add to a game observation (may-divergence). -/
def extraDiv (P : Profile) (I : ScalarInstance) (x : Pt I) (f : I.F.Op) : Set (Behaviour Val) :=
  {b | b = .diverges ∧ Diverges P (hostOf I.imports x.2) (invoke x.1 (I.addr f.1) f.2.1)}

/-- The observations of the composite of a linking setup's parts. -/
noncomputable def linkObs (P : Profile) (S : Linking.Setup) (K : Env (ifaceSig []))
    (f : (ifaceSig S.exportTypes).Op) : Set (Behaviour Val) :=
  compositeObs (K.strategy.comp ((S.providerI.σ P).comp (S.consumerI.σ P))) f

/-- **The linking chart**: the composite of the parts' strategies. Domain: the scalar fragment
of the setup (`S.Scalar`), so the chart is empty unless the setup is in M3's fragment. -/
noncomputable def linkChart (P : Profile) (S : Linking.Setup) : Chart :=
  BChart (Env (ifaceSig [])) (ifaceSig S.exportTypes).Op (Behaviour Val) (fun _ => S.Scalar)
    (linkObs P S)

/-- The empty host of a closed linked program. -/
def emptyHost : HostSemantics Nat := fun _ _ _ _ => False

end Silmaril.Wasm.Atlas.Games
