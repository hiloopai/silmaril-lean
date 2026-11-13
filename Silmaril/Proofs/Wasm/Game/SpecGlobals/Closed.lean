module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.CompLift
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.InstPhase
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.DetStrat

/-!
# Closed programs under global embeddings and forced prefixes

The closed program of an instance against an environment `K` (`closedD`, `closedInstT`, and
hence `closedSpec`) is the composite of `K`'s transition system with the instance's. Lifting the
simulations of `Machine`, `InstPhase` and `DetStrat` through the fixed environment
(`DivSimulation.compLeft`):

* `closedD_emb`, `closedInstT_emb`: invariance under an injective global embedding of the store
  (threads renamed), every profile;
* `closedInstT_detTo`: a forced instantiation prefix does not change the closed program.

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable (I : ScalarInstance) (P : Profile)

/-- **Closed programs are invariant under global embeddings**, every profile. -/
theorem closedD_emb {ι : Nat → Nat} (hinj : Function.Injective ι) {s t : Store Nat}
    (h : Emb ι Univ s t) (K : Env I.E) : I.closedD P s K = I.closedD P t K := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  exact le_antisymm (DivSimulation.compLeft K.dlts (Strat.fwdSim (I := I) P hκ h)).ofLTS_le
    (DivSimulation.compLeft K.dlts (Strat.bwdSim (I := I) P hκ h)).ofLTS_le

/-- **Closed programs with an instantiation phase are invariant under global embeddings**,
every profile. -/
theorem closedInstT_emb {ι : Nat → Nat} (hinj : Function.Injective ι) {s t : Store Nat}
    (h : Emb ι Univ s t) (t₀ : Thread) (K : Env I.E) :
    I.closedInstT P s t₀ K = I.closedInstT P t (thread ι t₀) K := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  exact le_antisymm
    (DivSimulation.compLeft K.dlts (InstPhase.fwdSim (I := I) (P := P) (t₀ := t₀) h hκ)).ofLTS_le
    (DivSimulation.compLeft K.dlts (InstPhase.bwdSim (I := I) (P := P) (t₀ := t₀) h hκ)).ofLTS_le

/-- **A forced instantiation prefix does not change the closed program**, every profile. -/
theorem closedInstT_detTo {P : Profile} {c d : Config Nat} (hcd : DetTo P c d) (K : Env I.E) :
    I.closedInstT P c.store (configThread c) K = I.closedInstT P d.store (configThread d) K :=
  le_antisymm (DivSimulation.compLeft K.dlts (DetStrat.fwdSim (I := I) hcd)).ofLTS_le
    (DivSimulation.compLeft K.dlts (DetStrat.bwdSim (I := I) hcd)).ofLTS_le

end Silmaril.Proofs.Wasm.Game.SpecGlobals
