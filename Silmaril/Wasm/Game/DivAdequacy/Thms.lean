module

public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Games.DivLTSComp.Thms
import Silmaril.Proofs.Wasm.Game.DivAdequacy.Main
import Silmaril.Proofs.Wasm.Game.DivAdequacy.Comp

/-!
# Adequacy with divergence-observing strategies (M2, divergence included)

For an **arbitrary** profile `P`:

* `ScalarInstance.forget_dstrategy`, `ScalarInstance.forget_closedD`: the
  divergence-observing strategies extend the plain ones: the finite plays of
  `I.dstrategy P s` are `I.strategy P s`, those of the closed program
  `I.closedD P s K` are `K.strategy ≫ I.strategy P s`.
* `ScalarInstance.mem_div_closedD_iff`: the closed program may diverge right
  after the export question `f` exactly when the Core invocation of `f`
  diverges under the induced host (an infinite host-free run, a host call
  that `K` never answers, or infinitely many answered import calls, on *some*
  branch).
* `ScalarInstance.adequacy_div`: hence the closed-world behaviours of an
  export call are **exactly** the observations `dcompositeObs` of the closed
  program, terminating behaviours and divergence alike, with no hypothesis on
  the profile. This is the game-level reading of may-divergence that the
  plain strategies cannot give under nondeterminism
  (`Silmaril.Wasm.Game.Adequacy`); for `profile o` it agrees with `adequacy`
  (`dcompositeObs_profile`).
* `IsInstance.adequacy_div`: the same for modules at their initial store.

**Compositional divergence.** `ScalarInstance.closedD_eq_comp`: the closed
program is the composite `K.dstrategy.comp (I.dstrategy P s)` of the
divergence-observing strategies of the environment and of the instance
(`Silmaril.Games.DivComp`), by `DStrategy.ofLTS_comp`: both systems denote their
strategies and take silent steps only while running. Hence
`ScalarInstance.adequacy_div_comp`: Core behaviours, divergence included, are
read off the composite of the components' strategies, divergence created by
infinitely many answered import calls being the hidden chatter of
`DStrategy.comp`.

Not shown: a divergence-observing version of M3 (linking).

Proofs: `Silmaril.Proofs.Wasm.Game.DivAdequacy.*` (new).
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

namespace Env

/-- The divergence-observing environment denotes the environment's strategy. -/
theorem denotes_dlts {E : Sig.{0}} (K : Env E) : K.dlts.Denotes K.strategy :=
  Silmaril.Proofs.Wasm.Game.Env.denotes_dlts K

/-- The finite plays of the divergence-observing environment are its strategy. -/
theorem forget_dstrategy {E : Sig.{0}} (K : Env E) : K.dstrategy.forget = K.strategy :=
  (denotes_dlts K).ofLTS_eq

end Env

namespace ScalarInstance

variable {I : ScalarInstance}

/-- The system with silent host-free steps denotes the strategy of the instance. -/
theorem denotes_dlts (P : Profile) (s : Store Nat) : (I.dlts P s).Denotes (I.strategy P s) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.denotes_dlts P s

/-- The finite plays of the divergence-observing strategy of an instance are its strategy. -/
theorem forget_dstrategy (P : Profile) (s : Store Nat) :
    (I.dstrategy P s).forget = I.strategy P s :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.forget_dstrategy P s

/-- The finite plays of the divergence-observing closed program are those of the closed
program `K.strategy ≫ I.strategy P s`. -/
theorem forget_closedD (P : Profile) (s : Store Nat) (K : Env I.E) :
    (I.closedD P s K).forget = I.closedWith P s K :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.forget_closedD P s K

/-- **Divergence of the closed program is Core divergence** (every profile). -/
theorem mem_div_closedD_iff {P : Profile} {s : Store Nat} {K : Env I.E} (f : I.F.Op) :
    [.inr (.ask f)] ∈ (I.closedD P s K).div ↔
      Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_div_closedD_iff f

/-- **M2 with divergence-observing strategies, every profile.** For a strategy-definable host
whose environment throws only existing exceptions, the closed-world behaviours of an export
call under an arbitrary profile `P` are exactly the observations of the divergence-observing
closed program: the behaviours of its answers, and `diverges` when it may diverge after the
question. -/
theorem adequacy_div {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      dcompositeObs (I.closedD P s K) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_div hw K hK f

/-- In the deterministic profiles the divergence-observing observations are the plain ones. -/
theorem dcompositeObs_profile {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (K : Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    dcompositeObs (I.closedD (profile o) s K) f = compositeObs (I.closedWith (profile o) s K) f :=
  (adequacy_div hw K hK f).symm.trans (adequacy hw K hK f)

/-- **The closed program is the composite of the components' divergence-observing
strategies** (every profile). -/
theorem closedD_eq_comp (P : Profile) (s : Store Nat) (K : Env I.E) :
    I.closedD P s K = K.dstrategy.comp (I.dstrategy P s) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.closedD_eq_comp P s K

/-- **M2 with compositional divergence, every profile.** The closed-world behaviours of an
export call, divergence included, are the observations of the composite
`K.dstrategy.comp (I.dstrategy P s)` of the divergence-observing strategies. -/
theorem adequacy_div_comp {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      dcompositeObs (K.dstrategy.comp (I.dstrategy P s)) f := by
  rw [← closedD_eq_comp]
  exact adequacy_div hw K hK f

end ScalarInstance

/-- **M2 for modules with divergence-observing strategies, every profile.** -/
theorem IsInstance.adequacy_div {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : IsInstance m mt I) (P : Profile) (K : Env I.E)
    (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
      dcompositeObs (I.closedD P I.store K) f :=
  ScalarInstance.adequacy_div h.ok K hK f

end Silmaril.Wasm.Game
