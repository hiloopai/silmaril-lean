module

public import Silmaril.Wasm.Component.Engine.Sim.Defs
import Silmaril.Proofs.Wasm.Component.EngineSim

/-!
# Engines that differ only in their store: what a simulation carries

For `S : E.StoreSim I` (a store map `φ` from `E.withStore I` to `E` commuting with every store
operation, `Engine.Sim.Defs`), with `S.map c = (φ c.1, c.2)`:

* `StoreSim.steps`: every run of `E.withStore I` maps to a run of `E`; `StoreSim.steps_lift`:
  every run of `E` from a mapped configuration is the image of a run of `E.withStore I`;
* `StoreSim.diverges_iff`: a configuration diverges iff its image does;
* `StoreSim.extends_iff`: store extension (`CoreEngine.Extends`) is reflected and preserved;
* `StoreSim.lawful`: if `E` is lawful (`CoreEngine.Lawful`), so is `E.withStore I`;
* `ExecSim.runCore`: the fuel loops of commuting steppers commute with `S.map`, with the same
  stop flag.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

namespace CoreEngine

namespace StoreSim

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I)

theorem internal_map {H : Type} {c c' : (E.withStore I).Config H}
    (h : (E.withStore I).Internal c c') : E.Internal (S.map c) (S.map c') :=
  Silmaril.Proofs.Wasm.Component.EngineSim.internal S h

theorem internal_lift_map {H : Type} {c : (E.withStore I).Config H} {d : E.Config H}
    (h : E.Internal (S.map c) d) : ∃ c', (E.withStore I).Internal c c' ∧ d = S.map c' :=
  Silmaril.Proofs.Wasm.Component.EngineSim.internal_lift S h

/-- **Runs map to runs.** -/
theorem steps {H : Type} {c c' : (E.withStore I).Config H} (h : (E.withStore I).Steps c c') :
    E.Steps (S.map c) (S.map c') :=
  Silmaril.Proofs.Wasm.Component.EngineSim.steps S h

/-- **Runs from a mapped configuration are images of runs.** -/
theorem steps_lift {H : Type} {c : (E.withStore I).Config H} {d : E.Config H}
    (h : E.Steps (S.map c) d) : ∃ c', (E.withStore I).Steps c c' ∧ d = S.map c' :=
  Silmaril.Proofs.Wasm.Component.EngineSim.steps_lift S h

theorem diverges_iff {H : Type} {c : (E.withStore I).Config H} :
    (E.withStore I).Diverges c ↔ E.Diverges (S.map c) :=
  Silmaril.Proofs.Wasm.Component.EngineSim.diverges_iff S

theorem extends_iff {H : Type} {s s' : I.Store H} :
    (E.withStore I).Extends s s' ↔ E.Extends (S.φ s) (S.φ s') :=
  Silmaril.Proofs.Wasm.Component.EngineSim.extends_iff S

/-- **The engine laws carry over.** -/
theorem lawful (S : E.StoreSim I) [E.Lawful] : (E.withStore I).Lawful :=
  Silmaril.Proofs.Wasm.Component.EngineSim.lawful S

end StoreSim

/-- **Fuel loops commute with the simulation.** -/
theorem ExecSim.runCore {E : CoreEngine} {I : E.StoreImpl} {S : E.StoreSim I} {X : E.Exec}
    {X' : (E.withStore I).Exec} (hX : ExecSim S X X') {H : Type} (n : Nat)
    (c : (E.withStore I).Config H) :
    X.runCore n (S.map c) = Prod.map S.map id (X'.runCore n c) :=
  Silmaril.Proofs.Wasm.Component.EngineSim.runCore S hX n c

end CoreEngine

end Silmaril.Wasm.Component.Engine
