module

public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Defs

/-!
# The step charts: Core and SpecTec

Step-level charts. A point's single "call" (`Unit`) is one reduction step; its observations
are the SpecTec values of its successors.

* `SpecTec.coreChart P host hn D`: Core configurations, observed through the SpecTec encoding
  `Sim.configV hn` of their `Step P host` successors. Domain: an arbitrary fragment `D` of
  configurations (e.g. Core-valid configurations, the fragment a satisfiable round-4 target
  will be stated on).
* `SpecTec.specChart env`: SpecTec values, observed through the successors of the imported
  SpecTec relation `Sim.SStep env` (`Step: config ~> config` of the wasm-3.0 script).
* `SpecTec.CfgRel hn`: two values are related when they encode configurations equal up to
  `CALL_REF` annotations (`Sim.Bwd.ConfigEq`).
* `SpecTec.FwdOn`/`SpecTec.BwdOn`: the forward and backward conjuncts of the SpecTec ↔ Core
  simulation, on the fragment `D`. They are **hypotheses** here: round 3 refuted the frozen
  targets (`Round3.not_wholeStepBounded`) and no satisfiable restatement is frozen yet
  (`docs/projects/spectec/README.md`, "Round 3 status").
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTec

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec

/-- The SpecTec values of a configuration's Core successors. -/
def coreObs (P : Profile) {H : Type} (host : HostSemantics H) (hn : H → String) (c : Config H)
    (_ : Unit) : Set Value :=
  {w | ∃ c', Step P host c c' ∧ w = Sim.configV hn c'}

/-- **The Core step chart** on the fragment `D`. -/
def coreChart (P : Profile) {H : Type} (host : HostSemantics H) (hn : H → String)
    (D : Config H → Prop) : Chart :=
  BChart (Config H) Unit Value D (coreObs P host hn)

/-- **The SpecTec step chart.** -/
def specChart (env : Env) : Chart :=
  BChart Value Unit Value (fun _ => True) (fun v _ => {w | Sim.SStep env v w})

/-- Values encoding configurations equal up to `CALL_REF` annotations. -/
def CfgRel {H : Type} (hn : H → String) (w w' : Value) : Prop :=
  ∃ c d : Config H, Sim.Bwd.ConfigEq c d ∧ w = Sim.configV hn c ∧ w' = Sim.configV hn d

/-- The forward conjunct on `D`: every Core step is matched by a SpecTec step up to
`ConfigEq`. -/
def FwdOn (env : Env) (P : Profile) {H : Type} (host : HostSemantics H) (hn : H → String)
    (D : Config H → Prop) : Prop :=
  ∀ c, D c → ∀ c', Step P host c c' →
    ∃ d', Sim.Bwd.ConfigEq c' d' ∧ Sim.SStep env (Sim.configV hn c) (Sim.configV hn d')

/-- The backward conjunct on `D`: every SpecTec step is matched by a Core step up to
`ConfigEq`. -/
def BwdOn (env : Env) (P : Profile) {H : Type} (host : HostSemantics H) (hn : H → String)
    (D : Config H → Prop) : Prop :=
  ∀ c, D c → ∀ w, Sim.SStep env (Sim.configV hn c) w →
    ∃ c' d', Sim.Bwd.ConfigEq c' d' ∧ w = Sim.configV hn d' ∧ Step P host c c'

end Silmaril.Wasm.Atlas.SpecTec
