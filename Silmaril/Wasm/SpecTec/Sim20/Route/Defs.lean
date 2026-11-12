module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Defs
public import Silmaril.Wasm.V2.Execution.Step

/-!
# The 2.0 composite route, as a statement

`docs/projects/spectec/README.md` §1.5: the cheapest whole-step statement for wasm-2.0 programs composes
Track E's embedding `v20own → core|v20` (a forward simulation of `V2.Execution.Step` by
Core 3.0 `Step`) with Round 6's `Round6.Task.wholeStepValidR Round6.Int.backend` (Core 3.0
`Step` against the **wasm-3.0** script under the backend reading). This file states the
composition; nothing here is proved, and Track E's simulation is a hypothesis of the statement
(`TrackEFwd`), since Track E has not landed.

Two caveats are part of the statement, not afterthoughts:

* it relates wasm-2.0 programs to the **3.0** script. The census (`Sim20.Census`) says which
  reduction rules the 2.0 and 3.0 scripts share byte for byte, and only for those does the
  statement say something about the 2.0 script's rules;
* Round 6's forward half lands on a configuration `d'` with `Bwd.ConfigEq c' d'`, not on `c'`
  itself, and is stated one step at a time, on valid (`ConfigOk`), `BoundedSel` configurations
  whose successors are `BoundedSel`. Chaining it along a Core run therefore needs those
  conditions along the run (`RunGood`), determinism along the run (so that Round 6's chosen
  successor is the run's), and a `ConfigEq`-compatibility of SpecTec steps that is not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (HostFinite configV)

/-- **Track E's obligation** for a configuration translation `tr`: every V2 step is a non-empty
sequence of Core 3.0 steps between the translations. -/
def TrackEFwd {H : Type} (P : Profile) (host20 : V2.Execution.HostSemantics H)
    (host : HostSemantics H) (tr : V2.Execution.Config H → Config H) : Prop :=
  ∀ c c', V2.Execution.Step P host20 c c' → Relation.TransGen (Step P host) (tr c) (tr c')

/-- A Core configuration where Round 6 applies and Core is deterministic. -/
def GoodAt {H : Type} (P : Profile) (host : HostSemantics H) (d : Config H) : Prop :=
  (∃ ts, ConfigOk d ts) ∧ Sim.Round5.Target.BoundedSel d ∧
    (∀ d₁, Step P host d d₁ → Sim.Round5.Target.BoundedSel d₁) ∧
    (∀ d₁ d₂, Step P host d d₁ → Step P host d d₂ → d₁ = d₂)

/-- Every configuration reachable from `d` is `GoodAt`. -/
def RunGood {H : Type} (P : Profile) (host : HostSemantics H) (d : Config H) : Prop :=
  ∀ d₁, Relation.ReflTransGen (Step P host) d d₁ → GoodAt P host d₁

/-- **The 2.0 composite route (target, not proved).** Given Track E's forward simulation for a
translation `tr`, there are primitives `B` such that every V2 step from a configuration whose
translation only reaches good configurations is matched, up to `Bwd.ConfigEq`, by a non-empty
sequence of wasm-3.0 SpecTec steps under the backend reading between the encoded
translations. -/
def Task.composite20 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice) (host20 : V2.Execution.HostSemantics H)
        (tr : V2.Execution.Config H → Config H),
        TrackEFwd (Profile.spec nd r) host20 host tr →
        ∃ B : Builtins, ∀ c c' : V2.Execution.Config H,
          V2.Execution.Step (Profile.spec nd r) host20 c c' →
          RunGood (Profile.spec nd r) host (tr c) →
          ∃ d', Sim.Bwd.ConfigEq (tr c') d' ∧
            Relation.TransGen (Sim.Round6.Int.backend.step B) (configV hn (tr c)) (configV hn d')

end Silmaril.Wasm.SpecTec.Sim20
