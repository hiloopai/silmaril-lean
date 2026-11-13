module

public import Silmaril.Wasm.SpecTec.Institution.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Basic
public import Silmaril.Wasm.Atlas.SpecTec.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Defs

/-!
# The SpecTec specification institution and the Wasm atlas, at wasm-3.0

The models of the SpecTec specification institution (`Silmaril.Wasm.SpecTec.Institution`) are
interpretations of the IL's relations. A model is observed in the Wasm atlas
(`Silmaril.Wasm.Atlas`, `docs/projects/wasm-components.md`) through its `Step` facts:

* `modelChart M`: the behaviour chart whose points are SpecTec values and whose observations at
  `v` are the `w` with `M ⊨ stepFact v w`. At the declarative canonical model
  `canon env (otherwise env)` this is `Atlas.SpecTec.specChart env` (`Thms`).
* `stepModel B`: the backend canonical model of the fixed wasm-3.0 script with primitives `B`,
  `canonB (simEnv B) (otherwiseB (simEnv B))`. Its step facts are `Round6.Reading.SStepB`, the
  reading for which round 6 proved the whole-step simulation (`Round6.Int.wholeStepValidR_backend`).
* `Dom`, `StepDet`, `DomDet`: the domain of that theorem (valid, `BoundedSel`, `BoundedSel`
  Core successors) and its deterministic part, on which the forward half is exact.

`Thms` builds the semi-comorphism: a transition from the Core step chart on `DomDet` to
`modelChart (stepModel B)`, equal on every sentence that respects `CfgRel` (configurations up to
`CALL_REF` annotations).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Wasm30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim

/-- **The step chart of a model**: observations at `v` are the values `w` with `M ⊨ stepFact v w`. -/
def modelChart {S : Sig} (M : Model S) : Chart :=
  BChart Value Unit Value (fun _ => True) (fun v _ => {w | M.D "Step" "%~>%" [] (.tuple [v, w])})

/-- **The backend canonical model** of the fixed wasm-3.0 script with primitives `B`. -/
noncomputable def stepModel (B : Builtins) : Model (sigOf (simEnv B)) :=
  canonB (simEnv B) (Round6.Reading.otherwiseB (simEnv B))

variable {H : Type}

/-- **The domain of the round-6 theorem**: valid, `BoundedSel`, with `BoundedSel` successors. -/
def Dom (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (∃ ts : List CValType, ConfigOk c ts) ∧ Round5.Target.BoundedSel c ∧
    ∀ c₁, Step P host c c₁ → Round5.Target.BoundedSel c₁

/-- Core has at most one successor at `c`. -/
def StepDet (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c₁ c₂, Step P host c c₁ → Step P host c c₂ → c₁ = c₂

/-- **The deterministic part of the domain**. -/
def DomDet (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  Dom P host c ∧ StepDet P host c

end Silmaril.Wasm.SpecTec.Institution.Wasm30
