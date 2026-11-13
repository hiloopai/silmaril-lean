module

public import Silmaril.Wasm.SpecTec.Institution.Wasm20.Defs
public import Silmaril.Wasm.Models.V2Core.Thms

/-!
# The SpecTec specification institution, wasm-2.0 → wasm-3.0: definitions

The wasm-2.0 transitions (`Wasm20.toModelS`, `Wasm20.toModelSE`) relate the V2 step chart to the
step chart of the wasm-2.0 script's model `stepModel20`; the wasm-3.0 semi-comorphism
(`Wasm30.toModel`) relates the Core step chart to the wasm-3.0 script's model `stepModel B`. The
2.0 → Core 3.0 embedding (`Models.V2Core.v20Emb`) is built on the step simulation
`Silmaril.Wasm.V2.Execution.Step.toCore`: one V2 step is matched by **one or more** Core steps,
up to the relation `Silmaril.Wasm.V2.Execution.Sim` (Core configuration normalised to the image
of a well-formed V2 configuration). This header sets up the chain through it.

* `Pair H`: a V2 configuration with a Core configuration; `PairDom P tgt`: the first is in the
  scalar fragment `Wasm20.DomS`, the two are `Sim`-related, and the second is 's
  deterministic domain `Wasm30.DomDet P tgt`.
* `m20Chart`, `v2PChart`: on `PairDom`, the step chart of `stepModel20 (floatIntB P)` at the
  image of the V2 configuration, and the V2 step chart, both read on pairs.
* `Blind`: the value-blind existential sentences, `may` atoms whose predicate holds of every
  value, under `and` and `top` (`progress` and its conjunctions). They are the sentences the
  chain transports: a V2 step is matched by a Core run, whose first step lands at a value that is
  in general not the image of the V2 successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Chain2030

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Institution

variable {H : Type}

/-- A V2 configuration and a Core configuration. -/
abbrev Pair (H : Type) :=
  Silmaril.Wasm.V2.Execution.Config H × Silmaril.Wasm.Execution.Core.Config H

/-- **The domain of the chain**: the V2 configuration is in the scalar fragment, the Core
configuration simulates it, and the Core configuration is in the deterministic part 's
domain. -/
def PairDom (P : Profile) (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (p : Pair H) :
    Prop :=
  Wasm20.DomS p.1 ∧ Silmaril.Wasm.V2.Execution.Sim p.1 p.2 ∧ Wasm30.DomDet P tgt p.2

/-- **The wasm-2.0 model's step chart, on pairs**: observations at `p` are the step facts of
`stepModel20 (floatIntB P)` from the image of the V2 configuration. -/
noncomputable def m20Chart (P : Profile) (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (hn : H → String) : Chart :=
  BChart (Pair H) Unit Value (PairDom P tgt) fun p _ =>
    {w | (Wasm20.stepModel20 (Silmaril.Wasm.SpecTec.Sim.Floats.floatIntB P)).D "Step" "%~>%" []
      (.tuple [Silmaril.Wasm.SpecTec.Sim20.configV hn p.1, w])}

/-- **The V2 step chart, on pairs.** -/
def v2PChart (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) : Chart :=
  BChart (Pair H) Unit Value (PairDom P tgt) fun p u => Wasm20.v2Obs P host hn p.1 u

/-- **Value-blind existential sentences**: every atom is `may _ φ` with `φ` true of every value. -/
def Blind : BSen Unit Value → Prop
  | .always _ _ => False
  | .may _ φ => ∀ b, φ b
  | .and s t => Blind s ∧ Blind t
  | .top => True

end Silmaril.Wasm.SpecTec.Institution.Chain2030
