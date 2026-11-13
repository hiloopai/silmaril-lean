module

public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Defs
public import Silmaril.Wasm.Atlas.SpecTec.Defs

/-!
# The wasm-3.0 semi-comorphism off the deterministic domain: definitions

`Wasm30.toModel` relates Core's step chart to the step chart of the backend canonical model
`stepModel B` on `DomDet`, where Core has at most one successor. Off `DomDet` the round-6 theorem
is exact backwards and only "up to Core's choice" forwards: every Core step is matched by a step
fact of `stepModel B` to the image of *some* Core successor. So `stepModel B` is a **resolution**
of Core's nondeterminism: its successor set at `c` is a nonempty-when-Core's-is subset of
Core's, up to `CfgRel`. This header names that situation and the fragments on which it is enough
for a two-sided statement.

* `Halves B hn P host`: the two halves  at primitives `B`, on `Dom`, read in
  `stepModel B`. Both `Wasm30.builtins` (by choice) and the concrete `Round4Int.BI` satisfy it
  (`Nondet.Thms`).
* `Indep S s`: **choice independence**. Every atom of the behaviour sentence `s` takes one truth
  value on the whole observation set `S c` of its call. At `S := coreObs … c`: the sentence
  cannot tell Core's successors of `c` apart.
* `DomUpTo K P host hn c`: `Dom`, and Core's successors of `c` are pairwise `K`-related (as
  SpecTec values). `K := Eq` contains `DomDet`; `K := ⊤` is all of `Dom`.
* `Admissible`, `unionObs`, `unionChart`: the set-valued model, the union of the step facts of
  every `stepModel B` with `Halves B`.
* `Task.choiceCover`: frozen, **open**: every Core successor on `Dom` is a step fact of some
  admissible `stepModel B`. Under it the union chart is equal to Core on `Dom` (`Nondet.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Nondet

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30

variable {H : Type}

/-- `w` is a step fact of `stepModel B` from `v`. -/
def MStep (B : Builtins) (v w : Value) : Prop :=
  (stepModel B).D "Step" "%~>%" [] (.tuple [v, w])

/-- **The two halves  at primitives `B`**, on `Dom`, read in `stepModel B`: forward up
to Core's choice of successor, backward up to `ConfigEq`. -/
structure Halves (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- Forward, up to Core's choice. -/
  fwd : ∀ c, Dom P host c → ∀ c', Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ MStep B (configV hn c) (configV hn d')
  /-- Backward, up to `ConfigEq`. -/
  bwd : ∀ c, Dom P host c → ∀ w, MStep B (configV hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c'

/-- **Choice independence**: every atom of `s` has one truth value on the observation set of its
call. -/
def Indep {C B : Type} (S : C → Set B) : BSen C B → Prop
  | .always c φ => ∀ b ∈ S c, ∀ b' ∈ S c, (φ b ↔ φ b')
  | .may c φ => ∀ b ∈ S c, ∀ b' ∈ S c, (φ b ↔ φ b')
  | .and s t => Indep S s ∧ Indep S t
  | .top => True

/-- **Determinism up to `K`**: `Dom`, and Core's successors are pairwise `K`-related. -/
def DomUpTo (K : Value → Value → Prop) (P : Profile) (host : HostSemantics H) (hn : H → String)
    (c : Config H) : Prop :=
  Dom P host c ∧ ∀ c₁ c₂, Step P host c c₁ → Step P host c c₂ → K (configV hn c₁) (configV hn c₂)

/-- The primitives whose backend canonical model satisfies both halves. -/
def Admissible (hn : H → String) (P : Profile) (host : HostSemantics H) : Set Builtins :=
  {B | Halves B hn P host}

/-- **The set-valued model**: the step facts of every admissible `stepModel B`. -/
def unionObs (hn : H → String) (P : Profile) (host : HostSemantics H) (v : Value) (_ : Unit) :
    Set Value :=
  {w | ∃ B ∈ Admissible hn P host, MStep B v w}

/-- The step chart of the set-valued model. -/
def unionChart (hn : H → String) (P : Profile) (host : HostSemantics H) : Chart :=
  BChart Value Unit Value (fun _ => True) (unionObs hn P host)

/-- **Choice cover** (frozen, open): on round 6's domain at `Profile.spec nd r`, every Core
successor is, up to `ConfigEq`, a step fact of the backend canonical model at some admissible
primitives. -/
def Task.choiceCover : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → ∀ (nd : Bool) (r : RelaxedChoice),
      ∀ c, Dom (Profile.spec nd r) host c → ∀ c', Step (Profile.spec nd r) host c c' →
        ∃ B ∈ Admissible hn (Profile.spec nd r) host,
          ∃ d', Bwd.ConfigEq c' d' ∧ MStep B (configV hn c) (configV hn d')

end Silmaril.Wasm.SpecTec.Institution.Nondet
