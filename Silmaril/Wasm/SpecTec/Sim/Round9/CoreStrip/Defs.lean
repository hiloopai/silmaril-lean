module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 9: the Core side of `Round7.Task.wholeStepValidRE` without `StripInj`

`Round7.Task.wholeStepValidRE` (RE) and its host-blind form `Round7.Task.wholeStepValidREH` (REH)
are open. Every proved route so far (`Round7.HostMods.stepValidREM_holds`) needs two things on the
Core side:

* `StripInj c`: two module instances of `c` with the same stripped form are equal. It is what
  makes `unstrip c` an inverse of stripping, so that the exports of the successor can be read
  back from the stripped successor.
* `HostExportBlind host`: the host relation commutes with stripping at *every* store, so that
  round 6 can be run at the stripped configuration with the *same* host.

This header states the replacements.

* **The host at the stripped side is built from the configuration.** `stripHostAt host s₀` is
  `host` everywhere except at the stripped store `stripStore s₀` (when `s₀` is typed). There it
  answers the outcomes of `host` at `s₀`, stripped. It is finite and `HostOk` whenever `host`
  is (`Round9.CoreStrip.stripHostAt_finite`, `stripHostAt_ok`), so round 6 applies to it with no
  hypothesis on export names. For an export-blind host it *is* `host`
  (`stripHostAt_of_blind`). So `HostExportBlind` is not needed on the Core side; on the SpecTec
  side it only identifies the builtins `BI P hn (stripHostAt host c.store)` with
  `BI P hn host`.
* **Exports are tracked up to `ExRel`, not inverted.** `HostRelAt host₁ host₂ s₁ s₂` relates the
  outcomes of two hosts at two stores up to export lists. `ExRel` is then a simulation between
  `Step P host₁` and `Step P host₂` (`Round9.CoreStrip.exRel_step₂`), with no injectivity.

What is left is stated as explicit leaves, all at one configuration `c`:

* `EraseFwdAt`, `EraseBwdAt` (SpecTec side): a step of the round-7 reading at `configV hn c`
  and a step of the round-6 reading at `configV hn (stripConfig c)`, with the stripped host's
  builtins, correspond along `Swap.eraseV`.
* `ExactAt` (the export lists): a SpecTec successor that agrees up to export lists with a Core
  successor is the image of a `Bwd.ConfigEq` witness of a Core successor.

`StepValidREX` is RE with "up to `Bwd.ConfigEq`" weakened to "up to export lists". It is proved
from the two SpecTec leaves (`Round9.CoreStrip.stepValidREX_of_leaves`), and RE follows from all
three (`wholeStepValidRE_of_leaves`); REH from the same leaves at export-blind hosts.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7 (stripStore stripOutcome stripConfig ExRel BoundedSelE backendE)
open Round4Int (BI)

variable {H : Type}

/-! ## Hosts compared at one store -/

/-- **Two hosts agree at two stores up to export lists**: every outcome of `host₁` at `s₁` has an
outcome of `host₂` at `s₂` with the same stripped form. -/
def HostRelAt (host₁ host₂ : HostSemantics H) (s₁ s₂ : Store H) : Prop :=
  ∀ (h : H) (vs : List Val) (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
    host₁ h s₁ vs o → ∃ o', host₂ h s₂ vs o' ∧ stripOutcome o = stripOutcome o'

/-- **A host returns only export-free stores at `s`.** -/
def HostStrippedAt (host : HostSemantics H) (s : Store H) : Prop :=
  ∀ (h : H) (vs : List Val) (s' : Store H) (r : Result),
    host h s vs (.returned s' r) → stripStore s' = s'

/-- **The host seen from the stripped side of `s₀`.** At `stripStore s₀`, for a typed `s₀`, it
answers the outcomes of `host` at `s₀` with their exports removed; everywhere else it is
`host`. -/
def stripHostAt (host : HostSemantics H) (s₀ : Store H) : HostSemantics H := fun h s vs o =>
  (s = stripStore s₀ ∧ StoreOk s₀ ∧ ∃ o₀, host h s₀ vs o₀ ∧ o = stripOutcome o₀) ∨
    (¬ (s = stripStore s₀ ∧ StoreOk s₀) ∧ host h s vs o)

/-! ## The SpecTec-side leaves at one configuration -/

section Leaves

variable (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H)

/-- **SpecTec leaf, forward along erasure.** A step of the round-7 reading from `configV hn c`
goes, erased, to a step of the round-6 reading from the stripped image, with the builtins of the
stripped host. -/
def EraseFwdAt : Prop :=
  ∀ w, backendE.step (BI P hn host) (configV hn c) w →
    Round6.Int.backend.step (BI P hn (stripHostAt host c.store)) (configV hn (stripConfig c))
      (Round7.Swap.eraseV w)

/-- **SpecTec leaf, backward along erasure.** A step of the round-6 reading from the stripped
image, with the builtins of the stripped host, is the erasure of a step of the round-7 reading
from `configV hn c`. -/
def EraseBwdAt : Prop :=
  ∀ w₀, Round6.Int.backend.step (BI P hn (stripHostAt host c.store))
      (configV hn (stripConfig c)) w₀ →
    ∃ w, backendE.step (BI P hn host) (configV hn c) w ∧ Round7.Swap.eraseV w = w₀

/-- **A Core successor and a SpecTec successor agree up to export lists**: the stripped Core
successor is a `Bwd.ConfigEq` witness of a configuration whose image is the erased SpecTec
successor. -/
def ExAgree (c₁ : Config H) (w : Value) : Prop :=
  ∃ d₀, Bwd.ConfigEq (stripConfig c₁) d₀ ∧ Round7.Swap.eraseV w = configV hn d₀

/-- **Leaf, exact export lists.** A SpecTec successor `w` that agrees up to export lists with a
Core successor is the image of a `Bwd.ConfigEq` witness of a Core successor. One leaf serves both
halves: forward, the Core successor it returns is the only one when there is only one. -/
def ExactAt : Prop :=
  ∀ c₁ w, Step P host c c₁ → backendE.step (BI P hn host) (configV hn c) w → ExAgree hn c₁ w →
    ∃ c₂ d', Bwd.ConfigEq c₂ d' ∧ w = configV hn d' ∧ Step P host c c₂

end Leaves

/-! ## The target up to export lists, and the leaves as hypotheses -/

/-- **`Round7.Task.wholeStepValidRE` up to export lists**, with the two SpecTec leaves as
hypotheses at each configuration of the domain. Proved (`Round9.CoreStrip.stepValidREX_of_leaves`).
No host hypothesis beyond `HostFinite` and `HostOk`, and no `StripInj`. -/
def StepValidREX : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice),
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c →
          EraseBwdAt hn (Profile.spec nd r) host c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ w, backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w ∧
              ExAgree hn c'' w) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedSelE c →
          EraseFwdAt hn (Profile.spec nd r) host c →
          backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w →
          ∃ c', Step (Profile.spec nd r) host c c' ∧ ExAgree hn c' w)

/-- **The three leaves at every configuration of RE's domain**, for every injective encoding and
finite `HostOk` host. `Round7.Task.wholeStepValidRE` follows (`wholeStepValidRE_of_leaves`). -/
def LeavesRE : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice) (c : Config H) (ts : List CValType),
        ConfigOk c ts → BoundedSelE c →
        EraseFwdAt hn (Profile.spec nd r) host c ∧ EraseBwdAt hn (Profile.spec nd r) host c ∧
          ExactAt hn (Profile.spec nd r) host c

/-- **The three leaves at export-blind hosts.** `Round7.Task.wholeStepValidREH` follows
(`wholeStepValidREH_of_leaves`). There `stripHostAt host c.store = host`, so the SpecTec leaves
are at one set of builtins. -/
def LeavesREH : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → Round7.HostExportBlind host →
      ∀ (nd : Bool) (r : RelaxedChoice) (c : Config H) (ts : List CValType),
        ConfigOk c ts → BoundedSelE c →
        EraseFwdAt hn (Profile.spec nd r) host c ∧ EraseBwdAt hn (Profile.spec nd r) host c ∧
          ExactAt hn (Profile.spec nd r) host c

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
