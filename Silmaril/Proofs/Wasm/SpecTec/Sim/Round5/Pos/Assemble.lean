module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.TypedNE
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Refute

/-!
# Round 5: the restated target from `PartsOk`

* `oneStepOk_of_parts`, `wholeStepValidOk_of_parts`: `Round5.Task.wholeStepValidOk` from
  `PartsOk` at every injective encoding, finite `HostOk` host and `Profile.spec nd r`. The
  successor is typed through Core's `Step.preservation` (a `HostOk` host keeps validity) and
  `typed_of_configOk_ne`; `succTyped` is no longer a field.
* `partsOk_of_parts`: `Round4Int.Parts` gives `PartsOk` (vacuously, since `Parts` is
  unsatisfiable through its `pos` field, `not_posTyping`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The restated one-step simulation, from `PartsOk`**, for a `HostOk` host. -/
theorem oneStepOk_of_parts (Pa : PartsOk hn P host) (hh : HostOk host) :
    (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedNE c → BoundedNE c' →
      Step P host c c' → ∃ d', Bwd.ConfigEq c' d' ∧
        SStep (simEnv (Round4Int.BI P hn host)) (configV hn c) (configV hn d')) ∧
    (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts → BoundedNE c →
      SStep (simEnv (Round4Int.BI P hn host)) (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c') :=
  ⟨fun c c' ts hc hb hb' hs =>
      Pa.fwd c c' ⟨⟨⟨ts, hc⟩, hb.1⟩, hb.2⟩ hb.1.store (typed_of_configOk_ne Pa.pos hc hb)
        (typed_of_configOk_ne Pa.pos (Step.preservation hh hc hs).1 hb') hs,
    fun c _ w hc hb hs =>
      Round4Int.backward_fam Pa.fam Pa.rem c w (Round4Int.readValid_of_bounded hc hb.1)
        (typed_of_configOk_ne Pa.pos hc hb) hs⟩

/-- **`Round5.Task.wholeStepValidOk`, from `PartsOk`** at every injective encoding, finite
`HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem wholeStepValidOk_of_parts
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), PartsOk hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk := fun H hn hinj host hfin hok nd r =>
  ⟨_, oneStepOk_of_parts (h H hn hinj host hfin hok nd r) hok⟩

/-- `Round4Int.Parts` gives `PartsOk`, so `PartsOk` asks no more than round 4 did. -/
theorem partsOk_of_parts (Pa : Round4Int.Parts hn P host) : PartsOk hn P host where
  pos := posTypingNE_of_posTyping Pa.pos
  fwd := R4Fwd.Forward.mono (fun _ h => h.1) Pa.fwd
  fam := Pa.fam
  rem := Pa.rem

/-- **`Round4Int.Parts` is unsatisfiable**, at every encoding, host and profile: its `pos`
field is `Round4.PosTyping`, which is uninhabited. -/
theorem not_parts (hn : H → String) (P : Profile) (host : HostSemantics H) :
    ¬ Round4Int.Parts hn P host := fun Pa => not_posTyping _ hn Pa.pos

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
