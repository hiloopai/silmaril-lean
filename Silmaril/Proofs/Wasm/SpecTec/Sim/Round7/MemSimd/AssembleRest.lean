module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.AssembleD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.EntryD

/-!
# Round 7, memory SIMD: three fields of `OpenRM` proved

Pass 6 reduced `Round7.Task.wholeStepValidRM` to `OpenRM V` (`wholeStepValidRM_of_open`). Three
of its fields are now proved, at `V := NoCastVM`:

* `closed`: `noCastVM_closed`;
* `entry`: `noCastVM_entry`;
* `typed`: `typedD_of_configOk_selM` (round 5's positive typing re-run at `configVD`).

`OpenRMRest` collects the fields that are still open: `forward`, `rest` (at `V := NoCastVM`),
`castsFwd` and `castsBwd`. `openRM_of_rest` builds `OpenRM NoCastVM` from them, and
`wholeStepValidRM_of_rest` proves the frozen target from `OpenRMRest`. It is a reduction: no field
of `OpenRMRest` is proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.Target (CastRedex)

variable {H : Type}

/-- **What is left of `OpenRM` at `V := NoCastVM`**: the forward half away from cast redexes,
the per-rule backward obligations off memory SIMD under `NoCastVM`, and the cast leaf. -/
structure OpenRMRest (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- The declarative forward half at `configVD`, away from cast redexes, up to Core's choice of
  successor. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BM P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations of the rules without memory SIMD, under `NoCastVM`. -/
  rest : BackwardUpToDRestS NoCastVM (simEnv (BM P hn host)) hn P host
  /-- The cast leaf, forward. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BM P hn host) (configVD hn c) (configVD hn d')
  /-- The cast leaf, backward. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code →
    Round6.Int.backend.step (BM P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

/-- **`OpenRM NoCastVM` from its open fields**: `closed`, `entry` and `typed` are proved. -/
theorem openRM_of_rest {hn : H → String} {P : Profile} {host : HostSemantics H}
    (O : OpenRMRest hn P host) : OpenRM NoCastVM hn P host where
  forward := O.forward
  closed := noCastVM_closed
  entry := noCastVM_entry
  typed _ _ hc hb := typedD_of_configOk_selM _ hn hc hb
  rest := O.rest
  castsFwd := O.castsFwd
  castsBwd := O.castsBwd

/-- **`Round7.Task.wholeStepValidRM` from `OpenRMRest`**: the frozen round-7 target holds as soon
as the forward half, the non-memory-SIMD backward obligations under `NoCastVM` and the cast leaf
hold at every injective encoding, finite `HostOk` host and spec profile. -/
theorem wholeStepValidRM_of_rest
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenRMRest hn (Profile.spec nd r) host) :
    Task.wholeStepValidRM :=
  wholeStepValidRM_of_open fun H hn hinj host hfin hok nd r =>
    ⟨NoCastVM, openRM_of_rest (h H hn hinj host hfin hok nd r)⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
