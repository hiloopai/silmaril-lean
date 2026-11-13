module

public import Silmaril.Wasm.Unified.Versions.FXSim.Defs
public import Silmaril.Raw.Wasm.Unified.FXSim.Beh

/-!
# CoreFX simulates Core 3.0 on FX code that reads as Core code

* **`behavioursFX_lift`**: if FX administrative code `es` reads as Core code `cs`
  (`LiftAs es cs`: Core instructions, and FX `block`, `loop`, `if` and labels whose bodies read
  as the Core ones), CoreFX without FX functions (`StepFX P host noFX`) and Core 3.0
  (`Step P host`) have **the same behaviours** from `es` and `cs` (same store and frame, any
  continuation store): the same results and the same divergence.
* `behavioursFX_liftIs`: the same for source code run on arguments (`cvals vs ++ b` against
  `vals vs ++ expression is`, `LiftIs b is`).
* `LiftIs.functional`, `liftIs_map_core`, `LiftIs.map_core_iff`: FX code reads as at most one
  Core program; embedded Core code reads as itself.

The proof (`Silmaril/Raw/Wasm/Unified/FXSim`) is a lock-step simulation in both directions. Forward,
every CoreFX rule on such code is a Core rule (`fwd`). Backward, every Core step is a CoreFX step
(`bwd`), except `return_call_ref-label` on a label that the FX code holds as an FX label: CoreFX
has no such rule. There the Core code is **doomed** (`Doomed`: a `return_call_ref` reachable only
through labels, outside any frame), and doomed code has no behaviours (`doomed_behavioursOf`);
the FX code is stuck without a result, so both sides agree.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **CoreFX and Core 3.0 have the same behaviours on FX code that reads as Core code.** -/
theorem behavioursFX_lift (P : Profile) (host : HostSemantics H) {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {es : List AdminFX} {cs : List Admin}
    (hl : LiftAs es cs) :
    behavioursFX P host noFX ⟨s, K, f, es⟩ = behavioursOf P host ⟨s, f, cs⟩ :=
  Silmaril.Raw.Wasm.Unified.FXSim.behavioursFX_lift hl

/-- Source code that reads as Core code, run on arguments. -/
theorem behavioursFX_liftIs (P : Profile) (host : HostSemantics H) (s : Store H)
    (K : List (Option ContFX)) (f : Frame) (vs : List Val) {b : List InstrFX} {is : List Instr}
    (hl : LiftIs b is) :
    behavioursFX P host noFX ⟨s, K, f, cvals vs ++ b.map InstrFX.toAdmin⟩ =
      behavioursOf P host ⟨s, f, vals vs ++ expression is⟩ :=
  behavioursFX_lift P host (Silmaril.Raw.Wasm.Unified.FXSim.LiftAs.append
    (Silmaril.Raw.Wasm.Unified.FXSim.liftAs_cvals vs)
    (Silmaril.Raw.Wasm.Unified.FXSim.LiftIs.toAdmin hl))

mutual
/-- An FX instruction reads as at most one Core instruction. -/
theorem LiftI.functional : ∀ {x : InstrFX} {i j : Instr}, LiftI x i → LiftI x j → i = j
  | _, _, _, .core _, .core _ => rfl
  | _, _, _, .block h, .block h' => by rw [LiftIs.functional h h']
  | _, _, _, .loop h, .loop h' => by rw [LiftIs.functional h h']
  | _, _, _, .if_ h₁ h₂, .if_ h₁' h₂' => by
    rw [LiftIs.functional h₁ h₁', LiftIs.functional h₂ h₂']

/-- **FX code reads as at most one Core program.** -/
theorem LiftIs.functional : ∀ {b : List InstrFX} {is js : List Instr},
    LiftIs b is → LiftIs b js → is = js
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h t, .cons h' t' => by rw [LiftI.functional h h', LiftIs.functional t t']
end

/-- Embedded Core code reads as itself. -/
theorem liftIs_map_core : ∀ is : List Instr, LiftIs (is.map InstrFX.core) is
  | [] => .nil
  | i :: is => .cons (.core i) (liftIs_map_core is)

/-- Embedded Core code reads only as itself. -/
theorem LiftIs.map_core_iff {is js : List Instr} : LiftIs (is.map InstrFX.core) js ↔ js = is :=
  ⟨fun h => LiftIs.functional h (liftIs_map_core is), fun h => h ▸ liftIs_map_core is⟩

end Silmaril.Wasm.Unified.Versions
