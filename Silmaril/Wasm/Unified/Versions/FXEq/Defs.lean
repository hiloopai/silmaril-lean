module

public import Silmaril.Wasm.Unified.Versions.FX.Defs
public import Silmaril.Wasm.Models.FXV.Defs
public import Silmaril.Wasm.Models.FX.Thms

/-!
# WasmFX in the unified institution: the corrected reduction and the structured forms

Two variants of the WasmFX model `fxModelN` (`Silmaril.Wasm.Unified.Versions.FX`).

* `fxModelN'`: **WasmFX with continuation values**: the same signature `sigFX` and opcode
  algebra `algFX`, run with the corrected reduction `StepFX'` (`Silmaril.Wasm.Models.FXV`,
  `behavioursFX'`), the model behind `Silmaril.Wasm.Models.FXVModel.fxModel'`;
  `fxModelAt'` at an FX point.
* `shapeFXs`, `algFXs`, `fxModelNs`: **the FX algebra with reachable structured forms**. In
  `algFX` the FX structured forms `block`, `loop` and `if` (FX bodies) are attached to the
  opcodes `named "block" []`, `named "loop" []` and `named "if" []`, which are not opcodes of
  `sigFX` (every opcode of `sigFX` carries a family number). So in `algFX` they denote nothing,
  and an FX body under a structured instruction (a `resume` inside a `block`) has no meaning;
  `Thms` proves this (`algFX_shape_dead`). `shapeFXs` attaches the structured forms to the 3.0
  opcodes of `block`, `loop` and `if` (families `4`, `5`, `6`), `algFXs` is `algFX` with
  `shapeFXs`, and `fxModelNs` runs it with `StepFX`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified.Core30 Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **WasmFX with continuation values** (`StepFX'`) at profile `P`. -/
def fxModelN' (P : Profile) (host : HostSemantics H) (s : Store H) (fx : H → Option FuncFX)
    (f : Frame) (okc : List InstrFX → Prop) : Model UIn UObs sigFX where
  alg := algFX
  ok := fun (D : Set (List InstrFX)) => ∃ is ∈ D, okc is
  run := fun (D : Set (List InstrFX)) vs =>
    {b | ∃ is ∈ D, okc is ∧ b ∈ behavioursFX' P host fx (cfgFX s f is vs)}

/-- WasmFX with continuation values at a CoreFX point. -/
def fxModelAt' (P : Profile) (f : Frame) (okc : List InstrFX → Prop)
    (x : Silmaril.Wasm.Models.FX.Pt H) : Model UIn UObs sigFX :=
  fxModelN' P x.2.1 x.1 x.2.2 f okc

/-- The FX structured forms of `block`, `loop` and `if`, attached to the 3.0 opcodes. -/
def shapeFXs : InstrFX → Option (Opcode × List Imm × List (List InstrFX))
  | .block bt b => some (head (.block bt []), [e bt], [b])
  | .loop bt b => some (head (.loop bt []), [e bt], [b])
  | .if_ bt b₁ b₂ => some (head (.if_ bt [] []), [e bt], [b₁, b₂])
  | _ => none

/-- **The FX opcode algebra with reachable structured forms.** -/
def algFXs : Alg sigFX.Op where
  I := Set InstrFX
  D := Set (List InstrFX)
  nil := {[]}
  cons := consSetFX
  op o imms Ds hs :=
    {x | (∃ i, x = .core i ∧ head i = o.1 ∧ immsOf i = imms ∧ hdlOf i = hs ∧
          List.Forall₂ (fun b D => b.map InstrFX.core ∈ D) i.bodies Ds) ∨
      (∃ j, x = .fx j ∧ headFX j = o.1 ∧ immsFX j = imms ∧ hdlFX j = hs ∧ Ds = []) ∨
      (∃ bs, shapeFXs x = some (o.1, imms, bs) ∧ hs = [] ∧ List.Forall₂ (· ∈ ·) bs Ds)}

/-- **The WasmFX model with reachable structured forms** (`StepFX`). -/
def fxModelNs (P : Profile) (host : HostSemantics H) (s : Store H) (fx : H → Option FuncFX)
    (f : Frame) (okc : List InstrFX → Prop) : Model UIn UObs sigFX where
  alg := algFXs
  ok := fun (D : Set (List InstrFX)) => ∃ is ∈ D, okc is
  run := fun (D : Set (List InstrFX)) vs =>
    {b | ∃ is ∈ D, okc is ∧ b ∈ behavioursFX P host fx (cfgFX s f is vs)}

end Silmaril.Wasm.Unified.Versions
