module

public import Silmaril.Wasm.Unified.Core30.Defs
public import Silmaril.Wasm.Atlas.Variant.Defs
public import Silmaril.Wasm.Wasmi.Defs

/-!
# Step-relation variants of the Core 3.0 model

The unified core's Core 3.0 model (`Silmaril.Wasm.Unified.Core30.model30`) interprets the 3.0
opcodes in the algebra `alg30` (sets of silmaril instructions) and runs code with Core 3.0
reduction `Step P host`. The variants of Core in the Atlas (`Silmaril.Wasm.Atlas.Variant`: the
loose model, implementations that deviate at a redex, spec errata) differ only in the step
relation, so they are models of the same signature with the same algebra:

* `modelR R host s f okc`: **the model of a step-relation family `R`** (code run from
  `vals vs ++ expression is` in store `s` and frame `f`, observations
  `Silmaril.Wasm.Atlas.Variant.behavioursR`); `model30` is `modelR (Step P)` (`Thms`,
  definitionally);
* `looseR P`: **the loose model** (`Silmaril.Wasm.Wasmi.Loose.Step`, Core 3.0 with
  `selectEither`);
* `wasmiR P`: **the wasmi model**: Core 3.0 on the translated store and translated code
  (`Silmaril.Wasm.Wasmi.fuseStore`, `fuse`), as wasmi 2.0.0 runs it;
* `Refines M N`: every observation of `M` is one of `N`, on every call: the model morphisms
  of this layer (the unified core's model category is discrete).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

/-- Inputs of a call: the arguments. -/
abbrev UIn : Type := List Val

/-- Observations: behaviours over Core 3.0 values. -/
abbrev UObs : Type := Behaviour Val

variable {H : Type}

/-- The configuration running instructions `is` on arguments `vs`. -/
def cfgOf (s : Store H) (f : Frame) (is : List Instr) (vs : UIn) : Config H :=
  ⟨s, f, vals vs ++ expression is⟩

/-- **The model of a step relation** over the 3.0 signature. -/
def modelR (R : Config H → Config H → Prop) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Model UIn UObs sig30 where
  alg := alg30
  ok := fun (D : Set (List Instr)) => ∃ is ∈ D, okc is
  run := fun (D : Set (List Instr)) vs =>
    {b | ∃ is ∈ D, okc is ∧ b ∈ Variant.behavioursR R (cfgOf s f is vs)}

/-- **The loose model** at profile `P`. -/
abbrev looseR (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Model UIn UObs sig30 :=
  modelR (Silmaril.Wasm.Wasmi.Loose.Step P host) s f okc

/-- **The wasmi model** at profile `P`: Core 3.0 on the translated store and code. -/
def wasmiR (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Model UIn UObs sig30 where
  alg := alg30
  ok := fun (D : Set (List Instr)) => ∃ is ∈ D, okc is
  run := fun (D : Set (List Instr)) vs =>
    {b | ∃ is ∈ D, okc is ∧ b ∈ Variant.behavioursR (Step P host)
      (cfgOf (Silmaril.Wasm.Wasmi.fuseStore s) f (Silmaril.Wasm.Wasmi.fuse is) vs)}

/-- **Refinement** of models of one signature: every observation of `M` is one of `N`. -/
def Refines {In B : Type} {K : FSig} (M N : Model In B K) : Prop := ∀ x, M.obs x ⊆ N.obs x

end Silmaril.Wasm.Unified.Versions
