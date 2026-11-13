module

public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Wasm.Unified.Versions.Defs

/-!
# The Wasm models at the component boundary

The unified Wasm models (`model30`, and the `Versions` models: 1.0, 2.0, Lime1, `core|S`, the
loose model, wasmi, all with inputs `List Val` and observations `Behaviour Val`) as core
semantics of the component layer, through the flat calling convention `abi30`:

* a flat payload `[x₁, …, xₙ]` is the argument list of numeric values (`flatVal`); a payload of
  component values is rejected (core modules are called with core values only);
* `returns vs` answers the flat values of `vs` if they are all numeric, and traps otherwise
  (references and vectors do not cross the flat boundary); `traps` and an uncaught exception
  (`throws`) answer a trap; `diverges` gives no answer (the game model observes safety only).

`coreSemV M := coreSem (M.abi abi30)` is the core semantics of a unified Wasm model; for
instance `coreSem30 P host s f okc` is Core 3.0. `uCompSemV M` etc. are the component logics of
`Silmaril.Wasm.Institution.Components` at that core semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (Flat Payload CoreSem)
open Silmaril.Wasm.Unified

/-- A flat value as a Core 3.0 value. -/
def flatVal (v : Flat) : Val := .num ⟨v.type, v.bits⟩

/-- A Core 3.0 value as a flat value (numeric values only). -/
def valFlat : Val → Option Flat
  | .num v => some ⟨v.type, v.bits⟩
  | _ => none

/-- The flat calling convention of the Wasm models. -/
def abi30 : Abi (List Val) (Behaviour Val) where
  arg
    | .flat xs => some (xs.map flatVal)
    | .vals _ => none
  ret
    | .returns vs => some ((vs.mapM valFlat).map Payload.flat)
    | .traps => some none
    | .throws _ => some none
    | .diverges => none

/-- The core semantics of a unified Wasm model. -/
abbrev coreSemV {S : FSig} (M : Model (List Val) (Behaviour Val) S) : CoreSem (UMod S) :=
  coreSem (M.abi abi30)

/-- **Core 3.0 as the core semantics of components.** -/
abbrev coreSem30 (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : CoreSem (UMod Core30.sig30) :=
  coreSemV (Core30.model30 P host s f okc)

/-- The nested-component logic of a unified Wasm model. -/
abbrev uCompSemV {S : FSig} (M : Model (List Val) (Behaviour Val) S) :=
  Silmaril.Wasm.Institution.Components.compSem (coreSemV M)

/-- The program logic of a unified Wasm model. -/
abbrev uProgramSemV {S : FSig} (M : Model (List Val) (Behaviour Val) S) :=
  Silmaril.Wasm.Institution.Components.programSem (coreSemV M)

end Silmaril.Wasm.Unified.Component
