module

public import Silmaril.Wasm.Unified.Versions.Own.Defs
public import Silmaril.Wasm.Unified.Versions.Named.Thms
public import Silmaril.Wasm.Models.V10.Defs
public import Silmaril.Wasm.Models.Lime1Core.Defs
public import Silmaril.Wasm.Lime1.FromV1

/-!
# The versions' own semantics as models of their unified signatures

`v10own`, `v20own` and `lime1own` (`Silmaril.Wasm.Models`) run silmaril's own 1.0, 2.0 and Lime1
machines on the versions' own syntaxes. Here they become models of the unified institution
through the own opcode algebras of `Silmaril.Wasm.Unified.Versions.Own`:

* the own syntaxes: `synL` (Lime1, translated by `Lime1.Instr.toCore`), `syn10` (1.0, translated
  through Lime1, `Lime1.Instr.toCore ∘ V1.Instr.toLime`, the route of the copied 1.0
  simulation) and `syn20` (2.0, `V2.Instr.toCore`, partial);
* the own behaviours of code: `behL`, `beh10`, `beh20 P`: run `values ws ++ code` from an own
  store and frame with the own reduction (`behavioursOfL`, `V1.Execution.behavioursOf`,
  `V2.Execution.behavioursOf P`), for own arguments `ws` whose Core reading is the input, and
  read the behaviours in Core values (`Value.toCore`, `V2.Execution.Val.toCore`). 1.0 values are
  read directly into Core (`Value.toCore`), not through 2.0 as `V10.obs` does;
* `ownLAt`, `own10At`, `own20At`: the own models of the 3.0 signature (own validation `okJ`, a
  parameter like the core's `okc`), and **`lime1ownAt`, `v10ownAt`, `v20ownAt`**: their reducts
  to the version signatures `nLime1`, `n10`, `n20`, at an own point (store and host) and own
  frame.

`Thms` relates them to the reducts of `model30` at the Core images of the points.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models

/-- The nested bodies of a Lime1 instruction. -/
def bodL : Lime1.Instr → List (List Lime1.Instr)
  | .block _ b | .loop _ b => [b]
  | .if_ _ l r => [l, r]
  | _ => []

/-- **Lime1's own syntax.** -/
def synL : Syn := ⟨Lime1.Instr, fun j => some j.toCore, bodL⟩

/-- **Wasm 1.0's own syntax**, translated through Lime1. -/
def syn10 : Syn := ⟨V1.Instr, fun j => some j.toLime.toCore, V1.Instr.bodies⟩

/-- **Wasm 2.0's own syntax.** -/
def syn20 : Syn := ⟨V2.Instr, V2.Instr.toCore, V2.Instr.bodies⟩

variable {H : Type}

/-- Lime1 behaviours of code. -/
def behL (host : V10.LHost H) (s : V10.LStore H) (f : Frame) (js : List Lime1.Instr) :
    UIn → Set UObs :=
  ownBeh Value.toCore Value.toCore fun ws =>
    Lime1Core.behavioursOfL host ⟨s, f, Lime1.Execution.values ws ++ Lime1.Execution.expression js⟩

/-- Wasm 1.0 behaviours of code. -/
def beh10 (host : V10.OHost H) (s : V10.OStore H) (f : Frame) (js : List V1.Instr) :
    UIn → Set UObs :=
  ownBeh Value.toCore Value.toCore fun ws =>
    V1.Execution.behavioursOf host ⟨s, f, V1.Execution.values ws ++ V1.Execution.expression js⟩

/-- Wasm 2.0 behaviours of code, at profile `P`. -/
def beh20 (P : Profile) (host : V2Core.VHost H) (s : V2Core.VStore H) (f : V2.Execution.Frame)
    (js : List V2.Instr) : UIn → Set UObs :=
  ownBeh V2.Execution.Val.toCore V2.Execution.Val.toCore fun ws =>
    V2.Execution.behavioursOf P host ⟨s, f, V2.Execution.vals ws ++ js.map .plain⟩

/-- The own Lime1 model of the 3.0 signature. -/
def ownLAt (okJ : List Lime1.Instr → Prop) (f : Frame) (p : Lime1Core.Pt H) :
    Model UIn UObs sig30 :=
  ownModel synL okJ (behL p.2 p.1 f)

/-- The own 1.0 model of the 3.0 signature. -/
def own10At (okJ : List V1.Instr → Prop) (f : Frame) (p : V10.Pt H) : Model UIn UObs sig30 :=
  ownModel syn10 okJ (beh10 p.2 p.1 f)

/-- The own 2.0 model of the 3.0 signature. -/
def own20At (P : Profile) (okJ : List V2.Instr → Prop) (f : V2.Execution.Frame)
    (p : V2Core.Pt H) : Model UIn UObs sig30 :=
  ownModel syn20 okJ (beh20 P p.2 p.1 f)

/-- **Lime1's own semantics** as a model of the Lime1 signature. -/
def lime1ownAt (okJ : List Lime1.Instr → Prop) (f : Frame) (p : Lime1Core.Pt H) :
    Model UIn UObs nLime1 :=
  (ownLAt okJ f p).reduct (FSig.incl (nsig_sub30 _))

/-- **Wasm 1.0's own semantics** as a model of the 1.0 signature. -/
def v10ownAt (okJ : List V1.Instr → Prop) (f : Frame) (p : V10.Pt H) : Model UIn UObs n10 :=
  (own10At okJ f p).reduct (FSig.incl (nsig_sub30 _))

/-- **Wasm 2.0's own semantics** as a model of the 2.0 signature. -/
def v20ownAt (P : Profile) (okJ : List V2.Instr → Prop) (f : V2.Execution.Frame)
    (p : V2Core.Pt H) : Model UIn UObs n20 :=
  (own20At P okJ f p).reduct (FSig.incl (nsig_sub30 _))

end Silmaril.Wasm.Unified.Versions.Own
