module

public import Silmaril.Wasm.Unified.Versions.Run.Defs

/-!
# Spec errata as models differing on one opcode

A defect of a specification at one opcode is a model of the same signature with the same opcode
algebra whose step relation differs only at redexes of that opcode. The example is the
`table.grow` defect of the pinned SpecTec 3.0 script (`Silmaril.Wasm.SpecTec.Broken`,
`TableGrowNeverFires`: no rule for `table.grow` ever fires): the erratum model has no step from a
configuration whose redex is `table.grow`.

* `dropAt R At`: the step relation `R` without the steps from configurations satisfying `At`
  (the redex class of the opcode);
* `GrowRedex c`: the code is a `table.grow` redex (a reference, an address constant and
  `table.grow x`, the operands of `Step/table.grow` and `Step/table.grow-fail`); `AtGrow c`: a
  `table.grow` redex in an evaluation context (`Silmaril.Wasm.Atlas.Variant.Ctx`);
* `growErr P host`: **Core 3.0 with `table.grow` never firing**; `errR`: **the erratum model**
  over the 3.0 signature (`modelR (growErr P host)`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The step relation `R` without the steps from configurations satisfying `At`. -/
def dropAt (R : Config H → Config H → Prop) (At : Config H → Prop) (c c' : Config H) : Prop :=
  R c c' ∧ ¬ At c

/-- A `table.grow` redex. -/
def GrowRedex (c : Config H) : Prop :=
  ∃ (r : Ref) (a : AddrType) (n : BitVec a.intType.width) (x : TableIdx),
    c.code = [.ref r, .plain (.intConst a.intType n), .plain (.tableGrow x)]

/-- A `table.grow` redex in an evaluation context. -/
def AtGrow (c : Config H) : Prop := ∃ c', Variant.Ctx (fun c _ => GrowRedex c) c c'

/-- **Core 3.0 with `table.grow` never firing.** -/
abbrev growErr (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  dropAt (Step P host) AtGrow

/-- **The erratum model** over the 3.0 signature. -/
abbrev errR (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Model UIn UObs sig30 :=
  modelR (growErr P host) s f okc

end Silmaril.Wasm.Unified.Versions
