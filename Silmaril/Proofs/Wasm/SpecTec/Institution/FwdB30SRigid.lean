module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SExact

/-!
# `Step_pure`/`Step_read` facts at `Wasm30.builtins`, exactly

`FwdB30X.pureX_builtins` and `readX_builtins` give, at every `FwdX30.PureHeadX`/`ReadHeadX`
redex on `DomDet`, a fact of `stepModel builtins` to Core's successor up to `CfgRel`. When the
successor's code is rigid (`RigidV`: no `CALL_REF`, label, handler or frame at the top), `CfgRel`
is equality there (`cfgRel_exact`), so the fact is to the image of Core's successor itself.

* `pureHeadX_rigid`: every `PureHeadX` successor is rigid (values, `TRAP`, `br`, `local.set`,
  `array.new_fixed`, …), so **`pureX_exact`**: the `Step_pure` fact exists at `adminsToV is'`.

The `Step_read` side is in `FwdB30SRigidR`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (PureHeadX ReadHeadX)

variable {H : Type}

/-- **Every `PureHeadX` successor is rigid.** -/
theorem pureHeadX_rigid {P : Profile} {is is' : List Admin} (h : PureHeadX P is is') :
    RigidV (adminsToV is') := by
  cases h with
  | numeric h => cases h <;> rigid_tac
  | vector h _ => cases h <;> rigid_tac
  | _ => rigid_tac

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- **Every `PureHeadX` redex has its `Step_pure` fact at `builtins`, exactly**: on `DomDet`,
the image of Core's successor code is a `Step_pure` fact of `stepModel builtins`. -/
theorem pureX_exact {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hp : PureHeadX (Profile.spec nd r) c.code is') :
    (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) :=
  exact_of_cfgRel
    (Q := fun js => (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js]))
    (FwdB30X.pureX_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hp) (pureHeadX_rigid hp)

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
