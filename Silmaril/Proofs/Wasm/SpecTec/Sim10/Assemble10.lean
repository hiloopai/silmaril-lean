module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble9
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureNumBwd

/-!
# What is left of `Task.wholeStepBwd10`, after the numeric rules

On top of `Assemble9`, `Step_pure` 20–27 (the numeric rules) are discharged at the spec's builtins
`Sim.Floats.floatIntB (Profile.spec nd r)`: `NumAgree10` holds there (`numAgree10_floatIntB`), and
under it every numeric rule is the image of a V1 `PureStep` (`bwd10_num`). `BwdRest10j` is the one
item left: `Step_read` 4, `call_indirect-trap`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Config HostSemantics Step PureStep)
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)

variable {H : Type}

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`: `call_indirect-trap`. -/
structure BwdRest10j (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  callIndirectTrap : ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" 4 (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩

/-- `BwdRest10i` at the spec's builtins, from `BwdRest10j`. -/
theorem bwdRest10i_of_rest10 {hn : H → String} {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} (R : BwdRest10j (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    BwdRest10i (Sim.Floats.floatIntB (Profile.spec nd r)) hn host where
  pure _ hi _ _ _ _ _ hf := bwd10_num numAgree10_floatIntB hi hf
  callIndirectTrap := R.callIndirectTrap

/-- **`Task.wholeStepBwd10` from `BwdRest10j`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest10
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10j (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest9 fun H hn hinj host nd r => bwdRest10i_of_rest10 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
