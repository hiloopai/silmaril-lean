module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble8
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CallIndirect

/-!
# What is left of `Task.wholeStepBwd10`, after the calls

On top of `Assemble8`, `Step_read` 3 (`call_indirect-call`, `CallIndirect`) and 5 (`call_addr`,
`CallAddr`) are discharged at every builtins. `BwdRest10i` lists the rest:

* `Step_pure`: 20–27 (the numeric rules);
* `Step_read`: 4 (`call_indirect-trap`, an `otherwise` rule).
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

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10i (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∈ pureOpen10f → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  callIndirectTrap : ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" 4 (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩

/-- `BwdRest10h`, from `BwdRest10i`. -/
theorem bwdRest10h_of_rest9 {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10i B hn host) : BwdRest10h B hn host where
  pure := R.pure
  read i hi c w hg hc hw hf := by
    have hi' : i = 3 ∨ i = 4 ∨ i = 5 := by
      simp only [readOpen10h, List.mem_cons, List.mem_nil_iff, or_false] at hi
      omega
    rcases hi' with rfl | rfl | rfl
    · exact bwd10_callIndirect hg hf
    · exact R.callIndirectTrap c w hg hc hw hf
    · exact bwd10_callAddr hg hf

/-- **`Task.wholeStepBwd10` from `BwdRest10i`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest9
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10i (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest8 fun H hn hinj host nd r => bwdRest10h_of_rest9 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
