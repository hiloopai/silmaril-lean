module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemGrowFail

/-!
# What is left of `Task.wholeStepBwd10`, after `memory.grow-fail`

On top of `Assemble4`, `Step` 12 (`memory.grow-fail`) is discharged (`MemGrowFail`).
`BwdRest10e` lists the rest:

* `Step_pure`: 9 (`br-succ`) and 20–27 (the numeric rules);
* `Step_read`: 3–5 (`call_indirect-*`, `call_addr`), 8–11 (loads), 12 (`memory.size`);
* `Step`: 6 (`global.set`), 7–10 (stores).
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

/-- The `Step` rules not yet discharged: `global.set` and the stores. -/
def stepOpen10e : List Nat := [6, 7, 8, 9, 10]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10e (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∈ pureOpen10d → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  read : ∀ (i : Nat), i ∈ readOpen10 → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩
  step : ∀ (i : Nat), i ∈ stepOpen10e → ∀ (c : Config H) (w : Value), GoodV1 c →
    Fires (simEnv10 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step host c c'

/-- `BwdRest10d`, from `BwdRest10e`. -/
theorem bwdRest10d_of_rest5 {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10e B hn host) : BwdRest10d B hn host where
  pure := R.pure
  read := R.read
  step i hi c w hg hf := by
    by_cases ho : i ∈ stepOpen10e
    · exact R.step i ho c w hg hf
    · have hi' : i = 12 := by
        simp only [stepOpen10, stepOpen10e, List.mem_cons, List.mem_nil_iff, or_false] at ho hi
        omega
      subst hi'
      exact bwd10_memGrowFail hg hf

/-- **`Task.wholeStepBwd10` from `BwdRest10e`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest5
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10e (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest4 fun H hn hinj host nd r => bwdRest10d_of_rest5 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
