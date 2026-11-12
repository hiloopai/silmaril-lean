module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureBrTable

/-!
# What is left of `Task.wholeStepBwd10`, after `br_table`

On top of `Assemble3`, `Step_pure` 12 and 13 (`br_table-*`) are discharged (`PureBrTable`).
`BwdRest10d` lists the rest:

* `Step_pure`: 9 (`br-succ`) and 20–27 (the numeric rules);
* `Step_read`: 3–5 (`call_indirect-*`, `call_addr`), 8–11 (loads), 12 (`memory.size`);
* `Step`: 6 (`global.set`), 7–10 (stores), 12 (`memory.grow-fail`).
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

/-- The `Step_pure` rules not yet discharged: `br-succ` and the numeric rules. -/
def pureOpen10d : List Nat := [9, 20, 21, 22, 23, 24, 25, 26, 27]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10d (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
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
  step : ∀ (i : Nat), i ∈ stepOpen10 → ∀ (c : Config H) (w : Value), GoodV1 c →
    Fires (simEnv10 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step host c c'

/-- `BwdRest10c`, from `BwdRest10d`. -/
theorem bwdRest10c_of_rest4 {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10d B hn host) : BwdRest10c B hn host where
  pure i hi c w hg hc hw hf := by
    by_cases ho : i ∈ pureOpen10d
    · exact R.pure i ho c w hg hc hw hf
    · have hi' : i = 12 ∨ i = 13 := by
        simp only [pureOpen10, pureOpen10d, List.mem_cons, List.mem_nil_iff, or_false] at ho hi
        omega
      rcases hi' with rfl | rfl
      · exact bwd10_brTableLt hf
      · exact bwd10_brTableGe hf
  read := R.read
  step := R.step

/-- **`Task.wholeStepBwd10` from `BwdRest10d`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest4
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10d (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest3 fun H hn hinj host nd r => bwdRest10c_of_rest4 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
