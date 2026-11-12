module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureVals

/-!
# What is left of `Task.wholeStepBwd10`, after the value-sequence rules

On top of `Assemble2`, `Step_pure` 7 `label-vals`, 8 `br-zero`, 14 `frame-vals`, 15 `return-frame`,
16 `return-label` and 17 `trap-vals` are discharged (`PureVals`). `BwdRest10c` lists the rest:

* `Step_pure`: 9 (`br-succ`), 12–13 (`br_table-*`), 20–27 (the numeric rules);
* `Step_read`: `readOpen10`; `Step`: `stepOpen10` (unchanged from `BwdRest10b`).
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

/-- The `Step_pure` rules not yet discharged. -/
def pureOpen10 : List Nat := [9, 12, 13, 20, 21, 22, 23, 24, 25, 26, 27]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10c (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∈ pureOpen10 → ∀ (c : Config H) (w : List Value), GoodV1 c →
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

/-- `BwdRest10b`, from `BwdRest10c`. -/
theorem bwdRest10b_of_rest3 {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10c B hn host) : BwdRest10b B hn host where
  pure i hi hd c w hg hc hw hf := by
    by_cases ho : i ∈ pureOpen10
    · exact R.pure i ho c w hg hc hw hf
    · have hi' : i = 7 ∨ i = 8 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 := by
        simp only [pureOpen10, pureDone10, List.mem_cons, List.mem_nil_iff, or_false] at ho hd
        omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [bwd10_labelVals hf, bwd10_brZero hf, bwd10_frameVals hf, bwd10_returnFrame hf,
        bwd10_returnLabel hf, bwd10_trapVals hf]
  read := R.read
  step := R.step

/-- **`Task.wholeStepBwd10` from `BwdRest10c`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10c (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest2 fun H hn hinj host nd r => bwdRest10b_of_rest3 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
