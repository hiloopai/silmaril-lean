module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble5
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureBrSucc
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.GlobalSet

/-!
# What is left of `Task.wholeStepBwd10`, after `br-succ` and `global.set`

On top of `Assemble5`, `Step_pure` 9 (`br-succ`, `PureBrSucc`) and `Step` 6 (`global.set`,
`GlobalSet`, under the `GSetOk` conjunct of `GoodV1`) are discharged. `BwdRest10f` lists the rest:

* `Step_pure`: 20–27 (the numeric rules);
* `Step_read`: 3–5 (`call_indirect-*`, `call_addr`), 8–11 (loads), 12 (`memory.size`);
* `Step`: 7–10 (stores).
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

/-- The `Step_pure` rules not yet discharged: the numeric rules. -/
def pureOpen10f : List Nat := [20, 21, 22, 23, 24, 25, 26, 27]

/-- The `Step` rules not yet discharged: the stores. -/
def stepOpen10f : List Nat := [7, 8, 9, 10]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10f (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∈ pureOpen10f → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  read : ∀ (i : Nat), i ∈ readOpen10 → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩
  step : ∀ (i : Nat), i ∈ stepOpen10f → ∀ (c : Config H) (w : Value), GoodV1 c →
    Fires (simEnv10 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step host c c'

/-- `BwdRest10e`, from `BwdRest10f`. -/
theorem bwdRest10e_of_rest6 {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10f B hn host) : BwdRest10e B hn host where
  pure i hi c w hg hc hw hf := by
    by_cases ho : i ∈ pureOpen10f
    · exact R.pure i ho c w hg hc hw hf
    · have hi' : i = 9 := by
        simp only [pureOpen10d, pureOpen10f, List.mem_cons, List.mem_nil_iff, or_false] at ho hi
        omega
      subst hi'
      exact bwd10_brSucc hf
  read := R.read
  step i hi c w hg hf := by
    by_cases ho : i ∈ stepOpen10f
    · exact R.step i ho c w hg hf
    · have hi' : i = 6 := by
        simp only [stepOpen10e, stepOpen10f, List.mem_cons, List.mem_nil_iff, or_false] at ho hi
        omega
      subst hi'
      exact bwd10_globalSet hg hf

/-- **`Task.wholeStepBwd10` from `BwdRest10f`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest6
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10f (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest5 fun H hn hinj host nd r => bwdRest10e_of_rest6 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
