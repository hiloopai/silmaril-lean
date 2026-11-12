module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemSize

/-!
# What is left of `Task.wholeStepBwd10`, after `memory.size`

On top of `Assemble7`, `Step_read` 12 (`memory.size`) is discharged (`MemSize`). `BwdRest10h`
lists the rest:

* `Step_pure`: 20–27 (the numeric rules);
* `Step_read`: 3–5 (`call_indirect-*`, `call_addr`).
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

/-- The `Step_read` rules not yet discharged: the indirect and address calls. -/
def readOpen10h : List Nat := [3, 4, 5]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10h (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∈ pureOpen10f → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  read : ∀ (i : Nat), i ∈ readOpen10h → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩

/-- `BwdRest10g`, from `BwdRest10h`. -/
theorem bwdRest10g_of_rest8 {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10h B hn host) : BwdRest10g B hn host where
  pure := R.pure
  read i hi c w hg hc hw hf := by
    by_cases ho : i ∈ readOpen10h
    · exact R.read i ho c w hg hc hw hf
    · have hi' : i = 12 := by
        simp only [readOpen10g, readOpen10h, List.mem_cons, List.mem_nil_iff, or_false] at ho hi
        omega
      subst hi'
      exact bwd10_memorySize hg hw hf

/-- **`Task.wholeStepBwd10` from `BwdRest10h`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest8
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10h (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest7 fun H hn hinj host nd r => bwdRest10g_of_rest8 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
