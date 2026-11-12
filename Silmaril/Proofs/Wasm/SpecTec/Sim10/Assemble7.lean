module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemTrap

/-!
# What is left of `Task.wholeStepBwd10`, after the loads and stores

On top of `Assemble6`, at the spec's builtins `floatIntB`:

* `Step_read` 8, 10 and `Step` 7, 9 (the four trap rules) are discharged (`MemTrap`), at every
  builtins;
* `Step_read` 9, 11 and `Step` 8, 10 (`load-*-val`, `store-*-val`) never fire at `floatIntB`, which
  answers neither `$bytes_` nor `$ibytes_` (`Inert`). These hold vacuously.

So every `Step` rule is discharged. `BwdRest10g` lists the rest:

* `Step_pure`: 20–27 (the numeric rules);
* `Step_read`: 3–5 (`call_indirect-*`, `call_addr`), 12 (`memory.size`).
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

/-- The `Step_read` rules not yet discharged: the indirect and address calls, `memory.size`. -/
def readOpen10g : List Nat := [3, 4, 5, 12]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10g (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∈ pureOpen10f → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  read : ∀ (i : Nat), i ∈ readOpen10g → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩

/-- `BwdRest10f` at the spec's builtins, from `BwdRest10g`. -/
theorem bwdRest10f_of_rest7 {P : Profile} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10g (Sim.Floats.floatIntB P) hn host) :
    BwdRest10f (Sim.Floats.floatIntB P) hn host where
  pure := R.pure
  read i hi c w hg hc hw hf := by
    by_cases ho : i ∈ readOpen10g
    · exact R.read i ho c w hg hc hw hf
    · have hi' : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by
        simp only [readOpen10, readOpen10g, List.mem_cons, List.mem_nil_iff, or_false] at ho hi
        omega
      rcases hi' with rfl | rfl | rfl | rfl
      · exact bwd10_loadNumTrap hg hf
      · exact absurd hf (not_fires_loadNumVal10 P _)
      · exact bwd10_loadPackTrap hg hf
      · exact absurd hf (not_fires_loadPackVal10 P _)
  step i hi c w hg hf := by
    have hi' : i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by
      simp only [stepOpen10f, List.mem_cons, List.mem_nil_iff, or_false] at hi
      omega
    rcases hi' with rfl | rfl | rfl | rfl
    · exact bwd10_storeNumTrap hg hf
    · exact absurd hf (not_fires_storeNumVal10 P _)
    · exact bwd10_storePackTrap hg hf
    · exact absurd hf (not_fires_storePackVal10 P _)

/-- **`Task.wholeStepBwd10` from `BwdRest10g`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest7
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10g (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest6 fun H hn hinj host nd r => bwdRest10f_of_rest7 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
