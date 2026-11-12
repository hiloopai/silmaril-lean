module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.ReadCtrl

/-!
# What is left of `Task.wholeStepBwd10`, after the state and block rules

Discharged on top of `Assemble`: `Step_read` 0 `block`, 1 `loop`, 2 `call`, 6 `local.get`,
7 `global.get`, and `Step` 5 `local.set` (at every builtins), and `Step` 11 `memory.grow-succeed`
(dead at the spec's builtins). `BwdRest10b` lists the rest, at the spec's builtins:

* `Step_pure`: the rules outside `pureDone10` (7–9, 12–17, 20–27);
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

/-- The `Step_read` rules not yet discharged. -/
def readOpen10 : List Nat := [3, 4, 5, 8, 9, 10, 11, 12]

/-- The `Step` rules not yet discharged. -/
def stepOpen10 : List Nat := [6, 7, 8, 9, 10, 12]

/-- **What is left of `Task.wholeStepBwd10`**, at builtins `B`. -/
structure BwdRest10b (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i < 29 → i ∉ pureDone10 → ∀ (c : Config H) (w : List Value), GoodV1 c →
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

/-- `BwdRest10` at the spec's builtins, from `BwdRest10b`. -/
theorem bwdRest10_of_rest2 {P : Profile} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10b (Sim.Floats.floatIntB P) hn host) :
    BwdRest10 (Sim.Floats.floatIntB P) hn host where
  pure := R.pure
  read i hi c w hg hc hw hf := by
    by_cases ho : i ∈ readOpen10
    · exact R.read i ho c w hg hc hw hf
    · have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 7 := by
        simp only [readOpen10, List.mem_cons, List.mem_nil_iff, or_false] at ho
        omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl
      exacts [bwd10_block hf, bwd10_loop hf, bwd10_call hg hf, bwd10_localGet hg hf,
        bwd10_globalGet hg hf]
  step i hi hlt c w hg hf := by
    by_cases ho : i ∈ stepOpen10
    · exact R.step i ho c w hg hf
    · have hi' : i = 5 ∨ i = 11 := by
        simp only [stepOpen10, List.mem_cons, List.mem_nil_iff, or_false] at ho
        omega
      rcases hi' with rfl | rfl
      · exact bwd10_localSet hg hf
      · exact absurd hf (not_fires10_memGrowSucceed P _)

/-- **`Task.wholeStepBwd10` from `BwdRest10b`** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest2
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10b (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest fun H hn hinj host nd r => bwdRest10_of_rest2 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
