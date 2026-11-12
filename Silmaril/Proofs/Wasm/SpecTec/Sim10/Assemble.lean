module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureCtrl

/-!
# What is left of `Task.wholeStepBwd10`

`BwdRest10` lists the per-rule obligations not yet discharged; `wholeStepBwd10_of_rest` reduces the
1.0 backward target to it at the spec's builtins. Discharged here, for every builtins:

* the five structural rules of `Step` (`WholeBwd`);
* `Step_pure` 0–6, 10, 11, 18, 19 and 28 (`PureCtrl`), `select-*` using `SelOk`;
* every index past the end of a relation (`Step_pure` has 29 rules, `Step_read` 13, `Step` 13:
  `not_firesPure10_ge`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep)
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)

set_option maxRecDepth 100000

/-! ## The lengths of the three relations -/

/-- A rule index past the end of a relation does not fire. -/
theorem not_fires_of_length {env : Env} {x : IL.Id} {n i : Nat}
    (hl : (env.findRel? x).map (fun r => r.2.2.2.length) = some n) (hi : n ≤ i) {v : Value} :
    ¬ Fires env x i v := by
  rintro ⟨t, rules, r, hrel, hr, -⟩
  rw [hrel] at hl
  have e : rules.length = n := Option.some.inj hl
  rw [List.getElem?_eq_none (by omega)] at hr
  exact absurd hr (by simp)

theorem not_firesPure10_ge {B : Builtins} {i : Nat} (hi : 29 ≤ i) {v : Value} :
    ¬ Fires (simEnv10 B) "Step_pure" i v :=
  not_fires_of_length rfl hi

theorem not_firesRead10_ge {B : Builtins} {i : Nat} (hi : 13 ≤ i) {v : Value} :
    ¬ Fires (simEnv10 B) "Step_read" i v :=
  not_fires_of_length rfl hi

theorem not_firesStep10_ge {B : Builtins} {i : Nat} (hi : 13 ≤ i) {v : Value} :
    ¬ Fires (simEnv10 B) "Step" i v :=
  not_fires_of_length rfl hi

/-! ## `Step_pure` -/

/-- The `Step_pure` rules discharged backwards. -/
def pureDone10 : List Nat := [0, 1, 2, 3, 4, 5, 6, 10, 11, 18, 19, 28]

variable {H : Type}

/-- **The discharged `Step_pure` rules**, at code satisfying `GoodV1`. -/
theorem pureDone10_bwd {B : Builtins} {i : Nat} (hi : i ∈ pureDone10) {c : Config H}
    {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w])) :
    PureBwd10 c.code w := by
  simp only [pureDone10, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd10_unreachable hf, bwd10_nop hf, bwd10_drop hf, bwd10_selectTrue hg.2.2.1 hf,
    bwd10_selectFalse hg.2.2.1 hf, bwd10_ifTrue hf, bwd10_ifFalse hf, bwd10_brIfTrue hf,
    bwd10_brIfFalse hf, bwd10_trapLabel hf, bwd10_trapFrame hf, bwd10_localTee hf]

/-! ## What is left -/

/-- **What is left of the backward obligations of `Task.wholeStepBwd10`**: the `Step_pure` rules
outside `pureDone10`, and the `Step_read` and `Step` rules, at `GoodV1` configurations. -/
structure BwdRest10 (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i < 29 → i ∉ pureDone10 → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  read : ∀ (i : Nat), i < 13 → ∀ (c : Config H) (w : List Value), GoodV1 c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩
  step : ∀ (i : Nat), 5 ≤ i → i < 13 → ∀ (c : Config H) (w : Value), GoodV1 c →
    Fires (simEnv10 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step host c c'

/-- The per-rule obligations under `GoodV1`, from what is left. -/
theorem bwdParts10_of_rest {B : Builtins} {hn : H → String} {host : HostSemantics H}
    (R : BwdRest10 B hn host) : BwdParts10 GoodV1 B hn host where
  pure i c w hg hc hw hf := by
    by_cases hlt : i < 29
    · by_cases hd : i ∈ pureDone10
      · exact pureDone10_bwd hd hg hf
      · exact R.pure i hlt hd c w hg hc hw hf
    · exact absurd hf (not_firesPure10_ge (by omega))
  read i c w hg hc hw hf := by
    by_cases hlt : i < 13
    · exact R.read i hlt c w hg hc hw hf
    · exact absurd hf (not_firesRead10_ge (by omega))
  step i hi c w hg hf := by
    by_cases hlt : i < 13
    · exact R.step i hi hlt c w hg hf
    · exact absurd hf (not_firesStep10_ge (by omega))

/-- **`Task.wholeStepBwd10` from what is left** at the spec's builtins. -/
theorem wholeStepBwd10_of_rest
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRest10 (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 :=
  wholeStepBwd10_of_parts fun H hn hinj host nd r => bwdParts10_of_rest (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim10.Whole
