module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble6

/-!
# The 1.0 load and store rules the scalar builtins leave inert

The wasm-1.0 script declares `$bytes_` and `$ibytes_` `hint(builtin)` with no clause
(`findDef_bytes10`, `findDef_ibytes10`), and `Sim.Floats.floatIntB` answers neither
(`floatIntB_bytes10`). The premise of each of

* `Step_read` 9 `load-num-val` (`if $bytes_(t, c) = $mem(z, 0).BYTES[…]`),
* `Step_read` 11 `load-pack-val` (`if $ibytes_(n, c) = …`),
* `Step` 8 `store-num-val` (`if b* = $bytes_(t, c)`),
* `Step` 10 `store-pack-val` (`if b* = $ibytes_(n, $wrap__(…))`)

compares a call to one of them, so at `floatIntB` none of the four fires (`not_fires_loadNumVal10`,
…). Backwards these obligations hold vacuously. As for 2.0 (`Sim20.Whole.not_fires_inert`), this
is a fact about `floatIntB`, not about the script: under builtins answering `$bytes_` the rules
fire, and the forward half needs them to.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (Fires)

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## The byte primitives -/

theorem findDef_bytes10 : ∃ ps t, (simEnv10 B).findDef? "bytes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

theorem findDef_ibytes10 : ∃ ps t, (simEnv10 B).findDef? "ibytes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

/-- `floatIntB` answers neither byte primitive. -/
theorem floatIntB_bytes10 (P : Profile) {f : IL.Id} (hf : f = "bytes_" ∨ f = "ibytes_")
    (ws : List ArgV) : (Sim.Floats.floatIntB P).call f ws = none := by
  have hn : f ∉ Sim.Floats.floatNames := by
    rcases hf with rfl | rfl <;> decide
  simp only [Sim.Floats.floatIntB, hn, ↓reduceIte]
  rcases hf with rfl | rfl <;>
  · unfold Sim.IntNumeric.intCall
    split <;> simp_all

/-- **A call to a byte primitive denotes nothing** at `floatIntB`. -/
theorem not_evalExp_bytes10 {P : Profile} {f : IL.Id} (hf : f = "bytes_" ∨ f = "ibytes_")
    {args : List Arg} {σ : List (IL.Id × Value)} {v : Value} :
    ¬ EvalExp (simEnv10 (Sim.Floats.floatIntB P)) (VarEnv.empty.bindVals σ) (.callE f args) v := by
  intro h
  obtain ⟨ps, t, hd⟩ : ∃ ps t, (simEnv10 (Sim.Floats.floatIntB P)).findDef? f = some (ps, t, []) := by
    rcases hf with rfl | rfl
    · exact findDef_bytes10
    · exact findDef_ibytes10
  have hb : ∀ ws, (simEnv10 (Sim.Floats.floatIntB P)).builtins.call f ws = none := by
    intro ws
    simp only [simEnv10, Env.builtins_withBuiltins]
    exact floatIntB_bytes10 P hf ws
  exact Equiv.ExecBuiltins.not_callDef_of_nil rfl hd hb (evalExp_callE_iff.1 h)

/-- A rule whose one premise compares a call to a byte primitive (on either side) never fires at
`floatIntB`. -/
theorem not_fires_bytes10 {P : Profile} {x nm : IL.Id} {k : Nat} {qs : List Param} {e a : Exp}
    {f : IL.Id} {args : List Arg} (hf : f = "bytes_" ∨ f = "ibytes_") (left : Bool)
    (hr : HasRuleAt (simEnv10 (Sim.Floats.floatIntB P)) x "%~>%" k (.ruleD nm qs "%~>%" e
      [.ifPr (if left then .cmpE .eqOp .boolT (.callE f args) a
        else .cmpE .eqOp .boolT a (.callE f args))])) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) x k v := by
  intro hfi
  obtain ⟨σ, -, -, hp⟩ := Sim.State.Fires.rule_eq hr hfi
  have hpr := Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))
  cases left with
  | true =>
    obtain ⟨u₁, u₂, e₁, -, -⟩ := evalExp_cmpE_iff.1 hpr
    exact not_evalExp_bytes10 hf e₁
  | false =>
    obtain ⟨u₁, u₂, -, e₂, -⟩ := evalExp_cmpE_iff.1 hpr
    exact not_evalExp_bytes10 hf e₂

/-! ## The four rules -/

theorem hasRuleAt10_loadNumVal : ∃ qs e args a, HasRuleAt (simEnv10 B) "Step_read" "%~>%" 9
    (.ruleD "load-num-val" qs "%~>%" e [.ifPr (.cmpE .eqOp .boolT (.callE "bytes_" args) a)]) :=
  ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt10_loadPackVal : ∃ qs e args a, HasRuleAt (simEnv10 B) "Step_read" "%~>%" 11
    (.ruleD "load-pack-val" qs "%~>%" e [.ifPr (.cmpE .eqOp .boolT (.callE "ibytes_" args) a)]) :=
  ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt10_storeNumVal : ∃ qs e args a, HasRuleAt (simEnv10 B) "Step" "%~>%" 8
    (.ruleD "store-num-val" qs "%~>%" e [.ifPr (.cmpE .eqOp .boolT a (.callE "bytes_" args))]) :=
  ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt10_storePackVal : ∃ qs e args a, HasRuleAt (simEnv10 B) "Step" "%~>%" 10
    (.ruleD "store-pack-val" qs "%~>%" e [.ifPr (.cmpE .eqOp .boolT a (.callE "ibytes_" args))]) :=
  ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩

/-- **`Step_read/load-num-val` never fires at `floatIntB`.** -/
theorem not_fires_loadNumVal10 (P : Profile) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) "Step_read" 9 v := by
  obtain ⟨qs, e, args, a, hr⟩ := hasRuleAt10_loadNumVal (B := Sim.Floats.floatIntB P)
  exact not_fires_bytes10 (.inl rfl) true hr v

/-- **`Step_read/load-pack-val` never fires at `floatIntB`.** -/
theorem not_fires_loadPackVal10 (P : Profile) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) "Step_read" 11 v := by
  obtain ⟨qs, e, args, a, hr⟩ := hasRuleAt10_loadPackVal (B := Sim.Floats.floatIntB P)
  exact not_fires_bytes10 (.inr rfl) true hr v

/-- **`Step/store-num-val` never fires at `floatIntB`.** -/
theorem not_fires_storeNumVal10 (P : Profile) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) "Step" 8 v := by
  obtain ⟨qs, e, args, a, hr⟩ := hasRuleAt10_storeNumVal (B := Sim.Floats.floatIntB P)
  exact not_fires_bytes10 (.inl rfl) false hr v

/-- **`Step/store-pack-val` never fires at `floatIntB`.** -/
theorem not_fires_storePackVal10 (P : Profile) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) "Step" 10 v := by
  obtain ⟨qs, e, args, a, hr⟩ := hasRuleAt10_storePackVal (B := Sim.Floats.floatIntB P)
  exact not_fires_bytes10 (.inr rfl) false hr v

end Silmaril.Wasm.SpecTec.Sim10.Whole
