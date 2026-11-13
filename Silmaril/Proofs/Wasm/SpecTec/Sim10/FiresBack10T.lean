module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdBoth
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreBwd10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.TypOff10
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreeMove

/-!
# Firings of `simEnv10T` read back in `simEnv10` (track v10)

`simEnv10T B` is `simEnv10 B` with the `STORE` erratum: the type declarations `instr` and
`admininstr` are corrected, nothing else changes. The evaluator cannot tell the two apart
(`envSame10T`), and off the thirteen types `tbad10` that reach `instr` or `admininstr` they type
alike (`hasTyp_off10T`). So a firing of a rule in `simEnv10T` is a firing in `simEnv10` as soon as
the rule's quantifiers avoid `tbad10` and its premises consult no relation and no `otherwise`
(`ruleOffB`):

* **`fires_back10T`**: such a firing moves back unchanged. This covers the 1.0 `Step_pure` rules
  whose quantifiers are values, immediates and frames (`unreachable` … `local.tee`, the numeric
  rules). Their round 2–4 leaf lemmas apply as they stand.

The other leaf rules quantify a `tbad10` type: every `Step` and `Step_read` rule binds `z : state`,
and the control rules of `Step_pure` bind `instr*` or `admininstr*`. Their firings cannot move
back as firings (a state whose store holds a storing function is typed in `simEnv10T` only), but
everything their round 2–4 proofs use does:

* **`firesPure10_invT`**, **`firesCfg10_invT`**: a firing in `simEnv10T` inverted, with the
  evaluations and premises read in `simEnv10` and the quantifier typing kept in `simEnv10T`. These
  have the shape 's `firesPure10_inv` and `firesCfg10_inv`, so the leaf proofs re-run
  over them (`BwdLeaf10T`).
* `val10_of_varT`, `quantsOk_back10T`: the typing the leaf proofs read (`val` and other types off
  `tbad10`), moved back.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Config value)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW DDerives otherwise)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (tbad10 hasTyp_off10T hasTyp_val10T hasRuleAtT
  evalExps_back evalExp_back envSame10T)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB GoodT relFreeB premW_back)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (hasElseB)

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## Rules whose firings move back -/

/-- A quantifier whose type avoids `tbad10`. -/
def paramOffB : Param → Bool
  | .expP _ t => (evTyp t).all (tyEvB tbad10)
  | _ => true

/-- A premise that consults no relation and no `otherwise`. -/
def premOkB (pr : Prem) : Bool := relFreeB pr && !hasElseB pr

/-- A rule whose quantifiers avoid `tbad10` and whose premises are evaluations only. -/
def ruleOffB : Rule → Bool
  | .ruleD _ qs _ _ prems => qs.all paramOffB && prems.all premOkB

/-- **Quantifier typing off `tbad10` moves back.** -/
theorem quantsOk_back10T {ρ : VarEnv} (hρ : ρ.typs = []) {qs : List Param}
    (hq : QuantsOk (simEnv10T B) ρ qs) (hoff : qs.all paramOffB = true) :
    QuantsOk (simEnv10 B) ρ qs := by
  intro x t hm
  obtain ⟨w, hw, ht⟩ := hq x t hm
  have hg : GoodT tbad10 (evTyp t) := by
    have h := List.all_eq_true.1 hoff _ hm
    exact fun e he => List.all_eq_true.1 h e he
  exact ⟨w, hw, (hasTyp_off10T B hρ hg).1 ht⟩

/-- **Evaluation-only premises move back**, under any reading of relations and `otherwise`. -/
theorem prems_back10T {ρ : VarEnv} {prems : List Prem} {D₁ D₂ : Sim.Interp} {els₁ els₂ : Prop}
    (hp : ∀ pr ∈ prems, PremW (simEnv10T B) D₂ els₂ ρ pr) (hok : prems.all premOkB = true) :
    ∀ pr ∈ prems, PremW (simEnv10 B) D₁ els₁ ρ pr := by
  intro pr hm
  have h := List.all_eq_true.1 hok pr hm
  simp only [premOkB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact premW_back (envSame10T B) (hp pr hm) h.1 fun he => absurd he (by simp [h.2])

/-- **A firing in `simEnv10T` of a rule that avoids `tbad10` is a firing in `simEnv10`.** -/
theorem fires_back10T {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} {v : Value}
    (h : HasRuleAt (simEnv10 B) x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (hf : Fires (simEnv10T B) x k v)
    (hr : ruleOffB (.ruleD nm qs "%~>%" e prems) = true := by decide) :
    Fires (simEnv10 B) x k v := by
  obtain ⟨σ, hq, he, hp⟩ := Sim20.Pure.fires_inv (hasRuleAtT h) hf
  simp only [ruleOffB, Bool.and_eq_true] at hr
  exact Sim20.Pure.fires_of_ruleAt h σ
    (quantsOk_back10T (Sim.valsOnly_bindVals σ).1 hq hr.1)
    (evalExp_back (envSame10T B) he) (prems_back10T hp hr.2)

/-! ## Firings inverted, read in `simEnv10` -/

/-- **A firing `Step_pure` rule of `simEnv10T`, inverted in `simEnv10`**: round 2's
`firesPure10_inv` with the quantifier typing kept in `simEnv10T`. -/
theorem firesPure10_invT {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {is : List Admin} {w : Value}
    (h : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.listE es, rh]) prems))
    (hf : Fires (simEnv10T B) "Step_pure" k (.tuple [.list (adminsToV is), w]))
    (hok : prems.all premOkB = true := by decide) :
    ∃ σ, QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs ∧
      EvalExps (simEnv10 B) (VarEnv.empty.bindVals σ) es (adminsToV is) ∧
      EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW (simEnv10 B) (DDerives (simEnv10 B) (otherwise (simEnv10 B)))
        (otherwise (simEnv10 B) "Step_pure" [] k (.tuple [.list (adminsToV is), w]))
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAtT h) hf
  exact ⟨σ, hq, evalExps_back (envSame10T B) hes, evalExp_back (envSame10T B) hrh,
    prems_back10T hp hok⟩

variable {H : Type}

/-- **A firing rule `z; es ~> rh` of `simEnv10T` at a configuration, inverted in `simEnv10`**:
round 2's `firesCfg10_inv` with the quantifier typing kept in `simEnv10T`. -/
theorem firesCfg10_invT {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {es : List Exp} {rh : Exp} {prems : List Prem} {hn : H → String} {c : Config H} {w : Value}
    (h : HasRuleAt (simEnv10 B) x "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires (simEnv10T B) x k (.tuple [configV hn c, w]))
    (hok : prems.all premOkB = true := by decide) :
    ∃ σ, QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps (simEnv10 B) (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW (simEnv10 B) (DDerives (simEnv10 B) (otherwise (simEnv10 B)))
        (otherwise (simEnv10 B) x [] k (.tuple [configV hn c, w])) (VarEnv.empty.bindVals σ)
        pr := by
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAtT h) hf
  exact ⟨σ, hq, fz, evalExps_back (envSame10T B) hes, evalExp_back (envSame10T B) hrh,
    prems_back10T hp hok⟩

/-- **A coerced `val` variable of a left-hand side, at a scope typed in `simEnv10T`, is a V1
value**: round 2's `val10_of_var`, since `val` is off `tbad10`. -/
theorem val10_of_varT {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {a : Admin}
    (hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "val" []) ∈ qs)
    (h : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.subE (.varE x) (.varT "val" []) (.varT "admininstr" [])) (adminToV a)) :
    ∃ v, a = value v ∧ (VarEnv.empty.bindVals σ).findVal? x = some (valV v) := by
  obtain ⟨R, fR, tR⟩ := hq x _ hm
  have hq' : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) [.expP x (.varT "val" [])] := by
    intro y t hy
    simp only [List.mem_singleton, Param.expP.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨R, fR, (hasTyp_val10T B (Sim.valsOnly_bindVals σ).1).1 tR⟩
  exact val10_of_var hq' (List.mem_singleton_self _) h

/-! ## The rules past the end -/

theorem not_firesPure10T_ge {i : Nat} (hi : 29 ≤ i) {v : Value} :
    ¬ Fires (simEnv10T B) "Step_pure" i v :=
  not_fires_of_length (by rw [StoreAgree.findRel?_simEnv10T]; rfl) hi

theorem not_firesRead10T_ge {i : Nat} (hi : 13 ≤ i) {v : Value} :
    ¬ Fires (simEnv10T B) "Step_read" i v :=
  not_fires_of_length (by rw [StoreAgree.findRel?_simEnv10T]; rfl) hi

theorem not_firesStep10T_ge {i : Nat} (hi : 13 ≤ i) {v : Value} :
    ¬ Fires (simEnv10T B) "Step" i v :=
  not_fires_of_length (by rw [StoreAgree.findRel?_simEnv10T]; rfl) hi

end Silmaril.Wasm.SpecTec.Sim10.Whole
