module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreNest10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdWhole10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.TypOff10

/-!
# Building firings of `simEnv10T` (track v10)

The forward leaves of rounds 2–4 (`fwdAt10_*`) build firings of `simEnv10 B` from the typings of
`FwdAt10`, which are `simEnv10` typings and so exclude every state whose store holds a storing
function. This module gives what is needed to build the same firings in `simEnv10T B` instead:

* **`fires_of_ruleAtT`**: a rule of `simEnv10 B` fires in `simEnv10T B` at an assignment whose
  quantifiers are typed in `simEnv10T`, when its left-hand side, right-hand side and premises
  evaluate in `simEnv10` and its premises consult no relation and no `otherwise` (`plainB`,
  checked on the rule term by `decide`). Evaluation moves by `envSame10T`.
* `sstep10_pureT`, `sstep10_readT`: `Step/pure` and `Step/read` in `simEnv10T`; `spure10T_of_fires`,
  `sread10T_of_fires`, `fwdAt10T_of_spure`, `fwdAt10T_of_spure'`, `fwdAt10T_of_sread`: round 2's
  plumbing at `FwdAt10T`.
* `typedV10T`: a `simEnv10` typing is a `simEnv10T` typing (typing grows, `hasTypT`).
* `adminT_lift`, `instrT_lift`: the `admininstr` and `instr` declarations of `simEnv10T` are those
  of `simEnv10` with `fixCase10` applied, and `fixCase10` keeps every case other than `STORE`
  (`findCase_map_fixCase10`); `findTypT_ne` moves every other type declaration.
* the code-typing inversions of `FwdLeaf` in `simEnv10T` (`typedV_idx_of_case10T`,
  `typedV_head10T`, `typedV_second10T`, `typedV_val_of_head10T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config value)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat iterPat)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW DDerives otherwise SStep SRead SPure cfgV
  TypedV ValsOnly stateT nT dderives_of_ruleAt evalExp_tup2 evalExp_case prems_one
  typedV_list_iff dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixCase10)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (hasRuleAtT hasTypT envSame10T findTyp?_simEnv10T_ne
  findTyp_adminT findTyp_admin10 findTyp_instr10 findCase_map_fixCase10 adminCases10
  instrCases10)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (evalExp_of plainB premW_of_plain)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (GoodT goodT_of_all tyEvB)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Firings -/

/-- Plain premises of `simEnv10` hold in `simEnv10T`, under any reading. -/
theorem prems_fwd10T {ρ : VarEnv} {prems : List Prem} {D₁ D₂ : Sim.Interp} {els₁ els₂ : Prop}
    (hp : ∀ pr ∈ prems, PremW (simEnv10 B) D₁ els₁ ρ pr) (hok : prems.all plainB = true) :
    ∀ pr ∈ prems, PremW (simEnv10T B) D₂ els₂ ρ pr :=
  fun pr hm => premW_of_plain (envSame10T B) (hp pr hm) (List.all_eq_true.1 hok pr hm)

/-- **Build a firing of `simEnv10T` from `simEnv10` evaluations and `simEnv10T` typings.** -/
theorem fires_of_ruleAtT {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} (h : HasRuleAt (simEnv10 B) x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (σ : List (IL.Id × Value)) {v : Value}
    (hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW (simEnv10 B) (DDerives (simEnv10 B) (otherwise (simEnv10 B)))
      (otherwise (simEnv10 B) x [] k v) (VarEnv.empty.bindVals σ) pr)
    (hok : prems.all plainB = true := by decide) :
    Fires (simEnv10T B) x k v :=
  Sim20.Pure.fires_of_ruleAt (hasRuleAtT h) σ hq (evalExp_of (envSame10T B) he)
    (prems_fwd10T hp hok)

/-- A typing in `simEnv10` is one in `simEnv10T`. -/
theorem typedV10T {t : Typ} {v : Value} (h : TypedV (simEnv10 B) t v) : TypedV (simEnv10T B) t v :=
  fun ρ hρ => hasTypT (h ρ hρ)

/-! ## `Step/pure` and `Step/read` in `simEnv10T` -/

/-- **`Step/pure`** in `simEnv10T`. -/
theorem sstep10_pureT {z : Value} {is js : List Value} (hz : TypedV (simEnv10T B) stateT z)
    (his : TypedV (simEnv10T B) adminsT (.list is)) (hjs : TypedV (simEnv10T B) adminsT (.list js))
    (hp : SPure (simEnv10T B) is js) : SStep (simEnv10T B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("admininstr*", .list is), ("admininstr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fj : ρ.findVal? "admininstr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv10T B) ρ
      [.expP "z" stateT, .expP "admininstr*" adminsT, .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv10T B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv10T B) ρ (iterPat "admininstr'" "admininstr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  exact dderives_of_ruleAt (hasRuleAtT (hasRuleAt_pure10 B)) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (Sim.evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (Sim.evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ei ej) hp))

/-- **`Step/read`** in `simEnv10T`. -/
theorem sstep10_readT {z : Value} {is js : List Value} (hz : TypedV (simEnv10T B) stateT z)
    (his : TypedV (simEnv10T B) adminsT (.list is)) (hjs : TypedV (simEnv10T B) adminsT (.list js))
    (hp : SRead (simEnv10T B) (cfgV z is) js) : SStep (simEnv10T B) (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("admininstr*", .list is), ("admininstr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fj : ρ.findVal? "admininstr'*" = some (.list js) := rfl
  have hq : QuantsOk (simEnv10T B) ρ
      [.expP "z" stateT, .expP "admininstr*" adminsT, .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp (simEnv10T B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp (simEnv10T B) ρ (iterPat "admininstr'" "admininstr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have ec : EvalExp (simEnv10T B) ρ (cfgE (.varE "z") (iterPat "admininstr" "admininstr*"))
      (cfgV z is) :=
    evalExp_case (op := "%;%") (evalExp_tup2 (Sim.evalExp_var fz) ei)
  exact dderives_of_ruleAt (hasRuleAtT (hasRuleAt_read10 B)) _ hq
    (evalExp_tup2 ec (evalExp_case (op := "%;%") (evalExp_tup2 (Sim.evalExp_var fz) ej)))
    (prems_one (.rulePr Equiv.evalArgs_nil (evalExp_tup2 ec ej) hp))

/-- A firing of 1.0's `Step_pure` in `simEnv10T` is a `Step_pure` step there. -/
theorem spure10T_of_fires {k : Nat} {is js : List Value}
    (hf : Fires (simEnv10T B) "Step_pure" k (.tuple [.list is, .list js])) :
    SPure (simEnv10T B) is js := by
  obtain ⟨t, rules, hrel⟩ := findRel_pure10T (B := B)
  exact (dderives_iff_fires hrel).2 ⟨k, hf⟩

/-- A firing of 1.0's `Step_read` in `simEnv10T` is a `Step_read` step there. -/
theorem sread10T_of_fires {k : Nat} {c : Value} {js : List Value}
    (hf : Fires (simEnv10T B) "Step_read" k (.tuple [c, .list js])) :
    SRead (simEnv10T B) c js := by
  obtain ⟨t, rules, hrel⟩ := findRel_read10T (B := B)
  exact (dderives_iff_fires hrel).2 ⟨k, hf⟩

/-- A firing of 1.0's `Step` in `simEnv10T` is a step there. -/
theorem sstepB10T_of_fires' {k : Nat} {v w : Value}
    (hf : Fires (simEnv10T B) "Step" k (.tuple [v, w])) : SStepB (simEnv10T B) v w :=
  StoreAgree.sstepB10T_of_fires hf

/-- A `Step_pure` step between the codes gives `FwdAt10T` at a fixed state. -/
theorem fwdAt10T_of_spure {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : SPure (simEnv10T B) (adminsToV code) (adminsToV code')) :
    FwdAt10T B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (StoreFix.sstepB10T_iff B).2 (sstep10_pureT hz hc hc' hp)

/-- A `Step_pure` step between the codes, given the typing of the code, gives `FwdAt10T`. -/
theorem fwdAt10T_of_spure' {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : TypedV (simEnv10T B) adminsT (.list (adminsToV code)) →
      SPure (simEnv10T B) (adminsToV code) (adminsToV code')) :
    FwdAt10T B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (StoreFix.sstepB10T_iff B).2 (sstep10_pureT hz hc hc' (hp hc))

/-- A `Step_read` step from the configuration gives `FwdAt10T` at a fixed state. -/
theorem fwdAt10T_of_sread {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : TypedV (simEnv10T B) stateT (stateV hn s f) →
      TypedV (simEnv10T B) adminsT (.list (adminsToV code)) →
      SRead (simEnv10T B) (configV hn ⟨s, f, code⟩) (adminsToV code')) :
    FwdAt10T B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (StoreFix.sstepB10T_iff B).2 (sstep10_readT hz hc hc' (hp hz hc))

/-! ## The type declarations of `simEnv10T` -/

/-- Every type declaration other than `instr` and `admininstr` is that of `simEnv10`. -/
theorem findTypT_ne {y : IL.Id} {d : List Param × List Inst}
    (h : (simEnv10 B).findTyp? y = some d) (h₁ : y ≠ "instr" := by decide)
    (h₂ : y ≠ "admininstr" := by decide) : (simEnv10T B).findTyp? y = some d :=
  (findTyp?_simEnv10T_ne B h₁ h₂).trans h

/-- `admininstr` in `simEnv10T`: the cases of `simEnv10`, with `fixCase10`. -/
theorem adminT_lift {cs : List TypCase}
    (h : (simEnv10 B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)])) :
    (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT (cs.map fixCase10))]) := by
  rw [findTyp_admin10 B] at h
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Inst.instD.injEq,
    DefTyp.variantT.injEq, true_and, and_true] at h
  subst h
  exact findTyp_adminT B

/-- `instr` in `simEnv10T`: the cases of `simEnv10`, with `fixCase10`. -/
theorem instrT_lift {cs : List TypCase}
    (h : (simEnv10 B).findTyp? "instr" = some ([], [.instD [] [] (.variantT cs)])) :
    (simEnv10T B).findTyp? "instr" =
      some ([], [.instD [] [] (.variantT (cs.map fixCase10))]) := by
  rw [findTyp_instr10 B] at h
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Inst.instD.injEq,
    DefTyp.variantT.injEq, true_and, and_true] at h
  subst h
  have ht := (StoreAgree.simEnv10T_tables B).1
  have h0 := findTyp_instr10 B
  simp only [Env.findTyp?] at h0
  simp only [Env.findTyp?, ht, Sim20.StoreAgree.find?_map_repl]
  simp [h0]

/-- `fixCase10` keeps a case other than `STORE`. -/
theorem findCaseT {cs : List TypCase} {op : MixopS} {p : Typ × List Prem}
    (h : findCase cs op = some p) (hop : op ≠ "STORE") :
    findCase (cs.map fixCase10) op = some p :=
  (findCase_map_fixCase10 op hop cs).trans h

/-! ## The inversions of `FwdLeaf` in `simEnv10T` -/

theorem findTyp_admininstr10_idxT : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCase cs "LOCAL.GET" = some (.varT "localidx" [], []) ∧
    findCase cs "LOCAL.SET" = some (.varT "localidx" [], []) ∧
    findCase cs "GLOBAL.GET" = some (.varT "globalidx" [], []) ∧
    findCase cs "CALL" = some (.varT "funcidx" [], []) :=
  let ⟨_, h, h₁, h₂, h₃, h₄⟩ := findTyp_admininstr10_idx (B := B)
  ⟨_, adminT_lift h, findCaseT h₁ (by decide), findCaseT h₂ (by decide), findCaseT h₃ (by decide),
    findCaseT h₄ (by decide)⟩

theorem findTyp_admininstr10_teeT : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCase cs "LOCAL.TEE" = some (.varT "localidx" [], []) :=
  let ⟨_, h, h₁⟩ := findTyp_admininstr10_tee (B := B)
  ⟨_, adminT_lift h, findCaseT h₁ (by decide)⟩

theorem findTyp_localidx10T : (simEnv10T B).findTyp? "localidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := findTypT_ne findTyp_localidx10
theorem findTyp_globalidx10T : (simEnv10T B).findTyp? "globalidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := findTypT_ne findTyp_globalidx10
theorem findTyp_funcidx10T : (simEnv10T B).findTyp? "funcidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := findTypT_ne findTyp_funcidx10

/-- **An index carried by an instruction typed in `simEnv10T` is a typed `idx`.** -/
theorem typedV_idx_of_case10T {cs : List TypCase} {op : MixopS} {y : IL.Id} {w : Value}
    (htd : (simEnv10T B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]))
    (hc : findCase cs op = some (.varT y [], []))
    (hy : (simEnv10T B).findTyp? y = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]))
    (h : TypedV (simEnv10T B) adminT10 (.case op w)) : TypedV (simEnv10T B) (.varT "idx" []) w :=
  typedV_of_scope valsOnly_empty (hasTyp_closedAlias_inv valsOnly_empty hy
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc))

/-- The first element of typed code is a typed `admininstr`. -/
theorem typedV_head10T {a : Admin} {l : List Admin}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV (a :: l)))) :
    TypedV (simEnv10T B) adminT10 (adminToV a) :=
  typedV_list_iff.1 h _ (.head _)

/-- The second element of typed code is a typed `admininstr`. -/
theorem typedV_second10T {a b : Admin} {l : List Admin}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV (a :: b :: l)))) :
    TypedV (simEnv10T B) adminT10 (adminToV b) :=
  typedV_list_iff.1 h _ (.tail _ (.head _))

/-- A V1 value at the head of typed code is a typed `val`. -/
theorem typedV_val_of_head10T {v : Execution.Runtime.Value} {l : List Admin}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV (value v :: l)))) :
    TypedV (simEnv10T B) (.varT "val" []) (valV v) := by
  have ha : TypedV (simEnv10T B) adminT10 (adminToV (value v)) := typedV_head10T h
  rw [adminToV_value] at ha
  exact typedV_val_of_admin10T (w := .tuple [valTypeV v.type, numV v]) ha

/-! ## Typings off `tbad10` move back -/

/-- **A typing in `simEnv10T` at a type off `tbad10` is one in `simEnv10`.** -/
theorem typedV_off10T {t : Typ} {v : Value} (hg : GoodT StoreAgree.tbad10 (evTyp t))
    (h : TypedV (simEnv10T B) t v) : TypedV (simEnv10 B) t v :=
  fun ρ hρ => (StoreAgree.hasTyp_off10T B hρ.1 hg).1 (h ρ hρ)

/-- **An instruction typed in `simEnv10T` whose payload type avoids `tbad10` is typed in
`simEnv10`.** So every leaf redex without nested code moves back. -/
theorem typedV_admin_back10T {cs : List TypCase} {op : MixopS} {t : Typ} {w : Value}
    (htd : (simEnv10 B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]))
    (hc : findCase cs op = some (t, [])) (hop : op ≠ "STORE")
    (hg : GoodT StoreAgree.tbad10 (evTyp t)) (h : TypedV (simEnv10T B) adminT10 (.case op w)) :
    TypedV (simEnv10 B) adminT10 (.case op w) :=
  Sim20.Pure.typedV_closedCase20 htd hc ((StoreAgree.hasTyp_off10T B rfl hg).1
    (hasTyp_closedVariant_inv valsOnly_empty (adminT_lift htd) (h _ valsOnly_empty)
      (findCaseT hc hop)))

/-- A V1 value typed as an instruction in `simEnv10T` is typed so in `simEnv10`. -/
theorem typedV_valAdmin_back10T {v : Execution.Runtime.Value}
    (h : TypedV (simEnv10T B) adminT10 (valV v)) : TypedV (simEnv10 B) adminT10 (valV v) := by
  obtain ⟨cs, htd, hc, -, -⟩ := findTyp_admininstr10F (B := B)
  exact typedV_admin_back10T (w := .tuple [valTypeV v.type, numV v]) htd hc (by decide)
    (goodT_of_all (by decide)) h

/-- Every arity is a typed `n` in `simEnv10T`. -/
theorem typedV_n10T (k : Nat) : TypedV (simEnv10T B) nT (.num (.natN k)) :=
  typedV10T (typedV_n10 k)

end Silmaril.Wasm.SpecTec.Sim10.Whole
