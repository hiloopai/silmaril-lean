module

public import Silmaril.Wasm.SpecTec.Sim10.Whole.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Transfer
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwd

/-!
# The wasm-1.0 reduction relations: closedness and the five structural rules of `Step`

* `closed_step10`: `Step`, `Step_pure` and `Step_read` of the wasm-1.0 script form a closed set (no
  rule conclusion has an empty-domain option iteration, and the premises consult only these three
  relations), checked by kernel `rfl`. So on `Step` the Round 6 backend reading is the declarative
  reading (`sstepB10_iff`), as for 2.0 (`Sim20.Whole.sstepB20_iff`).
* `pureRule10`, `readRule10`, `ctxtLabelRule10`, `ctxtFrameRule10`, `ctxtInstrsRule10`: rules 0–4
  of 1.0's `Step`, transcribed, with their provenance in `simEnv10 B` by kernel `rfl`
  (`hasRuleAt_pure10`, …). Unlike 2.0's, they type their code as `admininstr*` (2.0 writes
  `instr*` and coerces), 1.0 has `ctxt-instrs` (2.0 lost it), and 1.0's `ctxt-frame` lets the inner
  frame change (2.0 keeps it).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (iterPat)
open Silmaril.Wasm.SpecTec.Sim (SStep)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB closedB Closed closed_of_closedB
  closed_congr dderivesB_otherwise_iff_of_closed)

variable (B : Builtins)

set_option maxRecDepth 100000

/-! ## Closedness -/

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step`, `Step_pure` and `Step_read` are closed in the wasm-1.0 script. -/
theorem closedB_step10 :
    closedB (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed)
      ["Step", "Step_pure", "Step_read"] = true := by
  rfl

/-- The three reduction relations are closed in `simEnv10 B`. -/
theorem closed_step10 : Closed (simEnv10 B) (· ∈ ["Step", "Step_pure", "Step_read"]) :=
  closed_congr (fun _ => rfl) (closed_of_closedB closedB_step10)

/-- **On wasm-1.0's `Step` the backend reading is the declarative reading.** -/
theorem sstepB10_iff {c c' : Value} : SStepB (simEnv10 B) c c' ↔ SStep (simEnv10 B) c c' :=
  dderivesB_otherwise_iff_of_closed (closed_step10 B) (by simp)

/-! ## The structural rules, transcribed -/

/-- `admininstr*`. -/
abbrev adminsT : Typ := .iterT (.varT "admininstr" []) .list

/-- `z; code`. -/
def cfgE (z code : Exp) : Exp := .caseE "%;%" (.tupE [z, code])

/-- A premise `rel: l ~> r`. -/
def premE (rel : IL.Id) (l r : Exp) : Prem := .rulePr rel [] "%~>%" (.tupE [l, r])

/-- `Step/pure`, rule 0 of 1.0's `Step`. -/
def pureRule10 : Rule :=
  .ruleD "pure" [.expP "z" (.varT "state" []), .expP "admininstr*" adminsT,
      .expP "admininstr'*" adminsT] "%~>%"
    (.tupE [cfgE (.varE "z") (iterPat "admininstr" "admininstr*"),
      cfgE (.varE "z") (iterPat "admininstr'" "admininstr'*")])
    [premE "Step_pure" (iterPat "admininstr" "admininstr*") (iterPat "admininstr'" "admininstr'*")]

/-- `Step/read`, rule 1 of 1.0's `Step`. -/
def readRule10 : Rule :=
  .ruleD "read" [.expP "z" (.varT "state" []), .expP "admininstr*" adminsT,
      .expP "admininstr'*" adminsT] "%~>%"
    (.tupE [cfgE (.varE "z") (iterPat "admininstr" "admininstr*"),
      cfgE (.varE "z") (iterPat "admininstr'" "admininstr'*")])
    [premE "Step_read" (cfgE (.varE "z") (iterPat "admininstr" "admininstr*"))
      (iterPat "admininstr'" "admininstr'*")]

/-- `Step/ctxt-label`, rule 2 of 1.0's `Step`. -/
def ctxtLabelRule10 : Rule :=
  .ruleD "ctxt-label" [.expP "z" (.varT "state" []), .expP "n" (.varT "n" []),
      .expP "instr_0*" (.iterT (.varT "instr" []) .list), .expP "admininstr*" adminsT,
      .expP "z'" (.varT "state" []), .expP "admininstr'*" adminsT] "%~>%"
    (.tupE [cfgE (.varE "z") (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n",
        iterPat "instr_0" "instr_0*", iterPat "admininstr" "admininstr*"])]),
      cfgE (.varE "z'") (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n",
        iterPat "instr_0" "instr_0*", iterPat "admininstr'" "admininstr'*"])])])
    [premE "Step" (cfgE (.varE "z") (iterPat "admininstr" "admininstr*"))
      (cfgE (.varE "z'") (iterPat "admininstr'" "admininstr'*"))]

/-- `s; f`. -/
def stE (s f : Exp) : Exp := .caseE "%;%" (.tupE [s, f])

/-- `Step/ctxt-frame`, rule 3 of 1.0's `Step`: the inner frame `f'` becomes `f''`. -/
def ctxtFrameRule10 : Rule :=
  .ruleD "ctxt-frame" [.expP "s" (.varT "store" []), .expP "f" (.varT "frame" []),
      .expP "n" (.varT "n" []), .expP "f'" (.varT "frame" []), .expP "admininstr*" adminsT,
      .expP "s'" (.varT "store" []), .expP "f''" (.varT "frame" []),
      .expP "admininstr'*" adminsT] "%~>%"
    (.tupE [cfgE (stE (.varE "s") (.varE "f")) (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n",
        .varE "f'", iterPat "admininstr" "admininstr*"])]),
      cfgE (stE (.varE "s'") (.varE "f")) (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n",
        .varE "f''", iterPat "admininstr'" "admininstr'*"])])])
    [premE "Step" (cfgE (stE (.varE "s") (.varE "f'")) (iterPat "admininstr" "admininstr*"))
      (cfgE (stE (.varE "s'") (.varE "f''")) (iterPat "admininstr'" "admininstr'*"))]

/-- `val*` coerced to `admininstr*`. -/
abbrev valsE10 : Exp :=
  Sim20.Whole.subIterPat "val" "val*" (.varT "val" []) (.varT "admininstr" [])

/-- `Step/ctxt-instrs`, rule 4 of 1.0's `Step`. -/
def ctxtInstrsRule10 : Rule :=
  .ruleD "ctxt-instrs" [.expP "z" (.varT "state" []), .expP "val*" (.iterT (.varT "val" []) .list),
      .expP "admininstr*" adminsT, .expP "admininstr_1*" adminsT, .expP "z'" (.varT "state" []),
      .expP "admininstr'*" adminsT] "%~>%"
    (.tupE [cfgE (.varE "z") (.catE valsE10 (.catE (iterPat "admininstr" "admininstr*")
        (iterPat "admininstr_1" "admininstr_1*"))),
      cfgE (.varE "z'") (.catE valsE10 (.catE (iterPat "admininstr'" "admininstr'*")
        (iterPat "admininstr_1" "admininstr_1*")))])
    [premE "Step" (cfgE (.varE "z") (iterPat "admininstr" "admininstr*"))
      (cfgE (.varE "z'") (iterPat "admininstr'" "admininstr'*")),
     .ifPr (.binE .orOp .boolT (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "admininstr_1" "admininstr_1*") (.listE [])))]

theorem hasRuleAt_pure10 : HasRuleAt (simEnv10 B) "Step" "%~>%" 0 pureRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_read10 : HasRuleAt (simEnv10 B) "Step" "%~>%" 1 readRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_ctxtLabel10 : HasRuleAt (simEnv10 B) "Step" "%~>%" 2 ctxtLabelRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_ctxtFrame10 : HasRuleAt (simEnv10 B) "Step" "%~>%" 3 ctxtFrameRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_ctxtInstrs10 : HasRuleAt (simEnv10 B) "Step" "%~>%" 4 ctxtInstrsRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure` is a relation without parameters. -/
theorem findRel_pure10 :
    ∃ t rules, (simEnv10 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩

/-- `Step_read` is a relation without parameters. -/
theorem findRel_read10 :
    ∃ t rules, (simEnv10 B).findRel? "Step_read" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩

/-- `Step` is a relation without parameters. -/
theorem findRel_step10 :
    ∃ t rules, (simEnv10 B).findRel? "Step" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
