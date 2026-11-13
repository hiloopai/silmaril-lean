module

public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.Thms

/-!
# Instruction typing of the wasm-3.0 script: the rules

The rules of `Instr_ok`, `Instrs_ok` and `Instrtype_ok` that the instruction-typing comorphism
(`Institution.Instr30`) fires, each located in `simEnv B` by a kernel `rfl` and copied verbatim
from `Raw/…/Scripts/Wasm30/Original/Part2.lean`:

* `Instr_ok/nop` (rule 0), `Instr_ok/unreachable` (rule 1), `Instr_ok/drop` (rule 2);
* `Instrtype_ok` (its only rule);
* `Instrs_ok/empty` (rule 0), `Instrs_ok/instr` (rule 1), `Instrs_ok/frame` (rule 4).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (listIterE ctxP)
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (resE listP varP)

variable {B : Builtins}

/-- `%(x*) ->_(y*) %(z*)`, an instruction type written with three list variables. -/
def itE (x y z : IL.Id) : Exp := .caseE "%->_%%" (.tupE [resE x, listIterE y, resE z])

/-- `%([]) ->_[] %([])`. -/
def itNilE : Exp :=
  .caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.listE []]), .listE [], .caseE "%" (.tupE [.listE []])])

set_option maxRecDepth 100000 in
/-- `Instr_ok/nop`. -/
theorem ruleAt_nop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 0
    (.ruleD "nop" [ctxP] "%|-%:%" (.tupE [.varE "C", .caseE "NOP" (.tupE []), itNilE]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `%(t_1*) ->_[] %(t_2*)`, the type of `unreachable`. -/
def itUnreachE : Exp := .caseE "%->_%%" (.tupE [resE "t_1", .listE [], resE "t_2"])

set_option maxRecDepth 100000 in
/-- `Instr_ok/unreachable`. -/
theorem ruleAt_unreachable : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 1
    (.ruleD "unreachable" [ctxP, listP "t_1*" "valtype", listP "t_2*" "valtype"] "%|-%:%"
      (.tupE [.varE "C", .caseE "UNREACHABLE" (.tupE []), itUnreachE])
      [.rulePr "Instrtype_ok" [] "%|-%:OK" (.tupE [.varE "C", itUnreachE])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `%([t]) ->_[] %([])`, the type of `drop`. -/
def itDropE : Exp :=
  .caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.listE [.varE "t"]]), .listE [],
    .caseE "%" (.tupE [.listE []])])

set_option maxRecDepth 100000 in
/-- `Instr_ok/drop`. -/
theorem ruleAt_drop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 2
    (.ruleD "drop" [ctxP, varP "t" "valtype"] "%|-%:%"
      (.tupE [.varE "C", .caseE "DROP" (.tupE []), itDropE])
      [.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "t"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The iteration of `Instrtype_ok`'s locals premise. -/
def lctIt : IterExp := .mk .list [.mk "lct" (.varE "lct*"), .mk "x" (.varE "x*")]

/-- `Instrtype_ok`'s locals premise. -/
def lctPrem : Prem :=
  .iterPr (.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "LOCALS")
    (.projE (.uncaseE (.varE "x") "%") (0 : Int))) (.varE "lct"))) lctIt

set_option maxRecDepth 100000 in
/-- `Instrtype_ok`, its only rule. -/
theorem ruleAt_instrtypeOk : HasRuleAt (simEnv B) "Instrtype_ok" "%|-%:OK" 0
    (.ruleD "" [ctxP, listP "t_1*" "valtype", listP "x*" "idx", listP "t_2*" "valtype",
      listP "lct*" "localtype"] "%|-%:OK" (.tupE [.varE "C", itE "t_1" "x" "t_2"])
      [.rulePr "Resulttype_ok" [] "%|-%:OK" (.tupE [.varE "C", resE "t_1"]),
       .rulePr "Resulttype_ok" [] "%|-%:OK" (.tupE [.varE "C", resE "t_2"]), lctPrem]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instrs_ok/empty`. -/
theorem ruleAt_instrsEmpty : HasRuleAt (simEnv B) "Instrs_ok" "%|-%:%" 0
    (.ruleD "empty" [ctxP] "%|-%:%" (.tupE [.varE "C", .listE [], itNilE]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instrs_ok/instr`. -/
theorem ruleAt_instrsInstr : HasRuleAt (simEnv B) "Instrs_ok" "%|-%:%" 1
    (.ruleD "instr" [ctxP, varP "instr" "instr", listP "t_1*" "valtype", listP "x*" "idx",
      listP "t_2*" "valtype"] "%|-%:%" (.tupE [.varE "C", .listE [.varE "instr"], itE "t_1" "x" "t_2"])
      [.rulePr "Instr_ok" [] "%|-%:%" (.tupE [.varE "C", .varE "instr", itE "t_1" "x" "t_2"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30
