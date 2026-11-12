module

public import Silmaril.Wasm.SpecTec.Sim20.Encode.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# SpecTec 2.0 ↔ V2: the `Step_pure` rules, rule by rule

The rule-level correspondence of `docs/projects/spectec/README.md` §1.5, level 2, for the control and numeric
families of `Step_pure` (rules 0–27 of `Scripts.Wasm20.fixed`).

* The rules themselves, **verbatim** from the generated script (`Scripts.Wasm20.Original.d365`;
  the 2.0 errata do not touch `Step_pure`): `unreachableRule` … `cvtopTrapRule`. Their
  provenance in `simEnv20 B` is a kernel `rfl` (`Sim20.Pure.Thms`).
* `PureRule`, the 28 rules, with `PureRule.idx`.
* `PureAt P r a b`: V2's `PureStep` restricted to the constructor that transcribes rule `r`
  (`Silmaril.Wasm.V2.Execution.Step` is transcribed one constructor per rule, so rule `r` of
  the script should be constructor `r`). `PureAt.toPureStep` and `PureStep.pureAt` relate it to
  `PureStep`.
* `NumAgree`, the hypothesis the numeric rules need: the script's `$unop_`, `$binop_`,
  `$testop_`, `$relop_` and `$cvtop__`, under the builtins of the environment, return exactly
  V2's results. It is the 2.0 counterpart of what the Round 2–4 numeric tracks proved for 3.0,
  and is **not discharged** here.

The theorems (`Sim20.Pure.Thms`) read the script under the Round 6 backend reading
(`Round6.Reading.FiresB`, `SPureB`), which on `Step_pure` coincides with the declarative reading
(`Step_pure` is closed: `closedB_pure20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## IL types the rules quantify over -/

/-- `num_(I32)`. -/
abbrev i32T : Typ := .varT "num_" [.expA (.caseE "I32" (.tupE []))]
/-- `val`. -/
abbrev valT : Typ := .varT "val" []
/-- `val*`. -/
abbrev valsT : Typ := .iterT (.varT "val" []) .list
/-- `instr*`. -/
abbrev instrsT : Typ := .iterT (.varT "instr" []) .list
/-- `admininstr*`. -/
abbrev adminsT : Typ := .iterT (.varT "admininstr" []) .list
/-- `blocktype`. -/
abbrev blocktypeT : Typ := .varT "blocktype" []
/-- `labelidx`. -/
abbrev labelidxT : Typ := .varT "labelidx" []
/-- `labelidx*`. -/
abbrev labelidxsT : Typ := .iterT (.varT "labelidx" []) .list
/-- `valtype*?`. -/
abbrev valtypesOptT : Typ := .iterT (.iterT (.varT "valtype" []) .list) .opt
/-- `n`. -/
abbrev nT : Typ := .varT "n" []
/-- `frame`. -/
abbrev frameT : Typ := .varT "frame" []

/-! ## The rules, verbatim -/

/-- `Step_pure/unreachable`, rule 0 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def unreachableRule : Rule :=
    (Rule.ruleD "unreachable" [] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "UNREACHABLE" (Exp.tupE
    []))]), (Exp.listE [(Exp.caseE "TRAP" (Exp.tupE []))])]) [])

/-- `Step_pure/nop`, rule 1 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def nopRule : Rule :=
    (Rule.ruleD "nop" [] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "NOP" (Exp.tupE []))]),
    (Exp.listE [])]) [])

/-- `Step_pure/drop`, rule 2 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def dropRule : Rule :=
    (Rule.ruleD "drop" [(Param.expP "val" (Typ.varT "val" []))] "%~>%" (Exp.tupE [(Exp.listE
    [(Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])), (Exp.caseE
    "DROP" (Exp.tupE []))]), (Exp.listE [])]) [])

/-- `Step_pure/select-true`, rule 3 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def selectTrueRule : Rule :=
    (Rule.ruleD "select-true" [(Param.expP "val_1" (Typ.varT "val" [])), (Param.expP "val_2"
    (Typ.varT "val" [])), (Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32" (Exp.tupE
    [])))])), (Param.expP "t*?" (Typ.iterT (Typ.iterT (Typ.varT "valtype" []) Iter.list)
    Iter.opt))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.subE (Exp.varE "val_1") (Typ.varT "val" [])
    (Typ.varT "admininstr" [])), (Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT
    "admininstr" [])), (Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE
    "c")])), (Exp.caseE "SELECT" (Exp.iterE (Exp.iterE (Exp.varE "t") (IterExp.mk Iter.list
    [(Dom.mk "t" (Exp.varE "t*"))])) (IterExp.mk Iter.opt [(Dom.mk "t*" (Exp.varE "t*?"))])))]),
    (Exp.listE [(Exp.subE (Exp.varE "val_1") (Typ.varT "val" []) (Typ.varT "admininstr" []))])])
    [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.projE (Exp.uncaseE (Exp.varE "c") "%") (0 :
    Int)) (Exp.numE (Num.natN 0))))])

/-- `Step_pure/select-false`, rule 4 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def selectFalseRule : Rule :=
    (Rule.ruleD "select-false" [(Param.expP "val_1" (Typ.varT "val" [])), (Param.expP "val_2"
    (Typ.varT "val" [])), (Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32" (Exp.tupE
    [])))])), (Param.expP "t*?" (Typ.iterT (Typ.iterT (Typ.varT "valtype" []) Iter.list)
    Iter.opt))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.subE (Exp.varE "val_1") (Typ.varT "val" [])
    (Typ.varT "admininstr" [])), (Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT
    "admininstr" [])), (Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE
    "c")])), (Exp.caseE "SELECT" (Exp.iterE (Exp.iterE (Exp.varE "t") (IterExp.mk Iter.list
    [(Dom.mk "t" (Exp.varE "t*"))])) (IterExp.mk Iter.opt [(Dom.mk "t*" (Exp.varE "t*?"))])))]),
    (Exp.listE [(Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT "admininstr" []))])])
    [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.projE (Exp.uncaseE (Exp.varE "c") "%") (0 :
    Int)) (Exp.numE (Num.natN 0))))])

/-- `Step_pure/if-true`, rule 5 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def ifTrueRule : Rule :=
    (Rule.ruleD "if-true" [(Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32" (Exp.tupE
    [])))])), (Param.expP "bt" (Typ.varT "blocktype" [])), (Param.expP "instr_1*" (Typ.iterT
    (Typ.varT "instr" []) Iter.list)), (Param.expP "instr_2*" (Typ.iterT (Typ.varT "instr" [])
    Iter.list))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32"
    (Exp.tupE [])), (Exp.varE "c")])), (Exp.caseE "IF%%ELSE%" (Exp.tupE [(Exp.varE "bt"),
    (Exp.iterE (Exp.varE "instr_1") (IterExp.mk Iter.list [(Dom.mk "instr_1" (Exp.varE
    "instr_1*"))])), (Exp.iterE (Exp.varE "instr_2") (IterExp.mk Iter.list [(Dom.mk "instr_2"
    (Exp.varE "instr_2*"))]))]))]), (Exp.listE [(Exp.caseE "BLOCK" (Exp.tupE [(Exp.varE "bt"),
    (Exp.iterE (Exp.varE "instr_1") (IterExp.mk Iter.list [(Dom.mk "instr_1" (Exp.varE
    "instr_1*"))]))]))])]) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.projE (Exp.uncaseE
    (Exp.varE "c") "%") (0 : Int)) (Exp.numE (Num.natN 0))))])

/-- `Step_pure/if-false`, rule 6 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def ifFalseRule : Rule :=
    (Rule.ruleD "if-false" [(Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32"
    (Exp.tupE [])))])), (Param.expP "bt" (Typ.varT "blocktype" [])), (Param.expP "instr_1*"
    (Typ.iterT (Typ.varT "instr" []) Iter.list)), (Param.expP "instr_2*" (Typ.iterT (Typ.varT
    "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE
    [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE "c")])), (Exp.caseE "IF%%ELSE%" (Exp.tupE
    [(Exp.varE "bt"), (Exp.iterE (Exp.varE "instr_1") (IterExp.mk Iter.list [(Dom.mk "instr_1"
    (Exp.varE "instr_1*"))])), (Exp.iterE (Exp.varE "instr_2") (IterExp.mk Iter.list [(Dom.mk
    "instr_2" (Exp.varE "instr_2*"))]))]))]), (Exp.listE [(Exp.caseE "BLOCK" (Exp.tupE [(Exp.varE
    "bt"), (Exp.iterE (Exp.varE "instr_2") (IterExp.mk Iter.list [(Dom.mk "instr_2" (Exp.varE
    "instr_2*"))]))]))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.projE (Exp.uncaseE
    (Exp.varE "c") "%") (0 : Int)) (Exp.numE (Num.natN 0))))])

/-- `Step_pure/label-vals`, rule 7 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def labelValsRule : Rule :=
    (Rule.ruleD "label-vals" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "instr*" (Typ.iterT
    (Typ.varT "instr" []) Iter.list)), (Param.expP "val*" (Typ.iterT (Typ.varT "val" [])
    Iter.list))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "LABEL_%{%}%" (Exp.tupE [(Exp.varE
    "n"), (Exp.iterE (Exp.varE "instr") (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE
    "instr*"))])), (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT
    "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "val" (Exp.varE "val*"))]))]))]), (Exp.iterE
    (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk
    Iter.list [(Dom.mk "val" (Exp.varE "val*"))]))]) [])

/-- `Step_pure/br-zero`, rule 8 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def brZeroRule : Rule :=
    (Rule.ruleD "br-zero" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "instr'*" (Typ.iterT
    (Typ.varT "instr" []) Iter.list)), (Param.expP "val'*" (Typ.iterT (Typ.varT "val" [])
    Iter.list)), (Param.expP "val*" (Typ.iterT (Typ.varT "val" []) Iter.list)), (Param.expP
    "instr*" (Typ.iterT (Typ.varT "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.listE
    [(Exp.caseE "LABEL_%{%}%" (Exp.tupE [(Exp.varE "n"), (Exp.iterE (Exp.varE "instr'")
    (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))])), (Exp.catE (Exp.catE
    (Exp.catE (Exp.iterE (Exp.subE (Exp.varE "val'") (Typ.varT "val" []) (Typ.varT "admininstr"
    [])) (IterExp.mk Iter.list [(Dom.mk "val'" (Exp.varE "val'*"))])) (Exp.iterE (Exp.subE
    (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk (Iter.listN
    (Exp.varE "n") (@Option.none String)) [(Dom.mk "val" (Exp.varE "val*"))]))) (Exp.listE
    [(Exp.caseE "BR" (Exp.caseE "%" (Exp.tupE [(Exp.numE (Num.natN 0))])))])) (Exp.iterE
    (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk
    Iter.list [(Dom.mk "instr" (Exp.varE "instr*"))])))]))]), (Exp.catE (Exp.iterE (Exp.subE
    (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk (Iter.listN
    (Exp.varE "n") (@Option.none String)) [(Dom.mk "val" (Exp.varE "val*"))])) (Exp.iterE
    (Exp.subE (Exp.varE "instr'") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk
    Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))])))]) [])

/-- `Step_pure/br-succ`, rule 9 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def brSuccRule : Rule :=
    (Rule.ruleD "br-succ" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "instr'*" (Typ.iterT
    (Typ.varT "instr" []) Iter.list)), (Param.expP "val*" (Typ.iterT (Typ.varT "val" [])
    Iter.list)), (Param.expP "l" (Typ.varT "labelidx" [])), (Param.expP "instr*" (Typ.iterT
    (Typ.varT "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "LABEL_%{%}%"
    (Exp.tupE [(Exp.varE "n"), (Exp.iterE (Exp.varE "instr'") (IterExp.mk Iter.list [(Dom.mk
    "instr'" (Exp.varE "instr'*"))])), (Exp.catE (Exp.catE (Exp.iterE (Exp.subE (Exp.varE "val")
    (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "val"
    (Exp.varE "val*"))])) (Exp.listE [(Exp.caseE "BR" (Exp.caseE "%" (Exp.tupE [(Exp.binE
    BinOp.addOp (OpTyp.numT NumTyp.natT) (Exp.projE (Exp.uncaseE (Exp.varE "l") "%") (0 : Int))
    (Exp.numE (Num.natN 1)))])))])) (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr" [])
    (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE
    "instr*"))])))]))]), (Exp.catE (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" [])
    (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "val" (Exp.varE "val*"))]))
    (Exp.listE [(Exp.caseE "BR" (Exp.varE "l"))]))]) [])

/-- `Step_pure/br_if-true`, rule 10 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def brIfTrueRule : Rule :=
    (Rule.ruleD "br_if-true" [(Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32"
    (Exp.tupE [])))])), (Param.expP "l" (Typ.varT "labelidx" []))] "%~>%" (Exp.tupE [(Exp.listE
    [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE "c")])), (Exp.caseE
    "BR_IF" (Exp.varE "l"))]), (Exp.listE [(Exp.caseE "BR" (Exp.varE "l"))])]) [(Prem.ifPr
    (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.projE (Exp.uncaseE (Exp.varE "c") "%") (0 : Int))
    (Exp.numE (Num.natN 0))))])

/-- `Step_pure/br_if-false`, rule 11 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def brIfFalseRule : Rule :=
    (Rule.ruleD "br_if-false" [(Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32"
    (Exp.tupE [])))])), (Param.expP "l" (Typ.varT "labelidx" []))] "%~>%" (Exp.tupE [(Exp.listE
    [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE "c")])), (Exp.caseE
    "BR_IF" (Exp.varE "l"))]), (Exp.listE [])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
    (Exp.projE (Exp.uncaseE (Exp.varE "c") "%") (0 : Int)) (Exp.numE (Num.natN 0))))])

/-- `Step_pure/br_table-lt`, rule 12 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def brTableLtRule : Rule :=
    (Rule.ruleD "br_table-lt" [(Param.expP "i" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32"
    (Exp.tupE [])))])), (Param.expP "l*" (Typ.iterT (Typ.varT "labelidx" []) Iter.list)),
    (Param.expP "l'" (Typ.varT "labelidx" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST"
    (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE "i")])), (Exp.caseE "BR_TABLE"
    (Exp.tupE [(Exp.iterE (Exp.varE "l") (IterExp.mk Iter.list [(Dom.mk "l" (Exp.varE "l*"))])),
    (Exp.varE "l'")]))]), (Exp.listE [(Exp.caseE "BR" (Exp.idxE (Exp.iterE (Exp.varE "l")
    (IterExp.mk Iter.list [(Dom.mk "l" (Exp.varE "l*"))])) (Exp.projE (Exp.uncaseE (Exp.varE "i")
    "%") (0 : Int))))])]) [(Prem.ifPr (Exp.cmpE CmpOp.ltOp (OpTyp.numT NumTyp.natT) (Exp.projE
    (Exp.uncaseE (Exp.varE "i") "%") (0 : Int)) (Exp.lenE (Exp.iterE (Exp.varE "l") (IterExp.mk
    Iter.list [(Dom.mk "l" (Exp.varE "l*"))])))))])

/-- `Step_pure/br_table-ge`, rule 13 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def brTableGeRule : Rule :=
    (Rule.ruleD "br_table-ge" [(Param.expP "i" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32"
    (Exp.tupE [])))])), (Param.expP "l*" (Typ.iterT (Typ.varT "labelidx" []) Iter.list)),
    (Param.expP "l'" (Typ.varT "labelidx" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST"
    (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE "i")])), (Exp.caseE "BR_TABLE"
    (Exp.tupE [(Exp.iterE (Exp.varE "l") (IterExp.mk Iter.list [(Dom.mk "l" (Exp.varE "l*"))])),
    (Exp.varE "l'")]))]), (Exp.listE [(Exp.caseE "BR" (Exp.varE "l'"))])]) [(Prem.ifPr (Exp.cmpE
    CmpOp.geOp (OpTyp.numT NumTyp.natT) (Exp.projE (Exp.uncaseE (Exp.varE "i") "%") (0 : Int))
    (Exp.lenE (Exp.iterE (Exp.varE "l") (IterExp.mk Iter.list [(Dom.mk "l" (Exp.varE
    "l*"))])))))])

/-- `Step_pure/frame-vals`, rule 14 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def frameValsRule : Rule :=
    (Rule.ruleD "frame-vals" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "f" (Typ.varT
    "frame" [])), (Param.expP "val*" (Typ.iterT (Typ.varT "val" []) Iter.list))] "%~>%" (Exp.tupE
    [(Exp.listE [(Exp.caseE "FRAME_%{%}%" (Exp.tupE [(Exp.varE "n"), (Exp.varE "f"), (Exp.iterE
    (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk
    (Iter.listN (Exp.varE "n") (@Option.none String)) [(Dom.mk "val" (Exp.varE "val*"))]))]))]),
    (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" []))
    (IterExp.mk (Iter.listN (Exp.varE "n") (@Option.none String)) [(Dom.mk "val" (Exp.varE
    "val*"))]))]) [])

/-- `Step_pure/return-frame`, rule 15 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def returnFrameRule : Rule :=
    (Rule.ruleD "return-frame" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "f" (Typ.varT
    "frame" [])), (Param.expP "val'*" (Typ.iterT (Typ.varT "val" []) Iter.list)), (Param.expP
    "val*" (Typ.iterT (Typ.varT "val" []) Iter.list)), (Param.expP "instr*" (Typ.iterT (Typ.varT
    "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "FRAME_%{%}%" (Exp.tupE
    [(Exp.varE "n"), (Exp.varE "f"), (Exp.catE (Exp.catE (Exp.catE (Exp.iterE (Exp.subE (Exp.varE
    "val'") (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "val'"
    (Exp.varE "val'*"))])) (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT
    "admininstr" [])) (IterExp.mk (Iter.listN (Exp.varE "n") (@Option.none String)) [(Dom.mk
    "val" (Exp.varE "val*"))]))) (Exp.listE [(Exp.caseE "RETURN" (Exp.tupE []))])) (Exp.iterE
    (Exp.subE (Exp.varE "instr") (Typ.varT "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk
    Iter.list [(Dom.mk "instr" (Exp.varE "instr*"))])))]))]), (Exp.iterE (Exp.subE (Exp.varE
    "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])) (IterExp.mk (Iter.listN (Exp.varE "n")
    (@Option.none String)) [(Dom.mk "val" (Exp.varE "val*"))]))]) [])

/-- `Step_pure/return-label`, rule 16 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def returnLabelRule : Rule :=
    (Rule.ruleD "return-label" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "instr'*"
    (Typ.iterT (Typ.varT "instr" []) Iter.list)), (Param.expP "val*" (Typ.iterT (Typ.varT "val"
    []) Iter.list)), (Param.expP "instr*" (Typ.iterT (Typ.varT "instr" []) Iter.list))] "%~>%"
    (Exp.tupE [(Exp.listE [(Exp.caseE "LABEL_%{%}%" (Exp.tupE [(Exp.varE "n"), (Exp.iterE
    (Exp.varE "instr'") (IterExp.mk Iter.list [(Dom.mk "instr'" (Exp.varE "instr'*"))])),
    (Exp.catE (Exp.catE (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT
    "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "val" (Exp.varE "val*"))])) (Exp.listE
    [(Exp.caseE "RETURN" (Exp.tupE []))])) (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT
    "instr" []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE
    "instr*"))])))]))]), (Exp.catE (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" [])
    (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "val" (Exp.varE "val*"))]))
    (Exp.listE [(Exp.caseE "RETURN" (Exp.tupE []))]))]) [])

/-- `Step_pure/trap-vals`, rule 17 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def trapValsRule : Rule :=
    (Rule.ruleD "trap-vals" [(Param.expP "val*" (Typ.iterT (Typ.varT "val" []) Iter.list)),
    (Param.expP "instr*" (Typ.iterT (Typ.varT "instr" []) Iter.list))] "%~>%" (Exp.tupE
    [(Exp.catE (Exp.iterE (Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr"
    [])) (IterExp.mk Iter.list [(Dom.mk "val" (Exp.varE "val*"))])) (Exp.catE (Exp.listE
    [(Exp.caseE "TRAP" (Exp.tupE []))]) (Exp.iterE (Exp.subE (Exp.varE "instr") (Typ.varT "instr"
    []) (Typ.varT "admininstr" [])) (IterExp.mk Iter.list [(Dom.mk "instr" (Exp.varE
    "instr*"))])))), (Exp.listE [(Exp.caseE "TRAP" (Exp.tupE []))])]) [(Prem.ifPr (Exp.binE
    BinOp.orOp OpTyp.boolT (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.iterE (Exp.varE "val")
    (IterExp.mk Iter.list [(Dom.mk "val" (Exp.varE "val*"))])) (Exp.listE [])) (Exp.cmpE
    CmpOp.neOp OpTyp.boolT (Exp.iterE (Exp.varE "instr") (IterExp.mk Iter.list [(Dom.mk "instr"
    (Exp.varE "instr*"))])) (Exp.listE []))))])

/-- `Step_pure/trap-label`, rule 18 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def trapLabelRule : Rule :=
    (Rule.ruleD "trap-label" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "instr'*"
    (Typ.iterT (Typ.varT "instr" []) Iter.list))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE
    "LABEL_%{%}%" (Exp.tupE [(Exp.varE "n"), (Exp.iterE (Exp.varE "instr'") (IterExp.mk Iter.list
    [(Dom.mk "instr'" (Exp.varE "instr'*"))])), (Exp.listE [(Exp.caseE "TRAP" (Exp.tupE
    []))])]))]), (Exp.listE [(Exp.caseE "TRAP" (Exp.tupE []))])]) [])

/-- `Step_pure/trap-frame`, rule 19 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def trapFrameRule : Rule :=
    (Rule.ruleD "trap-frame" [(Param.expP "n" (Typ.varT "n" [])), (Param.expP "f" (Typ.varT
    "frame" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "FRAME_%{%}%" (Exp.tupE [(Exp.varE
    "n"), (Exp.varE "f"), (Exp.listE [(Exp.caseE "TRAP" (Exp.tupE []))])]))]), (Exp.listE
    [(Exp.caseE "TRAP" (Exp.tupE []))])]) [])

/-- `Step_pure/unop-val`, rule 20 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def unopValRule : Rule :=
    (Rule.ruleD "unop-val" [(Param.expP "nt" (Typ.varT "numtype" [])), (Param.expP "c_1"
    (Typ.varT "num_" [(Arg.expA (Exp.varE "nt"))])), (Param.expP "unop" (Typ.varT "unop_"
    [(Arg.expA (Exp.varE "nt"))])), (Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.varE
    "nt"))]))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"),
    (Exp.varE "c_1")])), (Exp.caseE "UNOP" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "unop")]))]),
    (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "c")]))])]) [(Prem.ifPr
    (Exp.memE (Exp.varE "c") (Exp.callE "unop_" [(Arg.expA (Exp.varE "nt")), (Arg.expA (Exp.varE
    "unop")), (Arg.expA (Exp.varE "c_1"))])))])

/-- `Step_pure/unop-trap`, rule 21 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def unopTrapRule : Rule :=
    (Rule.ruleD "unop-trap" [(Param.expP "nt" (Typ.varT "numtype" [])), (Param.expP "c_1"
    (Typ.varT "num_" [(Arg.expA (Exp.varE "nt"))])), (Param.expP "unop" (Typ.varT "unop_"
    [(Arg.expA (Exp.varE "nt"))]))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE
    [(Exp.varE "nt"), (Exp.varE "c_1")])), (Exp.caseE "UNOP" (Exp.tupE [(Exp.varE "nt"),
    (Exp.varE "unop")]))]), (Exp.listE [(Exp.caseE "TRAP" (Exp.tupE []))])]) [(Prem.ifPr
    (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.callE "unop_" [(Arg.expA (Exp.varE "nt")), (Arg.expA
    (Exp.varE "unop")), (Arg.expA (Exp.varE "c_1"))]) (Exp.listE [])))])

/-- `Step_pure/binop-val`, rule 22 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def binopValRule : Rule :=
    (Rule.ruleD "binop-val" [(Param.expP "nt" (Typ.varT "numtype" [])), (Param.expP "c_1"
    (Typ.varT "num_" [(Arg.expA (Exp.varE "nt"))])), (Param.expP "c_2" (Typ.varT "num_"
    [(Arg.expA (Exp.varE "nt"))])), (Param.expP "binop" (Typ.varT "binop_" [(Arg.expA (Exp.varE
    "nt"))])), (Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.varE "nt"))]))] "%~>%" (Exp.tupE
    [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "c_1")])), (Exp.caseE
    "CONST" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "c_2")])), (Exp.caseE "BINOP" (Exp.tupE
    [(Exp.varE "nt"), (Exp.varE "binop")]))]), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE
    [(Exp.varE "nt"), (Exp.varE "c")]))])]) [(Prem.ifPr (Exp.memE (Exp.varE "c") (Exp.callE
    "binop_" [(Arg.expA (Exp.varE "nt")), (Arg.expA (Exp.varE "binop")), (Arg.expA (Exp.varE
    "c_1")), (Arg.expA (Exp.varE "c_2"))])))])

/-- `Step_pure/binop-trap`, rule 23 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def binopTrapRule : Rule :=
    (Rule.ruleD "binop-trap" [(Param.expP "nt" (Typ.varT "numtype" [])), (Param.expP "c_1"
    (Typ.varT "num_" [(Arg.expA (Exp.varE "nt"))])), (Param.expP "c_2" (Typ.varT "num_"
    [(Arg.expA (Exp.varE "nt"))])), (Param.expP "binop" (Typ.varT "binop_" [(Arg.expA (Exp.varE
    "nt"))]))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"),
    (Exp.varE "c_1")])), (Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "c_2")])),
    (Exp.caseE "BINOP" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "binop")]))]), (Exp.listE
    [(Exp.caseE "TRAP" (Exp.tupE []))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.callE
    "binop_" [(Arg.expA (Exp.varE "nt")), (Arg.expA (Exp.varE "binop")), (Arg.expA (Exp.varE
    "c_1")), (Arg.expA (Exp.varE "c_2"))]) (Exp.listE [])))])

/-- `Step_pure/testop`, rule 24 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def testopRule : Rule :=
    (Rule.ruleD "testop" [(Param.expP "nt" (Typ.varT "numtype" [])), (Param.expP "c_1" (Typ.varT
    "num_" [(Arg.expA (Exp.varE "nt"))])), (Param.expP "testop" (Typ.varT "testop_" [(Arg.expA
    (Exp.varE "nt"))])), (Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32" (Exp.tupE
    [])))]))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"),
    (Exp.varE "c_1")])), (Exp.caseE "TESTOP" (Exp.tupE [(Exp.varE "nt"), (Exp.varE
    "testop")]))]), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])),
    (Exp.varE "c")]))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.varE "c") (Exp.callE
    "testop_" [(Arg.expA (Exp.varE "nt")), (Arg.expA (Exp.varE "testop")), (Arg.expA (Exp.varE
    "c_1"))])))])

/-- `Step_pure/relop`, rule 25 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def relopRule : Rule :=
    (Rule.ruleD "relop" [(Param.expP "nt" (Typ.varT "numtype" [])), (Param.expP "c_1" (Typ.varT
    "num_" [(Arg.expA (Exp.varE "nt"))])), (Param.expP "c_2" (Typ.varT "num_" [(Arg.expA
    (Exp.varE "nt"))])), (Param.expP "relop" (Typ.varT "relop_" [(Arg.expA (Exp.varE "nt"))])),
    (Param.expP "c" (Typ.varT "num_" [(Arg.expA (Exp.caseE "I32" (Exp.tupE [])))]))] "%~>%"
    (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "c_1")])),
    (Exp.caseE "CONST" (Exp.tupE [(Exp.varE "nt"), (Exp.varE "c_2")])), (Exp.caseE "RELOP"
    (Exp.tupE [(Exp.varE "nt"), (Exp.varE "relop")]))]), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE
    [(Exp.caseE "I32" (Exp.tupE [])), (Exp.varE "c")]))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp
    OpTyp.boolT (Exp.varE "c") (Exp.callE "relop_" [(Arg.expA (Exp.varE "nt")), (Arg.expA
    (Exp.varE "relop")), (Arg.expA (Exp.varE "c_1")), (Arg.expA (Exp.varE "c_2"))])))])

/-- `Step_pure/cvtop-val`, rule 26 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def cvtopValRule : Rule :=
    (Rule.ruleD "cvtop-val" [(Param.expP "nt_1" (Typ.varT "numtype" [])), (Param.expP "c_1"
    (Typ.varT "num_" [(Arg.expA (Exp.varE "nt_1"))])), (Param.expP "nt_2" (Typ.varT "numtype"
    [])), (Param.expP "cvtop" (Typ.varT "cvtop" [])), (Param.expP "c" (Typ.varT "num_" [(Arg.expA
    (Exp.varE "nt_2"))]))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE
    "nt_1"), (Exp.varE "c_1")])), (Exp.caseE "CVTOP" (Exp.tupE [(Exp.varE "nt_2"), (Exp.varE
    "nt_1"), (Exp.varE "cvtop")]))]), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.varE
    "nt_2"), (Exp.varE "c")]))])]) [(Prem.ifPr (Exp.memE (Exp.varE "c") (Exp.callE "cvtop__"
    [(Arg.expA (Exp.varE "nt_1")), (Arg.expA (Exp.varE "nt_2")), (Arg.expA (Exp.varE "cvtop")),
    (Arg.expA (Exp.varE "c_1"))])))])

/-- `Step_pure/cvtop-trap`, rule 27 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def cvtopTrapRule : Rule :=
    (Rule.ruleD "cvtop-trap" [(Param.expP "nt_1" (Typ.varT "numtype" [])), (Param.expP "c_1"
    (Typ.varT "num_" [(Arg.expA (Exp.varE "nt_1"))])), (Param.expP "nt_2" (Typ.varT "numtype"
    [])), (Param.expP "cvtop" (Typ.varT "cvtop" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE
    "CONST" (Exp.tupE [(Exp.varE "nt_1"), (Exp.varE "c_1")])), (Exp.caseE "CVTOP" (Exp.tupE
    [(Exp.varE "nt_2"), (Exp.varE "nt_1"), (Exp.varE "cvtop")]))]), (Exp.listE [(Exp.caseE "TRAP"
    (Exp.tupE []))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.callE "cvtop__"
    [(Arg.expA (Exp.varE "nt_1")), (Arg.expA (Exp.varE "nt_2")), (Arg.expA (Exp.varE "cvtop")),
    (Arg.expA (Exp.varE "c_1"))]) (Exp.listE [])))])


/-! ## What the numeric rules need: agreement of the script's numeric functions with V2 -/

section Numeric

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly)
open Silmaril.SpecTec.Equiv.Execution (pctV)

/-- **The numeric agreement hypothesis** at a profile `P`: in `env`, the script's `$unop_`,
`$binop_`, `$testop_` and `$relop_` (with `env`'s builtins for the `hint(builtin)` primitives)
return, at the encodings of V2 operands, exactly V2's results: the list of every result V2
permits for the set-valued functions, the one result for the others. This is a statement about
the wasm-2.0 script's `3-numerics` and the builtins; it is **assumed**, not proved, here. -/
structure NumAgree (env : Env) (P : Profile) : Prop where
  /-- `$unop_(Inn, …)`, at a valid operator. -/
  intUnOp : ∀ (t : IntType) (op : IntUnOp) (x : BitVec t.width), op.valid t →
    ∃ vs, Applies env "unop_" [.val (numTypeV (.int t)), .val (intUnOpV op), .val (pctV x.toNat)]
      (.list vs) ∧ ∀ c, c ∈ vs ↔ ∃ z, IntUnOpResult t op x z ∧ c = pctV z.toNat
  /-- `$unop_(Fnn, …)`. -/
  floatUnOp : ∀ (t : FloatType) (op : FloatUnOp) (x : BitVec t.width),
    ∃ vs, Applies env "unop_" [.val (numTypeV (.float t)), .val (floatUnOpV op),
      .val (Sim.floatV t x)] (.list vs) ∧
      ∀ c, c ∈ vs ↔ ∃ z, FloatUnOpResult P t op x z ∧ c = Sim.floatV t z
  /-- `$binop_(Inn, …)`; the list is empty exactly when V2 has no result. -/
  intBinOp : ∀ (t : IntType) (op : IntBinOp) (x y : BitVec t.width),
    ∃ vs, Applies env "binop_" [.val (numTypeV (.int t)), .val (intBinOpV op),
      .val (pctV x.toNat), .val (pctV y.toNat)] (.list vs) ∧
      ∀ c, c ∈ vs ↔ ∃ z, IntBinOpResult t op x y z ∧ c = pctV z.toNat
  /-- `$binop_(Fnn, …)`. -/
  floatBinOp : ∀ (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width),
    ∃ vs, Applies env "binop_" [.val (numTypeV (.float t)), .val (floatBinOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (.list vs) ∧
      ∀ c, c ∈ vs ↔ ∃ z, FloatBinOpResult P t op x y z ∧ c = Sim.floatV t z
  /-- `$testop_(Inn, …)`. -/
  intTestOp : ∀ (t : IntType) (op : IntTestOp) (x : BitVec t.width),
    Applies env "testop_" [.val (numTypeV (.int t)), .val (intTestOpV op), .val (pctV x.toNat)]
      (pctV (testOp t op x).toNat)
  /-- `$relop_(Inn, …)`. -/
  intRelOp : ∀ (t : IntType) (op : IntRelOp) (x y : BitVec t.width),
    Applies env "relop_" [.val (numTypeV (.int t)), .val (intRelOpV op), .val (pctV x.toNat),
      .val (pctV y.toNat)] (pctV (intRelOp t op x y).toNat)
  /-- `$relop_(Fnn, …)`. -/
  floatRelOp : ∀ (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width),
    Applies env "relop_" [.val (numTypeV (.float t)), .val (floatRelOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (pctV (floatRelOp t op x y).toNat)

/-- `HasTyp` of `v` against `T(x)` in every value-only scope that binds `x` to `w`: what a
rule quantifier of a dependent type (`num_(nt)`, `unop_(nt)`, …) needs. -/
def TypedAt (env : Env) (T : IL.Id) (x : IL.Id) (w v : Value) : Prop :=
  ∀ ρ : VarEnv, ValsOnly ρ → ρ.findVal? x = some w → HasTyp env ρ (.varT T [.expA (.varE x)]) v

/-- **The numeric typing hypothesis**: the encodings of V2 number types, numbers and (valid)
scalar operators have their IL types. The build-time check `Sim20.EncodeCheck` accepts every
instance in its corpus; the general statement is **assumed** here. -/
structure NumTyped (env : Env) : Prop where
  /-- `numtype`. -/
  numtype : ∀ t, Silmaril.Wasm.SpecTec.Sim.TypedV env (.varT "numtype" []) (numTypeV t)
  /-- `num_(nt)`, for every variable name the rules use. -/
  num : ∀ (t : NumType) (x : BitVec t.width) (y : IL.Id), TypedAt env "num_" y (numTypeV t)
    (numV ⟨t, x⟩)
  /-- `num_(I32)`. -/
  i32 : ∀ b : BitVec 32, Silmaril.Wasm.SpecTec.Sim.TypedV env i32T (pctV b.toNat)
  /-- `unop_(Inn)`, at a valid operator. -/
  intUnOp : ∀ t (op : IntUnOp), op.valid t → TypedAt env "unop_" "nt" (numTypeV (.int t))
    (intUnOpV op)
  /-- `unop_(Fnn)`. -/
  floatUnOp : ∀ t op, TypedAt env "unop_" "nt" (numTypeV (.float t)) (floatUnOpV op)
  /-- `binop_(Inn)`. -/
  intBinOp : ∀ t op, TypedAt env "binop_" "nt" (numTypeV (.int t)) (intBinOpV op)
  /-- `binop_(Fnn)`. -/
  floatBinOp : ∀ t op, TypedAt env "binop_" "nt" (numTypeV (.float t)) (floatBinOpV op)
  /-- `testop_(Inn)`. -/
  intTestOp : ∀ t op, TypedAt env "testop_" "nt" (numTypeV (.int t)) (intTestOpV op)
  /-- `relop_(Inn)`. -/
  intRelOp : ∀ t op, TypedAt env "relop_" "nt" (numTypeV (.int t)) (intRelOpV op)
  /-- `relop_(Fnn)`. -/
  floatRelOp : ∀ t op, TypedAt env "relop_" "nt" (numTypeV (.float t)) (floatRelOpV op)

end Numeric

end Silmaril.Wasm.SpecTec.Sim20.Pure
