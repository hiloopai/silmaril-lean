module

public import Silmaril.Wasm.SpecTec.Sim20.Pure.Defs

/-!
# SpecTec 2.0 ↔ V2: the reference and variable rules

The rules of `Scripts.Wasm20.fixed` for references and variables that the rule-level
correspondence of `docs/projects/spectec/README.md` §1.5 covers in pass 3, **verbatim** from the generated
script (`Scripts.Wasm20.Original`, Parts 3 and 4; no erratum touches them):

* `Step_pure` 28 `ref.is_null-true` and 55 `local.tee`;
* `Step_read` 6 `ref.func`, 7 `local.get`, 8 `global.get`;
* `Step` 4 `local.set`.

`ref.is_null-false` (`Step_pure` 29) is not covered: its premise is `-- otherwise`, which under
the declarative reading refutes the 29 earlier rules at the left-hand side. `global.set` and the
table and memory rules are not covered either; see `docs/projects/spectec/README.md`.

Their provenance in `simEnv20 B` is a kernel `rfl` (`Sim20.State.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

/-- `Step_pure/ref.is_null-true`, rule 28 of `Step_pure` (verbatim). -/
def refIsNullTrueRule : Rule :=
    (Rule.ruleD "ref.is_null-true" [(Param.expP "ref" (Typ.varT "ref" [])), (Param.expP "rt" (Typ.varT "reftype"
    []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.subE (Exp.varE "ref") (Typ.varT "ref" []) (Typ.varT "admininstr"
    [])), (Exp.caseE "REF.IS_NULL" (Exp.tupE []))]), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32"
    (Exp.tupE [])), (Exp.caseE "%" (Exp.tupE [(Exp.numE (Num.natN 1))]))]))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
    (Exp.varE "ref") (Exp.caseE "REF.NULL" (Exp.varE "rt"))))])

/-- `Step_pure/ref.is_null-false`, rule 29 of `Step_pure` (verbatim). Its premise is
`-- otherwise`. -/
def refIsNullFalseRule : Rule :=
    (Rule.ruleD "ref.is_null-false"
  [(Param.expP "ref" (Typ.varT "ref" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.subE (Exp.varE "ref")
  (Typ.varT "ref" []) (Typ.varT "admininstr" [])), (Exp.caseE "REF.IS_NULL" (Exp.tupE []))]), (Exp.listE
  [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.caseE "%" (Exp.tupE [(Exp.numE
  (Num.natN 0))]))]))])]) [Prem.elsePr])

/-- `Step_pure/local.tee`, rule 55 of `Step_pure` (verbatim). -/
def localTeeRule : Rule :=
    (Rule.ruleD "local.tee" [(Param.expP "val" (Typ.varT "val" [])), (Param.expP "x"
    (Typ.varT "idx" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.subE (Exp.varE "val") (Typ.varT "val"
    []) (Typ.varT "admininstr" [])), (Exp.caseE "LOCAL.TEE" (Exp.varE "x"))]), (Exp.listE [(Exp.subE
    (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])), (Exp.subE (Exp.varE "val") (Typ.varT "val"
    []) (Typ.varT "admininstr" [])), (Exp.caseE "LOCAL.SET" (Exp.varE "x"))])]) [])

/-- `Step_read/ref.func`, rule 6 of `Step_read` (verbatim). -/
def refFuncRule : Rule :=
    (Rule.ruleD "ref.func" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "x"
    (Typ.varT "idx" []))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE
    [(Exp.caseE "REF.FUNC" (Exp.varE "x"))])])), (Exp.listE [(Exp.caseE "REF.FUNC_ADDR" (Exp.idxE (Exp.callE "funcaddr"
    [(Arg.expA (Exp.varE "z"))]) (Exp.projE (Exp.uncaseE (Exp.varE "x") "%") (0 : Int))))])]) [])

/-- `Step_read/call`, rule 2 of `Step_read` (verbatim). -/
def callRule : Rule :=
    (Rule.ruleD "call" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "x" (Typ.varT "idx" []))] "%~>%"
    (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "CALL" (Exp.varE "x"))])])),
    (Exp.listE [(Exp.caseE "CALL_ADDR" (Exp.idxE (Exp.callE "funcaddr" [(Arg.expA (Exp.varE "z"))])
    (Exp.projE (Exp.uncaseE (Exp.varE "x") "%") (0 : Int))))])]) [])

/-- `Step_read/local.get`, rule 7 of `Step_read` (verbatim). -/
def localGetRule : Rule :=
    (Rule.ruleD "local.get" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "x" (Typ.varT "idx"
    []))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "LOCAL.GET"
    (Exp.varE "x"))])])), (Exp.listE [(Exp.subE (Exp.callE "local" [(Arg.expA (Exp.varE "z")), (Arg.expA
    (Exp.varE "x"))]) (Typ.varT "val" []) (Typ.varT "admininstr" []))])]) [])

/-- `Step_read/global.get`, rule 8 of `Step_read` (verbatim). -/
def globalGetRule : Rule :=
    (Rule.ruleD "global.get"
    [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "x" (Typ.varT "idx" []))] "%~>%" (Exp.tupE
    [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "GLOBAL.GET" (Exp.varE "x"))])])),
    (Exp.listE [(Exp.subE (Exp.dotE (Exp.callE "global" [(Arg.expA (Exp.varE "z")), (Arg.expA (Exp.varE "x"))]) "VALUE")
    (Typ.varT "val" []) (Typ.varT "admininstr" []))])]) [])

/-- `Step/local.set`, rule 4 of `Step` (verbatim). -/
def localSetRule : Rule :=
    (Rule.ruleD "local.set" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "val" (Typ.varT "val"
    [])), (Param.expP "x" (Typ.varT "idx" []))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"),
    (Exp.listE [(Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])), (Exp.caseE "LOCAL.SET"
    (Exp.varE "x"))])])), (Exp.caseE "%;%" (Exp.tupE [(Exp.callE "with_local" [(Arg.expA (Exp.varE "z")),
    (Arg.expA (Exp.varE "x")), (Arg.expA (Exp.varE "val"))]), (Exp.listE [])]))]) [])

/-- `stateT`, `idxT`: the IL types the variable rules quantify over. -/
abbrev stateT : Typ := .varT "state" []
/-- `idx`. -/
abbrev idxT : Typ := .varT "idx" []
/-- `ref`. -/
abbrev refT : Typ := .varT "ref" []
/-- `reftype`. -/
abbrev reftypeT : Typ := .varT "reftype" []

end Silmaril.Wasm.SpecTec.Sim20.State
