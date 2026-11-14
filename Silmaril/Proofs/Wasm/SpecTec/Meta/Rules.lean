module

public import Silmaril.Wasm.SpecTec.Meta.Defs

/-!
# The rules of their `Step_exp` and `Reduce_exp` that the fragment reaches, as literals

Each `def` below is copied from the generated script (`Scripts.MetaIL.{Fixed,Original}`, the
`recD` group holding `Step_exp`), and `stepF_eq`/`stepO_eq` and the `reduce*_eq` theorems check
by `rfl` that they are the rules `envF`/`envO` look up, at the stated indices. Having them as
literals lets `simp` see their conclusions and premises. (The extraction was done by a one-off
script; the `rfl` checks are what make it trustworthy.)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta.Rules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

set_option maxRecDepth 100000

/-! ### `Step_exp` of `fixed` -/

namespace F

/-- Rule 0 of `Step_exp`, `UN-ctx`. -/
def unCtx : Rule :=
  (Rule.ruleD "UN-ctx" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "unop" [])),
  (Param.expP "e" (Typ.varT "exp" [])), (Param.expP "e'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.caseE "UN" (Exp.tupE [(Exp.varE "op"), (Exp.varE "e")])), (Exp.caseE "UN"
  (Exp.tupE [(Exp.varE "op"), (Exp.varE "e'")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e'")]))])

/-- Rule 1 of `Step_exp`, `UN-BOOL`. -/
def unBool : Rule :=
  (Rule.ruleD "UN-BOOL" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "boolunop" (Typ.varT
  "boolunop" [])), (Param.expP "b" Typ.boolT)] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "UN"
  (Exp.tupE [(Exp.subE (Exp.varE "boolunop") (Typ.varT "boolunop" []) (Typ.varT "unop" [])),
  (Exp.caseE "BOOL" (Exp.tupE [(Exp.varE "b")]))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.callE
  "boolun" [(Arg.expA (Exp.varE "boolunop")), (Arg.expA (Exp.varE "b"))])]))]) [])

/-- Rule 2 of `Step_exp`, `UN-NUM`. -/
def unNum : Rule :=
  (Rule.ruleD "UN-NUM" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "numunop" (Typ.varT
  "numunop" [])), (Param.expP "num" (Typ.varT "num" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"),
  (Exp.caseE "UN" (Exp.tupE [(Exp.subE (Exp.varE "numunop") (Typ.varT "numunop" []) (Typ.varT "unop"
  [])), (Exp.subE (Exp.varE "num") (Typ.varT "num" []) (Typ.varT "exp" []))])), (Exp.subE (Exp.callE
  "numun" [(Arg.expA (Exp.varE "numunop")), (Arg.expA (Exp.varE "num"))]) (Typ.varT "num" [])
  (Typ.varT "exp" []))]) [])

/-- Rule 3 of `Step_exp`, `BIN-ctx1`. -/
def binCtx1 : Rule :=
  (Rule.ruleD "BIN-ctx1" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "binop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_1'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE
  [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE "BIN" (Exp.tupE [(Exp.varE
  "op"), (Exp.varE "e_1'"), (Exp.varE "e_2")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e_1"), (Exp.varE "e_1'")]))])

/-- Rule 4 of `Step_exp`, `BIN-ctx2`. -/
def binCtx2 : Rule :=
  (Rule.ruleD "BIN-ctx2" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "binop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_2'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE
  [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE "BIN" (Exp.tupE [(Exp.varE
  "op"), (Exp.varE "e_1"), (Exp.varE "e_2'")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e_2"), (Exp.varE "e_2'")]))])

/-- Rule 5 of `Step_exp`, `BIN-BOOL`. -/
def binBool : Rule :=
  (Rule.ruleD "BIN-BOOL" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "boolbinop" (Typ.varT
  "boolbinop" [])), (Param.expP "b_1" Typ.boolT), (Param.expP "b_2" Typ.boolT)] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE [(Exp.subE (Exp.varE "boolbinop") (Typ.varT
  "boolbinop" []) (Typ.varT "binop" [])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.varE "b_1")])),
  (Exp.caseE "BOOL" (Exp.tupE [(Exp.varE "b_2")]))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.callE
  "boolbin" [(Arg.expA (Exp.varE "boolbinop")), (Arg.expA (Exp.varE "b_1")), (Arg.expA (Exp.varE
  "b_2"))])]))]) [])

/-- Rule 6 of `Step_exp`, `BIN-NUM`. -/
def binNum : Rule :=
  (Rule.ruleD "BIN-NUM" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "numbinop" (Typ.varT
  "numbinop" [])), (Param.expP "num_1" (Typ.varT "num" [])), (Param.expP "num_2" (Typ.varT "num"
  []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE [(Exp.subE (Exp.varE
  "numbinop") (Typ.varT "numbinop" []) (Typ.varT "binop" [])), (Exp.subE (Exp.varE "num_1")
  (Typ.varT "num" []) (Typ.varT "exp" [])), (Exp.subE (Exp.varE "num_2") (Typ.varT "num" [])
  (Typ.varT "exp" []))])), (Exp.subE (Exp.callE "numbin" [(Arg.expA (Exp.varE "numbinop")),
  (Arg.expA (Exp.varE "num_1")), (Arg.expA (Exp.varE "num_2"))]) (Typ.varT "num" []) (Typ.varT "exp"
  []))]) [])

/-- Rule 7 of `Step_exp`, `CMP-ctx1`. -/
def cmpCtx1 : Rule :=
  (Rule.ruleD "CMP-ctx1" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "cmpop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_1'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "CMP" (Exp.tupE
  [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE "CMP" (Exp.tupE [(Exp.varE
  "op"), (Exp.varE "e_1'"), (Exp.varE "e_2")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e_1"), (Exp.varE "e_1'")]))])

/-- Rule 8 of `Step_exp`, `CMP-ctx2`. -/
def cmpCtx2 : Rule :=
  (Rule.ruleD "CMP-ctx2" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "cmpop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_2'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "CMP" (Exp.tupE
  [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE "CMP" (Exp.tupE [(Exp.varE
  "op"), (Exp.varE "e_1"), (Exp.varE "e_2'")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e_2"), (Exp.varE "e_2'")]))])

/-- Rule 9 of `Step_exp`, `CMP-EQ-true`. -/
def cmpEqTrue : Rule :=
  (Rule.ruleD "CMP-EQ-true" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "val_1" (Typ.varT "val"
  [])), (Param.expP "val_2" (Typ.varT "val" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE
  "CMP" (Exp.tupE [(Exp.caseE "EQ" (Exp.tupE [])), (Exp.subE (Exp.varE "val_1") (Typ.varT "val" [])
  (Typ.varT "exp" [])), (Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT "exp" []))])),
  (Exp.caseE "BOOL" (Exp.tupE [(Exp.boolE true)]))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
  (Exp.varE "val_1") (Exp.varE "val_2")))])

/-- Rule 10 of `Step_exp`, `CMP-EQ-false`. -/
def cmpEqFalse : Rule :=
  (Rule.ruleD "CMP-EQ-false" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "val_1" (Typ.varT
  "val" [])), (Param.expP "val_2" (Typ.varT "val" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"),
  (Exp.caseE "CMP" (Exp.tupE [(Exp.caseE "EQ" (Exp.tupE [])), (Exp.subE (Exp.varE "val_1") (Typ.varT
  "val" []) (Typ.varT "exp" [])), (Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT "exp"
  []))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.boolE false)]))]) [(Prem.ifPr (Exp.cmpE CmpOp.neOp
  OpTyp.boolT (Exp.varE "val_1") (Exp.varE "val_2")))])

/-- Rule 11 of `Step_exp`, `CMP-NE-false`. -/
def cmpNeFalse : Rule :=
  (Rule.ruleD "CMP-NE-false" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "val_1" (Typ.varT
  "val" [])), (Param.expP "val_2" (Typ.varT "val" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"),
  (Exp.caseE "CMP" (Exp.tupE [(Exp.caseE "NE" (Exp.tupE [])), (Exp.subE (Exp.varE "val_1") (Typ.varT
  "val" []) (Typ.varT "exp" [])), (Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT "exp"
  []))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.boolE false)]))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp
  OpTyp.boolT (Exp.varE "val_1") (Exp.varE "val_2")))])

/-- Rule 12 of `Step_exp`, `CMP-NE-true`. -/
def cmpNeTrue : Rule :=
  (Rule.ruleD "CMP-NE-true" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "val_1" (Typ.varT "val"
  [])), (Param.expP "val_2" (Typ.varT "val" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE
  "CMP" (Exp.tupE [(Exp.caseE "NE" (Exp.tupE [])), (Exp.subE (Exp.varE "val_1") (Typ.varT "val" [])
  (Typ.varT "exp" [])), (Exp.subE (Exp.varE "val_2") (Typ.varT "val" []) (Typ.varT "exp" []))])),
  (Exp.caseE "BOOL" (Exp.tupE [(Exp.boolE true)]))]) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT
  (Exp.varE "val_1") (Exp.varE "val_2")))])

/-- Rule 13 of `Step_exp`, `CMP-NUM`. -/
def cmpNum : Rule :=
  (Rule.ruleD "CMP-NUM" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "numcmpop" (Typ.varT
  "numcmpop" [])), (Param.expP "num_1" (Typ.varT "num" [])), (Param.expP "num_2" (Typ.varT "num"
  []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "CMP" (Exp.tupE [(Exp.subE (Exp.varE
  "numcmpop") (Typ.varT "numcmpop" []) (Typ.varT "cmpop" [])), (Exp.subE (Exp.varE "num_1")
  (Typ.varT "num" []) (Typ.varT "exp" [])), (Exp.subE (Exp.varE "num_2") (Typ.varT "num" [])
  (Typ.varT "exp" []))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.callE "numcmp" [(Arg.expA (Exp.varE
  "numcmpop")), (Arg.expA (Exp.varE "num_1")), (Arg.expA (Exp.varE "num_2"))])]))]) [])

/-- Rule 0 of `Reduce_exp`, `normal`. -/
def redNormal : Rule :=
  (Rule.ruleD "normal" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "e" (Typ.varT "exp" []))]
  "%|-%~>*%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e")]) [])

/-- Rule 1 of `Reduce_exp`, `step`. -/
def redStep : Rule :=
  (Rule.ruleD "step" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "e" (Typ.varT "exp" [])),
  (Param.expP "e''" (Typ.varT "exp" [])), (Param.expP "e'" (Typ.varT "exp" []))] "%|-%~>*%"
  (Exp.tupE [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e''")]) [(Prem.rulePr "Step_exp" []
  "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e'")])), (Prem.rulePr "Reduce_exp"
  [] "%|-%~>*%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e'"), (Exp.varE "e''")]))])

end F

/-! ### `Step_exp` of `original` -/

namespace O

/-- Rule 0 of `Step_exp`, `UN-ctx`. -/
def unCtx : Rule :=
  (Rule.ruleD "UN-ctx" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "unop" [])),
  (Param.expP "e" (Typ.varT "exp" [])), (Param.expP "e'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.caseE "UN" (Exp.tupE [(Exp.varE "op"), (Exp.varE "e")])), (Exp.caseE "UN"
  (Exp.tupE [(Exp.varE "op"), (Exp.varE "e'")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e'")]))])

/-- Rule 1 of `Step_exp`, `UN-BOOL`. -/
def unBool : Rule :=
  (Rule.ruleD "UN-BOOL" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "boolunop" (Typ.varT
  "boolunop" [])), (Param.expP "b" Typ.boolT)] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "UN"
  (Exp.tupE [(Exp.subE (Exp.varE "boolunop") (Typ.varT "boolunop" []) (Typ.varT "unop" [])),
  (Exp.caseE "BOOL" (Exp.tupE [(Exp.varE "b")]))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.callE
  "boolun" [(Arg.expA (Exp.varE "boolunop")), (Arg.expA (Exp.varE "b"))])]))]) [])

/-- Rule 2 of `Step_exp`, `UN-NUM`. -/
def unNum : Rule :=
  (Rule.ruleD "UN-NUM" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "numunop" (Typ.varT
  "numunop" [])), (Param.expP "num" (Typ.varT "num" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"),
  (Exp.caseE "UN" (Exp.tupE [(Exp.subE (Exp.varE "numunop") (Typ.varT "numunop" []) (Typ.varT "unop"
  [])), (Exp.subE (Exp.varE "num") (Typ.varT "num" []) (Typ.varT "exp" []))])), (Exp.subE (Exp.callE
  "numun" [(Arg.expA (Exp.varE "numunop")), (Arg.expA (Exp.varE "num"))]) (Typ.varT "num" [])
  (Typ.varT "exp" []))]) [])

/-- Rule 3 of `Step_exp`, `BIN-ctx1`. -/
def binCtx1 : Rule :=
  (Rule.ruleD "BIN-ctx1" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "binop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_1'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE
  [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE "BIN" (Exp.tupE [(Exp.varE
  "op"), (Exp.varE "e_1'"), (Exp.varE "e_2")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e_1"), (Exp.varE "e_1'")]))])

/-- Rule 4 of `Step_exp`, `BIN-ctx2`. -/
def binCtx2 : Rule :=
  (Rule.ruleD "BIN-ctx2" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "binop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_1'" (Typ.varT "exp" [])), (Param.expP "e_2'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE
  "e_2")])), (Exp.caseE "BIN" (Exp.tupE [(Exp.varE "op"), (Exp.varE "e_1'"), (Exp.varE "e_2")]))])
  [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e_2"), (Exp.varE
  "e_2'")]))])

/-- Rule 5 of `Step_exp`, `BIN-BOOL`. -/
def binBool : Rule :=
  (Rule.ruleD "BIN-BOOL" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "boolbinop" (Typ.varT
  "boolbinop" [])), (Param.expP "b_1" Typ.boolT), (Param.expP "b_2" Typ.boolT)] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE [(Exp.subE (Exp.varE "boolbinop") (Typ.varT
  "boolbinop" []) (Typ.varT "binop" [])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.varE "b_1")])),
  (Exp.caseE "BOOL" (Exp.tupE [(Exp.varE "b_2")]))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.callE
  "boolbin" [(Arg.expA (Exp.varE "boolbinop")), (Arg.expA (Exp.varE "b_1")), (Arg.expA (Exp.varE
  "b_2"))])]))]) [])

/-- Rule 6 of `Step_exp`, `BIN-NUM`. -/
def binNum : Rule :=
  (Rule.ruleD "BIN-NUM" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "numbinop" (Typ.varT
  "numbinop" [])), (Param.expP "num_1" (Typ.varT "num" [])), (Param.expP "num_2" (Typ.varT "num"
  []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "BIN" (Exp.tupE [(Exp.subE (Exp.varE
  "numbinop") (Typ.varT "numbinop" []) (Typ.varT "binop" [])), (Exp.subE (Exp.varE "num_1")
  (Typ.varT "num" []) (Typ.varT "exp" [])), (Exp.subE (Exp.varE "num_2") (Typ.varT "num" [])
  (Typ.varT "exp" []))])), (Exp.subE (Exp.callE "numbin" [(Arg.expA (Exp.varE "numbinop")),
  (Arg.expA (Exp.varE "num_1")), (Arg.expA (Exp.varE "num_2"))]) (Typ.varT "num" []) (Typ.varT "exp"
  []))]) [])

/-- Rule 7 of `Step_exp`, `CMP-ctx1`. -/
def cmpCtx1 : Rule :=
  (Rule.ruleD "CMP-ctx1" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "cmpop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_1'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "CMP" (Exp.tupE
  [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE "CMP" (Exp.tupE [(Exp.varE
  "op"), (Exp.varE "e_1'"), (Exp.varE "e_2")]))]) [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.varE "e_1"), (Exp.varE "e_1'")]))])

/-- Rule 8 of `Step_exp`, `CMP-ctx2`. -/
def cmpCtx2 : Rule :=
  (Rule.ruleD "CMP-ctx2" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "op" (Typ.varT "cmpop"
  [])), (Param.expP "e_1" (Typ.varT "exp" [])), (Param.expP "e_2" (Typ.varT "exp" [])), (Param.expP
  "e_1'" (Typ.varT "exp" [])), (Param.expP "e_2'" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE
  [(Exp.varE "S"), (Exp.caseE "CMP" (Exp.tupE [(Exp.varE "op"), (Exp.varE "e_1"), (Exp.varE
  "e_2")])), (Exp.caseE "CMP" (Exp.tupE [(Exp.varE "op"), (Exp.varE "e_1'"), (Exp.varE "e_2")]))])
  [(Prem.rulePr "Step_exp" [] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e_2"), (Exp.varE
  "e_2'")]))])

/-- Rule 9 of `Step_exp`, `CMP-EQ-true`. -/
def cmpEqTrue : Rule :=
  (Rule.ruleD "CMP-EQ-true" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "e_1" (Typ.varT "exp"
  [])), (Param.expP "e_2" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE
  "CMP" (Exp.tupE [(Exp.caseE "EQ" (Exp.tupE [])), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE
  "BOOL" (Exp.tupE [(Exp.boolE true)]))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.varE
  "e_1") (Exp.varE "e_2")))])

/-- Rule 10 of `Step_exp`, `CMP-NE-false`. -/
def cmpNeFalse : Rule :=
  (Rule.ruleD "CMP-NE-false" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "e_1" (Typ.varT "exp"
  [])), (Param.expP "e_2" (Typ.varT "exp" []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE
  "CMP" (Exp.tupE [(Exp.caseE "NE" (Exp.tupE [])), (Exp.varE "e_1"), (Exp.varE "e_2")])), (Exp.caseE
  "BOOL" (Exp.tupE [(Exp.boolE false)]))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.varE
  "e_1") (Exp.varE "e_2")))])

/-- Rule 11 of `Step_exp`, `CMP-NUM`. -/
def cmpNum : Rule :=
  (Rule.ruleD "CMP-NUM" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "numcmpop" (Typ.varT
  "numcmpop" [])), (Param.expP "num_1" (Typ.varT "num" [])), (Param.expP "num_2" (Typ.varT "num"
  []))] "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.caseE "CMP" (Exp.tupE [(Exp.subE (Exp.varE
  "numcmpop") (Typ.varT "numcmpop" []) (Typ.varT "cmpop" [])), (Exp.subE (Exp.varE "num_1")
  (Typ.varT "num" []) (Typ.varT "exp" [])), (Exp.subE (Exp.varE "num_2") (Typ.varT "num" [])
  (Typ.varT "exp" []))])), (Exp.caseE "BOOL" (Exp.tupE [(Exp.callE "numcmp" [(Arg.expA (Exp.varE
  "numcmpop")), (Arg.expA (Exp.varE "num_1")), (Arg.expA (Exp.varE "num_2"))])]))]) [])

/-- Rule 0 of `Reduce_exp`, `normal`. -/
def redNormal : Rule :=
  (Rule.ruleD "normal" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "e" (Typ.varT "exp" []))]
  "%|-%~>*%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e")]) [])

/-- Rule 1 of `Reduce_exp`, `step`. -/
def redStep : Rule :=
  (Rule.ruleD "step" [(Param.expP "S" (Typ.varT "S" [])), (Param.expP "e" (Typ.varT "exp" [])),
  (Param.expP "e''" (Typ.varT "exp" [])), (Param.expP "e'" (Typ.varT "exp" []))] "%|-%~>*%"
  (Exp.tupE [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e''")]) [(Prem.rulePr "Step_exp" []
  "%|-%~>%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e"), (Exp.varE "e'")])), (Prem.rulePr "Reduce_exp"
  [] "%|-%~>*%" (Exp.tupE [(Exp.varE "S"), (Exp.varE "e'"), (Exp.varE "e''")]))])

end O

namespace F

/-! ### `$numbin` of `fixed` -/

/-- The clauses of `$numbin` in `fixed` (after erratum M2). -/
def numbinF : List Clause :=
  [(Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "ADD" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.binE BinOp.addOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE
    "n_2"))])) []),
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "ADD" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.binE BinOp.addOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2"))])) []),
  (Clause.defD [(Param.expP "q_1" (Typ.numT NumTyp.ratT)), (Param.expP "q_2" (Typ.numT
    NumTyp.ratT))] [(Arg.expA (Exp.caseE "ADD" (Exp.tupE []))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE
    [(Exp.varE "q_1")]))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE [(Exp.varE "q_2")])))] (Exp.caseE
    "RAT" (Exp.tupE [(Exp.binE BinOp.addOp (OpTyp.numT NumTyp.ratT) (Exp.varE "q_1") (Exp.varE
    "q_2"))])) []),
  (Clause.defD [(Param.expP "r_1" (Typ.numT NumTyp.realT)), (Param.expP "r_2" (Typ.numT
    NumTyp.realT))] [(Arg.expA (Exp.caseE "ADD" (Exp.tupE []))), (Arg.expA (Exp.caseE "REAL"
    (Exp.tupE [(Exp.varE "r_1")]))), (Arg.expA (Exp.caseE "REAL" (Exp.tupE [(Exp.varE "r_2")])))]
    (Exp.caseE "REAL" (Exp.tupE [(Exp.binE BinOp.addOp (OpTyp.numT NumTyp.realT) (Exp.varE "r_1")
    (Exp.varE "r_2"))])) []),
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "SUB" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.subOp (OpTyp.numT NumTyp.intT) (Exp.cvtE (Exp.varE
    "n_1") NumTyp.natT NumTyp.intT) (Exp.cvtE (Exp.varE "n_2") NumTyp.natT NumTyp.intT)) NumTyp.intT
    NumTyp.natT)])) [(Prem.ifPr (Exp.cmpE CmpOp.geOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1")
    (Exp.varE "n_2")))]),
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "SUB" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.binE BinOp.subOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2"))])) []),
  (Clause.defD [(Param.expP "q_1" (Typ.numT NumTyp.ratT)), (Param.expP "q_2" (Typ.numT
    NumTyp.ratT))] [(Arg.expA (Exp.caseE "SUB" (Exp.tupE []))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE
    [(Exp.varE "q_1")]))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE [(Exp.varE "q_2")])))] (Exp.caseE
    "RAT" (Exp.tupE [(Exp.binE BinOp.subOp (OpTyp.numT NumTyp.ratT) (Exp.varE "q_1") (Exp.varE
    "q_2"))])) []),
  (Clause.defD [(Param.expP "r_1" (Typ.numT NumTyp.realT)), (Param.expP "r_2" (Typ.numT
    NumTyp.realT))] [(Arg.expA (Exp.caseE "SUB" (Exp.tupE []))), (Arg.expA (Exp.caseE "REAL"
    (Exp.tupE [(Exp.varE "r_1")]))), (Arg.expA (Exp.caseE "REAL" (Exp.tupE [(Exp.varE "r_2")])))]
    (Exp.caseE "REAL" (Exp.tupE [(Exp.binE BinOp.subOp (OpTyp.numT NumTyp.realT) (Exp.varE "r_1")
    (Exp.varE "r_2"))])) []),
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "MUL" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.binE BinOp.mulOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE
    "n_2"))])) []),
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "MUL" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.binE BinOp.mulOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2"))])) []),
  (Clause.defD [(Param.expP "q_1" (Typ.numT NumTyp.ratT)), (Param.expP "q_2" (Typ.numT
    NumTyp.ratT))] [(Arg.expA (Exp.caseE "MUL" (Exp.tupE []))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE
    [(Exp.varE "q_1")]))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE [(Exp.varE "q_2")])))] (Exp.caseE
    "RAT" (Exp.tupE [(Exp.binE BinOp.mulOp (OpTyp.numT NumTyp.ratT) (Exp.varE "q_1") (Exp.varE
    "q_2"))])) []),
  (Clause.defD [(Param.expP "r_1" (Typ.numT NumTyp.realT)), (Param.expP "r_2" (Typ.numT
    NumTyp.realT))] [(Arg.expA (Exp.caseE "MUL" (Exp.tupE []))), (Arg.expA (Exp.caseE "REAL"
    (Exp.tupE [(Exp.varE "r_1")]))), (Arg.expA (Exp.caseE "REAL" (Exp.tupE [(Exp.varE "r_2")])))]
    (Exp.caseE "REAL" (Exp.tupE [(Exp.binE BinOp.mulOp (OpTyp.numT NumTyp.realT) (Exp.varE "r_1")
    (Exp.varE "r_2"))])) []),
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "DIV" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.divOp (OpTyp.numT NumTyp.ratT) (Exp.cvtE (Exp.varE
    "n_1") NumTyp.natT NumTyp.ratT) (Exp.cvtE (Exp.varE "n_2") NumTyp.natT NumTyp.ratT)) NumTyp.ratT
    NumTyp.natT)])) [(Prem.ifPr (Exp.binE BinOp.andOp OpTyp.boolT (Exp.cmpE CmpOp.neOp OpTyp.boolT
    (Exp.varE "n_2") (Exp.numE (Num.natN 0))) (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.binE BinOp.modOp
    (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE "n_2")) (Exp.numE (Num.natN 0)))))]),
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "DIV" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.divOp (OpTyp.numT NumTyp.ratT) (Exp.cvtE (Exp.varE
    "i_1") NumTyp.intT NumTyp.ratT) (Exp.cvtE (Exp.varE "i_2") NumTyp.intT NumTyp.ratT)) NumTyp.ratT
    NumTyp.intT)])) [(Prem.ifPr (Exp.binE BinOp.andOp OpTyp.boolT (Exp.cmpE CmpOp.neOp OpTyp.boolT
    (Exp.varE "i_2") (Exp.cvtE (Exp.numE (Num.natN 0)) NumTyp.natT NumTyp.intT)) (Exp.cmpE
    CmpOp.eqOp OpTyp.boolT (Exp.binE BinOp.modOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2")) (Exp.cvtE (Exp.numE (Num.natN 0)) NumTyp.natT NumTyp.intT))))]),
  (Clause.defD [(Param.expP "q_1" (Typ.numT NumTyp.ratT)), (Param.expP "q_2" (Typ.numT
    NumTyp.ratT))] [(Arg.expA (Exp.caseE "DIV" (Exp.tupE []))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE
    [(Exp.varE "q_1")]))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE [(Exp.varE "q_2")])))] (Exp.caseE
    "RAT" (Exp.tupE [(Exp.binE BinOp.divOp (OpTyp.numT NumTyp.ratT) (Exp.varE "q_1") (Exp.varE
    "q_2"))])) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "q_2") (Exp.cvtE (Exp.numE
    (Num.natN 0)) NumTyp.natT NumTyp.ratT)))]),
  (Clause.defD [(Param.expP "r_1" (Typ.numT NumTyp.realT)), (Param.expP "r_2" (Typ.numT
    NumTyp.realT))] [(Arg.expA (Exp.caseE "DIV" (Exp.tupE []))), (Arg.expA (Exp.caseE "REAL"
    (Exp.tupE [(Exp.varE "r_1")]))), (Arg.expA (Exp.caseE "REAL" (Exp.tupE [(Exp.varE "r_2")])))]
    (Exp.caseE "REAL" (Exp.tupE [(Exp.binE BinOp.divOp (OpTyp.numT NumTyp.realT) (Exp.varE "r_1")
    (Exp.varE "r_2"))])) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.cvtE (Exp.varE "r_2")
    NumTyp.realT NumTyp.natT) (Exp.numE (Num.natN 0))))]),
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "MOD" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.binE BinOp.modOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE
    "n_2"))])) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "n_2") (Exp.numE (Num.natN
    0))))]),
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "MOD" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.binE BinOp.modOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2"))])) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "i_2") (Exp.cvtE (Exp.numE
    (Num.natN 0)) NumTyp.natT NumTyp.intT)))]),
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "POW" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.binE BinOp.powOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE
    "n_2"))])) []),
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "POW" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.powOp (OpTyp.numT NumTyp.ratT) (Exp.cvtE (Exp.varE
    "i_1") NumTyp.intT NumTyp.ratT) (Exp.varE "i_2")) NumTyp.ratT NumTyp.intT)])) [(Prem.ifPr
    (Exp.cmpE CmpOp.geOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_2") (Exp.cvtE (Exp.numE (Num.natN 0))
    NumTyp.natT NumTyp.intT)))]),
  (Clause.defD [(Param.expP "q_1" (Typ.numT NumTyp.ratT)), (Param.expP "q_2" (Typ.numT
    NumTyp.ratT))] [(Arg.expA (Exp.caseE "POW" (Exp.tupE []))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE
    [(Exp.varE "q_1")]))), (Arg.expA (Exp.caseE "RAT" (Exp.tupE [(Exp.varE "q_2")])))] (Exp.caseE
    "RAT" (Exp.tupE [(Exp.binE BinOp.powOp (OpTyp.numT NumTyp.ratT) (Exp.varE "q_1") (Exp.cvtE
    (Exp.varE "q_2") NumTyp.ratT NumTyp.intT))])) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
    (Exp.cvtE (Exp.varE "q_2") NumTyp.ratT NumTyp.intT) (Exp.cvtE (Exp.varE "q_2") NumTyp.ratT
    NumTyp.intT)))]),
  (Clause.defD [(Param.expP "r_1" (Typ.numT NumTyp.realT)), (Param.expP "r_2" (Typ.numT
    NumTyp.realT))] [(Arg.expA (Exp.caseE "POW" (Exp.tupE []))), (Arg.expA (Exp.caseE "REAL"
    (Exp.tupE [(Exp.varE "r_1")]))), (Arg.expA (Exp.caseE "REAL" (Exp.tupE [(Exp.varE "r_2")])))]
    (Exp.caseE "REAL" (Exp.tupE [(Exp.binE BinOp.powOp (OpTyp.numT NumTyp.realT) (Exp.varE "r_1")
    (Exp.cvtE (Exp.varE "r_2") NumTyp.realT NumTyp.intT))])) [])]

end F

namespace F

/-- Clause 4 of `$numbin` in `fixed`. -/
def nbSubNat : Clause :=
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "SUB" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.subOp (OpTyp.numT NumTyp.intT) (Exp.cvtE (Exp.varE
    "n_1") NumTyp.natT NumTyp.intT) (Exp.cvtE (Exp.varE "n_2") NumTyp.natT NumTyp.intT)) NumTyp.intT
    NumTyp.natT)])) [(Prem.ifPr (Exp.cmpE CmpOp.geOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1")
    (Exp.varE "n_2")))])

/-- Clause 12 of `$numbin` in `fixed`. -/
def nbDivNat : Clause :=
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "DIV" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.divOp (OpTyp.numT NumTyp.ratT) (Exp.cvtE (Exp.varE
    "n_1") NumTyp.natT NumTyp.ratT) (Exp.cvtE (Exp.varE "n_2") NumTyp.natT NumTyp.ratT)) NumTyp.ratT
    NumTyp.natT)])) [(Prem.ifPr (Exp.binE BinOp.andOp OpTyp.boolT (Exp.cmpE CmpOp.neOp OpTyp.boolT
    (Exp.varE "n_2") (Exp.numE (Num.natN 0))) (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.binE BinOp.modOp
    (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE "n_2")) (Exp.numE (Num.natN 0)))))])

/-- Clause 13 of `$numbin` in `fixed`. -/
def nbDivInt : Clause :=
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "DIV" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.cvtE (Exp.binE BinOp.divOp (OpTyp.numT NumTyp.ratT) (Exp.cvtE (Exp.varE
    "i_1") NumTyp.intT NumTyp.ratT) (Exp.cvtE (Exp.varE "i_2") NumTyp.intT NumTyp.ratT)) NumTyp.ratT
    NumTyp.intT)])) [(Prem.ifPr (Exp.binE BinOp.andOp OpTyp.boolT (Exp.cmpE CmpOp.neOp OpTyp.boolT
    (Exp.varE "i_2") (Exp.cvtE (Exp.numE (Num.natN 0)) NumTyp.natT NumTyp.intT)) (Exp.cmpE
    CmpOp.eqOp OpTyp.boolT (Exp.binE BinOp.modOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2")) (Exp.cvtE (Exp.numE (Num.natN 0)) NumTyp.natT NumTyp.intT))))])

/-- Clause 16 of `$numbin` in `fixed`. -/
def nbModNat : Clause :=
  (Clause.defD [(Param.expP "n_1" (Typ.numT NumTyp.natT)), (Param.expP "n_2" (Typ.numT
    NumTyp.natT))] [(Arg.expA (Exp.caseE "MOD" (Exp.tupE []))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE
    [(Exp.varE "n_1")]))), (Arg.expA (Exp.caseE "NAT" (Exp.tupE [(Exp.varE "n_2")])))] (Exp.caseE
    "NAT" (Exp.tupE [(Exp.binE BinOp.modOp (OpTyp.numT NumTyp.natT) (Exp.varE "n_1") (Exp.varE
    "n_2"))])) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "n_2") (Exp.numE (Num.natN
    0))))])

/-- Clause 17 of `$numbin` in `fixed`. -/
def nbModInt : Clause :=
  (Clause.defD [(Param.expP "i_1" (Typ.numT NumTyp.intT)), (Param.expP "i_2" (Typ.numT
    NumTyp.intT))] [(Arg.expA (Exp.caseE "MOD" (Exp.tupE []))), (Arg.expA (Exp.caseE "INT" (Exp.tupE
    [(Exp.varE "i_1")]))), (Arg.expA (Exp.caseE "INT" (Exp.tupE [(Exp.varE "i_2")])))] (Exp.caseE
    "INT" (Exp.tupE [(Exp.binE BinOp.modOp (OpTyp.numT NumTyp.intT) (Exp.varE "i_1") (Exp.varE
    "i_2"))])) [(Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "i_2") (Exp.cvtE (Exp.numE
    (Num.natN 0)) NumTyp.natT NumTyp.intT)))])

end F

end Silmaril.Wasm.SpecTec.Meta.Rules
