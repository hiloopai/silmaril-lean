module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Ref

/-!
# Round 6: the rules of the validation group, verbatim

The rule lists of the ten relations of the pinned script's validation group (definition 334) that
`Reftype_ok {}` and `Reftype_sub {}` reach, copied verbatim from
`Raw/…/Scripts/Wasm30/Original/Part1.lean` and located in `simEnv B` by a kernel `rfl`
(`findRel_*`), and the inversion of `DDerivesB` at a relation whose rules are known
(`dderivesB_inv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round6.Reading

variable {B : Builtins}

/-- The rules of `Heaptype_ok`. -/
def heaptypeOkRules : List Rule :=
  [(Rule.ruleD "abs" [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "absheaptype" (Typ.varT "absheaptype" []))] "%|-%:OK" (Exp.tupE [(Exp.varE "C"),
  (Exp.subE (Exp.varE "absheaptype") (Typ.varT "absheaptype" []) (Typ.varT "heaptype" []))]) []),
  (Rule.ruleD "typeuse" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "typeuse" (Typ.varT "typeuse"
  []))] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.subE (Exp.varE "typeuse") (Typ.varT "typeuse" [])
  (Typ.varT "heaptype" []))]) [(Prem.rulePr "Typeuse_ok" [] "%|-%:OK" (Exp.tupE [(Exp.varE "C"),
  (Exp.varE "typeuse")]))]), (Rule.ruleD "bot" [(Param.expP "C" (Typ.varT "context" []))] "%|-%:OK"
  (Exp.tupE [(Exp.varE "C"), (Exp.caseE "BOT" (Exp.tupE []))]) [])]

set_option maxRecDepth 100000 in
/-- `Heaptype_ok` in `simEnv B`. -/
theorem findRel_heaptypeOk : ∃ t, (simEnv B).findRel? "Heaptype_ok" = some ([], "%|-%:OK", t, heaptypeOkRules) :=
  ⟨_, rfl⟩

/-- The rules of `Typeuse_ok`. -/
def typeuseOkRules : List Rule :=
  [(Rule.ruleD "typeidx" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "typeidx" (Typ.varT "typeidx" [])), (Param.expP "dt" (Typ.varT "deftype"
  []))] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "_IDX" (Exp.varE "typeidx"))]) [(Prem.ifPr
  (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.idxE (Exp.dotE (Exp.varE "C") "TYPES") (Exp.projE (Exp.uncaseE
  (Exp.varE "typeidx") "%") (0 : Int))) (Exp.varE "dt")))]), (Rule.ruleD "rec" [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "i" (Typ.varT "n" [])), (Param.expP "st" (Typ.varT "subtype" []))] "%|-%:OK"
  (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.varE "i"))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
  (Exp.idxE (Exp.dotE (Exp.varE "C") "RECS") (Exp.varE "i")) (Exp.varE "st")))]), (Rule.ruleD "deftype"
  [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "deftype" (Typ.varT "deftype" []))] "%|-%:OK"
  (Exp.tupE [(Exp.varE "C"), (Exp.subE (Exp.varE "deftype") (Typ.varT "deftype" []) (Typ.varT "typeuse"
  []))]) [(Prem.rulePr "Deftype_ok" [] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.varE "deftype")]))])]

set_option maxRecDepth 100000 in
/-- `Typeuse_ok` in `simEnv B`. -/
theorem findRel_typeuseOk : ∃ t, (simEnv B).findRel? "Typeuse_ok" = some ([], "%|-%:OK", t, typeuseOkRules) :=
  ⟨_, rfl⟩

/-- The rules of `Deftype_ok`. -/
def deftypeOkRules : List Rule :=
  [(Rule.ruleD "" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "rectype" (Typ.varT "rectype"
  [])), (Param.expP "i" (Typ.varT "n" [])), (Param.expP "n" (Typ.varT "n" [])), (Param.expP "subtype*"
  (Typ.iterT (Typ.varT "subtype" []) Iter.list))] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "_DEF"
  (Exp.tupE [(Exp.varE "rectype"), (Exp.varE "i")]))]) [(Prem.rulePr "Rectype_ok2" [] "%|-%:%" (Exp.tupE
  [(Exp.compE (Exp.strE [(ExpField.mk "TYPES" (Exp.listE [])), (ExpField.mk "TAGS" (Exp.listE [])),
  (ExpField.mk "GLOBALS" (Exp.listE [])), (ExpField.mk "MEMS" (Exp.listE [])), (ExpField.mk "TABLES"
  (Exp.listE [])), (ExpField.mk "FUNCS" (Exp.listE [])), (ExpField.mk "DATAS" (Exp.listE [])), (ExpField.mk "ELEMS"
  (Exp.listE [])), (ExpField.mk "LOCALS" (Exp.listE [])), (ExpField.mk "LABELS" (Exp.listE [])),
  (ExpField.mk "RETURN" (Exp.optE none)), (ExpField.mk "REFS" (Exp.listE [])), (ExpField.mk "RECS"
  (Exp.iterE (Exp.varE "subtype") (IterExp.mk (Iter.listN (Exp.varE "n") (@Option.none String)) [(Dom.mk "subtype"
  (Exp.varE "subtype*"))])))]) (Exp.varE "C")), (Exp.varE "rectype"), (Exp.caseE "OK" (Exp.numE (Num.natN 0)))])),
  (Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.varE "rectype") (Exp.caseE "REC" (Exp.caseE "%"
  (Exp.tupE [(Exp.iterE (Exp.varE "subtype") (IterExp.mk (Iter.listN (Exp.varE "n") (@Option.none String))
  [(Dom.mk "subtype" (Exp.varE "subtype*"))]))]))))), (Prem.ifPr (Exp.cmpE CmpOp.ltOp (OpTyp.numT NumTyp.natT)
  (Exp.varE "i") (Exp.varE "n")))])]

set_option maxRecDepth 100000 in
/-- `Deftype_ok` in `simEnv B`. -/
theorem findRel_deftypeOk : ∃ t, (simEnv B).findRel? "Deftype_ok" = some ([], "%|-%:OK", t, deftypeOkRules) :=
  ⟨_, rfl⟩

/-- The rules of `Rectype_ok2`. -/
def rectypeOk2Rules : List Rule :=
  [(Rule.ruleD "empty" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "i"
  (Typ.numT NumTyp.natT))] "%|-%:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.caseE "%" (Exp.tupE
  [(Exp.listE [])]))), (Exp.caseE "OK" (Exp.varE "i"))]) []), (Rule.ruleD "cons" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "subtype_1" (Typ.varT "subtype" [])), (Param.expP "subtype*"
  (Typ.iterT (Typ.varT "subtype" []) Iter.list)), (Param.expP "i" (Typ.numT NumTyp.natT))] "%|-%:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.caseE "%" (Exp.tupE [(Exp.catE (Exp.listE [(Exp.varE "subtype_1")])
  (Exp.iterE (Exp.varE "subtype") (IterExp.mk Iter.list [(Dom.mk "subtype" (Exp.varE "subtype*"))])))]))),
  (Exp.caseE "OK" (Exp.varE "i"))]) [(Prem.rulePr "Subtype_ok2" [] "%|-%:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.varE "subtype_1"), (Exp.caseE "OK" (Exp.varE "i"))])), (Prem.rulePr "Rectype_ok2" [] "%|-%:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "subtype")
  (IterExp.mk Iter.list [(Dom.mk "subtype" (Exp.varE "subtype*"))]))]))), (Exp.caseE "OK" (Exp.binE BinOp.addOp
  (OpTyp.numT NumTyp.natT) (Exp.varE "i") (Exp.numE (Num.natN 1))))]))])]

set_option maxRecDepth 100000 in
/-- `Rectype_ok2` in `simEnv B`. -/
theorem findRel_rectypeOk2 : ∃ t, (simEnv B).findRel? "Rectype_ok2" = some ([], "%|-%:%", t, rectypeOk2Rules) :=
  ⟨_, rfl⟩

/-- The rules of `Subtype_ok2`. -/
def subtypeOk2Rules : List Rule :=
  [(Rule.ruleD "" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "typeuse*" (Typ.iterT (Typ.varT "typeuse" []) Iter.list)),
  (Param.expP "comptype" (Typ.varT "comptype" [])), (Param.expP "i" (Typ.numT NumTyp.natT)), (Param.expP "comptype'*"
  (Typ.iterT (Typ.varT "comptype" []) Iter.list)), (Param.expP "typeuse'**" (Typ.iterT (Typ.iterT
  (Typ.varT "typeuse" []) Iter.list) Iter.list))] "%|-%:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "SUB"
  (Exp.tupE [(Exp.iterE (Exp.caseE "FINAL" (Exp.tupE [])) (IterExp.mk Iter.opt [])), (Exp.iterE (Exp.varE "typeuse")
  (IterExp.mk Iter.list [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])), (Exp.varE "comptype")])), (Exp.caseE "OK"
  (Exp.varE "i"))]) [(Prem.ifPr (Exp.cmpE CmpOp.leOp (OpTyp.numT NumTyp.natT) (Exp.lenE (Exp.iterE
  (Exp.varE "typeuse") (IterExp.mk Iter.list [(Dom.mk "typeuse" (Exp.varE "typeuse*"))]))) (Exp.numE
  (Num.natN 1)))), (Prem.iterPr (Prem.rulePr "Typeuse_ok" [] "%|-%:OK" (Exp.tupE [(Exp.varE "C"),
  (Exp.varE "typeuse")])) (IterExp.mk Iter.list [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])), (Prem.iterPr
  (Prem.ifPr (Exp.callE "before" [(Arg.expA (Exp.varE "typeuse")), (Arg.expA (Exp.varE "i"))])) (IterExp.mk Iter.list
  [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])), (Prem.iterPr (Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
  (Exp.callE "unrollht_" [(Arg.expA (Exp.varE "C")), (Arg.expA (Exp.subE (Exp.varE "typeuse") (Typ.varT "typeuse"
  []) (Typ.varT "heaptype" [])))]) (Exp.caseE "SUB" (Exp.tupE [(Exp.optE none), (Exp.iterE (Exp.varE "typeuse'")
  (IterExp.mk Iter.list [(Dom.mk "typeuse'" (Exp.varE "typeuse'*"))])), (Exp.varE "comptype'")]))))
  (IterExp.mk Iter.list [(Dom.mk "comptype'" (Exp.varE "comptype'*")), (Dom.mk "typeuse" (Exp.varE "typeuse*")),
  (Dom.mk "typeuse'*" (Exp.varE "typeuse'**"))])), (Prem.rulePr "Comptype_ok" [] "%|-%:OK" (Exp.tupE
  [(Exp.varE "C"), (Exp.varE "comptype")])), (Prem.iterPr (Prem.rulePr "Comptype_sub" [] "%|-%<:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.varE "comptype"), (Exp.varE "comptype'")])) (IterExp.mk Iter.list
  [(Dom.mk "comptype'" (Exp.varE "comptype'*"))]))])]

set_option maxRecDepth 100000 in
/-- `Subtype_ok2` in `simEnv B`. -/
theorem findRel_subtypeOk2 : ∃ t, (simEnv B).findRel? "Subtype_ok2" = some ([], "%|-%:%", t, subtypeOk2Rules) :=
  ⟨_, rfl⟩

/-- The rules of `Comptype_sub`. -/
def comptypeSubRules : List Rule :=
  [(Rule.ruleD "struct" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "ft_1*" (Typ.iterT
  (Typ.varT "fieldtype" []) Iter.list)), (Param.expP "ft'_1*" (Typ.iterT (Typ.varT "fieldtype" []) Iter.list)),
  (Param.expP "ft_2*" (Typ.iterT (Typ.varT "fieldtype" []) Iter.list))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.caseE "STRUCT" (Exp.caseE "%" (Exp.tupE [(Exp.catE (Exp.iterE (Exp.varE "ft_1") (IterExp.mk Iter.list
  [(Dom.mk "ft_1" (Exp.varE "ft_1*"))])) (Exp.iterE (Exp.varE "ft'_1") (IterExp.mk Iter.list [(Dom.mk "ft'_1"
  (Exp.varE "ft'_1*"))])))]))), (Exp.caseE "STRUCT" (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "ft_2")
  (IterExp.mk Iter.list [(Dom.mk "ft_2" (Exp.varE "ft_2*"))]))])))]) [(Prem.iterPr (Prem.rulePr "Fieldtype_sub"
  [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "ft_1"), (Exp.varE "ft_2")])) (IterExp.mk Iter.list
  [(Dom.mk "ft_1" (Exp.varE "ft_1*")), (Dom.mk "ft_2" (Exp.varE "ft_2*"))]))]), (Rule.ruleD "array"
  [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "ft_1" (Typ.varT "fieldtype" [])), (Param.expP "ft_2"
  (Typ.varT "fieldtype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "ARRAY" (Exp.varE "ft_1")),
  (Exp.caseE "ARRAY" (Exp.varE "ft_2"))]) [(Prem.rulePr "Fieldtype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.varE "ft_1"), (Exp.varE "ft_2")]))]), (Rule.ruleD "func" [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "t_11*" (Typ.iterT (Typ.varT "valtype" []) Iter.list)), (Param.expP "t_12*" (Typ.iterT
  (Typ.varT "valtype" []) Iter.list)), (Param.expP "t_21*" (Typ.iterT (Typ.varT "valtype" []) Iter.list)),
  (Param.expP "t_22*" (Typ.iterT (Typ.varT "valtype" []) Iter.list))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.caseE "FUNC%->%" (Exp.tupE [(Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_11") (IterExp.mk Iter.list
  [(Dom.mk "t_11" (Exp.varE "t_11*"))]))])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_12")
  (IterExp.mk Iter.list [(Dom.mk "t_12" (Exp.varE "t_12*"))]))]))])), (Exp.caseE "FUNC%->%" (Exp.tupE
  [(Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_21") (IterExp.mk Iter.list [(Dom.mk "t_21" (Exp.varE "t_21*"))]))])),
  (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_22") (IterExp.mk Iter.list [(Dom.mk "t_22" (Exp.varE "t_22*"))]))]))]))])
  [(Prem.rulePr "Resulttype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "%" (Exp.tupE
  [(Exp.iterE (Exp.varE "t_21") (IterExp.mk Iter.list [(Dom.mk "t_21" (Exp.varE "t_21*"))]))])),
  (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_11") (IterExp.mk Iter.list [(Dom.mk "t_11" (Exp.varE "t_11*"))]))]))])),
  (Prem.rulePr "Resulttype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "%" (Exp.tupE
  [(Exp.iterE (Exp.varE "t_12") (IterExp.mk Iter.list [(Dom.mk "t_12" (Exp.varE "t_12*"))]))])),
  (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_22") (IterExp.mk Iter.list [(Dom.mk "t_22" (Exp.varE "t_22*"))]))]))]))])]

set_option maxRecDepth 100000 in
/-- `Comptype_sub` in `simEnv B`. -/
theorem findRel_comptypeSub : ∃ t, (simEnv B).findRel? "Comptype_sub" = some ([], "%|-%<:%", t, comptypeSubRules) :=
  ⟨_, rfl⟩

/-- `Deftype_sub/refl`. -/
def dsRefl : Rule :=
  (Rule.ruleD "refl" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "deftype_1" (Typ.varT "deftype" [])), (Param.expP "deftype_2"
  (Typ.varT "deftype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "deftype_1"), (Exp.varE "deftype_2")])
  [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.callE "clos_deftype" [(Arg.expA (Exp.varE "C")),
  (Arg.expA (Exp.varE "deftype_1"))]) (Exp.callE "clos_deftype" [(Arg.expA (Exp.varE "C")), (Arg.expA
  (Exp.varE "deftype_2"))])))])

/-- `Deftype_sub/super`. -/
def dsSuper : Rule :=
  (Rule.ruleD "super" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "deftype_1"
  (Typ.varT "deftype" [])), (Param.expP "deftype_2" (Typ.varT "deftype" [])), (Param.expP "final?"
  (Typ.iterT (Typ.varT "final" []) Iter.opt)), (Param.expP "typeuse*" (Typ.iterT (Typ.varT "typeuse"
  []) Iter.list)), (Param.expP "ct" (Typ.varT "comptype" [])), (Param.expP "i" (Typ.numT NumTyp.natT))] "%|-%<:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.varE "deftype_1"), (Exp.varE "deftype_2")]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT
  (Exp.callE "unrolldt" [(Arg.expA (Exp.varE "deftype_1"))]) (Exp.caseE "SUB" (Exp.tupE [(Exp.iterE
  (Exp.varE "final") (IterExp.mk Iter.opt [(Dom.mk "final" (Exp.varE "final?"))])), (Exp.iterE (Exp.varE "typeuse")
  (IterExp.mk Iter.list [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])), (Exp.varE "ct")])))), (Prem.rulePr "Heaptype_sub"
  [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.subE (Exp.idxE (Exp.iterE (Exp.varE "typeuse") (IterExp.mk Iter.list
  [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])) (Exp.varE "i")) (Typ.varT "typeuse" []) (Typ.varT "heaptype"
  [])), (Exp.subE (Exp.varE "deftype_2") (Typ.varT "deftype" []) (Typ.varT "heaptype" []))]))])

/-- The rules of `Deftype_sub`. -/
def deftypeSubRules : List Rule := [dsRefl, dsSuper]

set_option maxRecDepth 100000 in
/-- `Deftype_sub` in `simEnv B`. -/
theorem findRel_deftypeSub : ∃ t, (simEnv B).findRel? "Deftype_sub" = some ([], "%|-%<:%", t, deftypeSubRules) :=
  ⟨_, rfl⟩

/-- `Heaptype_sub/refl`. -/
def hsRefl : Rule :=
  (Rule.ruleD "refl" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "heaptype" (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.varE "heaptype"), (Exp.varE "heaptype")]) [])

/-- `Heaptype_sub/trans`. -/
def hsTrans : Rule :=
  (Rule.ruleD "trans" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "heaptype_1" (Typ.varT "heaptype" [])), (Param.expP "heaptype_2"
  (Typ.varT "heaptype" [])), (Param.expP "heaptype'" (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.varE "heaptype_1"), (Exp.varE "heaptype_2")]) [(Prem.rulePr "Heaptype_ok"
  [] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype'")])), (Prem.rulePr "Heaptype_sub"
  [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype_1"), (Exp.varE "heaptype'")])), (Prem.rulePr "Heaptype_sub"
  [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype'"), (Exp.varE "heaptype_2")]))])

/-- `Heaptype_sub/eq-any`. -/
def hsEqAny : Rule :=
  (Rule.ruleD "eq-any" [(Param.expP "C" (Typ.varT "context" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.caseE "EQ" (Exp.tupE [])), (Exp.caseE "ANY" (Exp.tupE []))]) [])

/-- `Heaptype_sub/i31-eq`. -/
def hsI31Eq : Rule :=
  (Rule.ruleD "i31-eq" [(Param.expP "C"
  (Typ.varT "context" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "I31" (Exp.tupE [])),
  (Exp.caseE "EQ" (Exp.tupE []))]) [])

/-- `Heaptype_sub/struct-eq`. -/
def hsStructEq : Rule :=
  (Rule.ruleD "struct-eq" [(Param.expP "C" (Typ.varT "context"
  []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "STRUCT" (Exp.tupE [])), (Exp.caseE "EQ"
  (Exp.tupE []))]) [])

/-- `Heaptype_sub/array-eq`. -/
def hsArrayEq : Rule :=
  (Rule.ruleD "array-eq" [(Param.expP "C" (Typ.varT "context" []))] "%|-%<:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.caseE "ARRAY" (Exp.tupE [])), (Exp.caseE "EQ" (Exp.tupE []))])
  [])

/-- `Heaptype_sub/struct`. -/
def hsStruct : Rule :=
  (Rule.ruleD "struct" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "deftype" (Typ.varT "deftype"
  [])), (Param.expP "fieldtype*" (Typ.iterT (Typ.varT "fieldtype" []) Iter.list))] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.subE (Exp.varE "deftype") (Typ.varT "deftype" []) (Typ.varT "heaptype" [])),
  (Exp.caseE "STRUCT" (Exp.tupE []))]) [(Prem.rulePr "Expand" [] "%~~%" (Exp.tupE [(Exp.varE "deftype"),
  (Exp.caseE "STRUCT" (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "fieldtype") (IterExp.mk Iter.list
  [(Dom.mk "fieldtype" (Exp.varE "fieldtype*"))]))])))]))])

/-- `Heaptype_sub/array`. -/
def hsArray : Rule :=
  (Rule.ruleD "array" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "deftype" (Typ.varT "deftype" [])), (Param.expP "fieldtype"
  (Typ.varT "fieldtype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.subE (Exp.varE "deftype")
  (Typ.varT "deftype" []) (Typ.varT "heaptype" [])), (Exp.caseE "ARRAY" (Exp.tupE []))]) [(Prem.rulePr "Expand"
  [] "%~~%" (Exp.tupE [(Exp.varE "deftype"), (Exp.caseE "ARRAY" (Exp.varE "fieldtype"))]))])

/-- `Heaptype_sub/func`. -/
def hsFunc : Rule :=
  (Rule.ruleD "func"
  [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "deftype" (Typ.varT "deftype" [])), (Param.expP "t_1*"
  (Typ.iterT (Typ.varT "valtype" []) Iter.list)), (Param.expP "t_2*" (Typ.iterT (Typ.varT "valtype"
  []) Iter.list))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.subE (Exp.varE "deftype") (Typ.varT "deftype"
  []) (Typ.varT "heaptype" [])), (Exp.caseE "FUNC" (Exp.tupE []))]) [(Prem.rulePr "Expand" [] "%~~%"
  (Exp.tupE [(Exp.varE "deftype"), (Exp.caseE "FUNC%->%" (Exp.tupE [(Exp.caseE "%" (Exp.tupE [(Exp.iterE
  (Exp.varE "t_1") (IterExp.mk Iter.list [(Dom.mk "t_1" (Exp.varE "t_1*"))]))])), (Exp.caseE "%"
  (Exp.tupE [(Exp.iterE (Exp.varE "t_2") (IterExp.mk Iter.list [(Dom.mk "t_2" (Exp.varE "t_2*"))]))]))]))]))])

/-- `Heaptype_sub/def`. -/
def hsDef : Rule :=
  (Rule.ruleD "def" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "deftype_1" (Typ.varT "deftype"
  [])), (Param.expP "deftype_2" (Typ.varT "deftype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.subE
  (Exp.varE "deftype_1") (Typ.varT "deftype" []) (Typ.varT "heaptype" [])), (Exp.subE (Exp.varE "deftype_2")
  (Typ.varT "deftype" []) (Typ.varT "heaptype" []))]) [(Prem.rulePr "Deftype_sub" [] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.varE "deftype_1"), (Exp.varE "deftype_2")]))])

/-- `Heaptype_sub/typeidx-l`. -/
def hsIdxL : Rule :=
  (Rule.ruleD "typeidx-l"
  [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "typeidx" (Typ.varT "typeidx" [])), (Param.expP "heaptype"
  (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "_IDX" (Exp.varE "typeidx")),
  (Exp.varE "heaptype")]) [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.subE
  (Exp.idxE (Exp.dotE (Exp.varE "C") "TYPES") (Exp.projE (Exp.uncaseE (Exp.varE "typeidx") "%") (0 : Int)))
  (Typ.varT "deftype" []) (Typ.varT "heaptype" [])), (Exp.varE "heaptype")]))])

/-- `Heaptype_sub/typeidx-r`. -/
def hsIdxR : Rule :=
  (Rule.ruleD "typeidx-r"
  [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "heaptype" (Typ.varT "heaptype" [])), (Param.expP "typeidx"
  (Typ.varT "typeidx" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype"), (Exp.caseE "_IDX"
  (Exp.varE "typeidx"))]) [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype"),
  (Exp.subE (Exp.idxE (Exp.dotE (Exp.varE "C") "TYPES") (Exp.projE (Exp.uncaseE (Exp.varE "typeidx") "%")
  (0 : Int))) (Typ.varT "deftype" []) (Typ.varT "heaptype" []))]))])

/-- `Heaptype_sub/rec-struct`. -/
def hsRecStruct : Rule :=
  (Rule.ruleD "rec-struct"
  [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "i" (Typ.varT "n" [])), (Param.expP "final?"
  (Typ.iterT (Typ.varT "final" []) Iter.opt)), (Param.expP "fieldtype*" (Typ.iterT (Typ.varT "fieldtype"
  []) Iter.list))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.varE "i")), (Exp.caseE "STRUCT"
  (Exp.tupE []))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.idxE (Exp.dotE (Exp.varE "C") "RECS")
  (Exp.varE "i")) (Exp.caseE "SUB" (Exp.tupE [(Exp.iterE (Exp.varE "final") (IterExp.mk Iter.opt
  [(Dom.mk "final" (Exp.varE "final?"))])), (Exp.listE []), (Exp.caseE "STRUCT" (Exp.caseE "%" (Exp.tupE
  [(Exp.iterE (Exp.varE "fieldtype") (IterExp.mk Iter.list [(Dom.mk "fieldtype" (Exp.varE "fieldtype*"))]))])))]))))])

/-- `Heaptype_sub/rec-array`. -/
def hsRecArray : Rule :=
  (Rule.ruleD "rec-array" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "i" (Typ.varT "n"
  [])), (Param.expP "final?" (Typ.iterT (Typ.varT "final" []) Iter.opt)), (Param.expP "fieldtype"
  (Typ.varT "fieldtype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.varE "i")),
  (Exp.caseE "ARRAY" (Exp.tupE []))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.idxE (Exp.dotE
  (Exp.varE "C") "RECS") (Exp.varE "i")) (Exp.caseE "SUB" (Exp.tupE [(Exp.iterE (Exp.varE "final")
  (IterExp.mk Iter.opt [(Dom.mk "final" (Exp.varE "final?"))])), (Exp.listE []), (Exp.caseE "ARRAY"
  (Exp.varE "fieldtype"))]))))])

/-- `Heaptype_sub/rec-func`. -/
def hsRecFunc : Rule :=
  (Rule.ruleD "rec-func" [(Param.expP "C" (Typ.varT "context" [])),
  (Param.expP "i" (Typ.varT "n" [])), (Param.expP "final?" (Typ.iterT (Typ.varT "final" []) Iter.opt)),
  (Param.expP "t_1*" (Typ.iterT (Typ.varT "valtype" []) Iter.list)), (Param.expP "t_2*" (Typ.iterT
  (Typ.varT "valtype" []) Iter.list))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REC" (Exp.varE "i")),
  (Exp.caseE "FUNC" (Exp.tupE []))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.idxE (Exp.dotE
  (Exp.varE "C") "RECS") (Exp.varE "i")) (Exp.caseE "SUB" (Exp.tupE [(Exp.iterE (Exp.varE "final")
  (IterExp.mk Iter.opt [(Dom.mk "final" (Exp.varE "final?"))])), (Exp.listE []), (Exp.caseE "FUNC%->%"
  (Exp.tupE [(Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_1") (IterExp.mk Iter.list [(Dom.mk "t_1"
  (Exp.varE "t_1*"))]))])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "t_2") (IterExp.mk Iter.list
  [(Dom.mk "t_2" (Exp.varE "t_2*"))]))]))]))]))))])

/-- `Heaptype_sub/rec-sub`. -/
def hsRecSub : Rule :=
  (Rule.ruleD "rec-sub" [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "i" (Typ.varT "n" [])), (Param.expP "typeuse*" (Typ.iterT (Typ.varT "typeuse"
  []) Iter.list)), (Param.expP "j" (Typ.numT NumTyp.natT)), (Param.expP "final?" (Typ.iterT (Typ.varT "final"
  []) Iter.opt)), (Param.expP "ct" (Typ.varT "comptype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.caseE "REC" (Exp.varE "i")), (Exp.subE (Exp.idxE (Exp.iterE (Exp.varE "typeuse") (IterExp.mk Iter.list
  [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])) (Exp.varE "j")) (Typ.varT "typeuse" []) (Typ.varT "heaptype"
  []))]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.idxE (Exp.dotE (Exp.varE "C") "RECS")
  (Exp.varE "i")) (Exp.caseE "SUB" (Exp.tupE [(Exp.iterE (Exp.varE "final") (IterExp.mk Iter.opt
  [(Dom.mk "final" (Exp.varE "final?"))])), (Exp.iterE (Exp.varE "typeuse") (IterExp.mk Iter.list
  [(Dom.mk "typeuse" (Exp.varE "typeuse*"))])), (Exp.varE "ct")]))))])

/-- `Heaptype_sub/none`. -/
def hsNone : Rule :=
  (Rule.ruleD "none" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "heaptype" (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.caseE "NONE" (Exp.tupE [])), (Exp.varE "heaptype")]) [(Prem.rulePr "Heaptype_sub"
  [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype"), (Exp.caseE "ANY" (Exp.tupE []))])),
  (Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "heaptype") (Exp.caseE "BOT" (Exp.tupE []))))])

/-- `Heaptype_sub/nofunc`. -/
def hsNofunc : Rule :=
  (Rule.ruleD "nofunc" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "heaptype" (Typ.varT "heaptype"
  []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "NOFUNC" (Exp.tupE [])), (Exp.varE "heaptype")])
  [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype"), (Exp.caseE "FUNC"
  (Exp.tupE []))])), (Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "heaptype") (Exp.caseE "BOT"
  (Exp.tupE []))))])

/-- `Heaptype_sub/noexn`. -/
def hsNoexn : Rule :=
  (Rule.ruleD "noexn" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "heaptype"
  (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "NOEXN" (Exp.tupE [])),
  (Exp.varE "heaptype")]) [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype"),
  (Exp.caseE "EXN" (Exp.tupE []))])), (Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT (Exp.varE "heaptype")
  (Exp.caseE "BOT" (Exp.tupE []))))])

/-- `Heaptype_sub/noextern`. -/
def hsNoextern : Rule :=
  (Rule.ruleD "noextern" [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "heaptype" (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "NOEXTERN"
  (Exp.tupE [])), (Exp.varE "heaptype")]) [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%" (Exp.tupE [(Exp.varE "C"),
  (Exp.varE "heaptype"), (Exp.caseE "EXTERN" (Exp.tupE []))])), (Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT
  (Exp.varE "heaptype") (Exp.caseE "BOT" (Exp.tupE []))))])

/-- `Heaptype_sub/bot`. -/
def hsBot : Rule :=
  (Rule.ruleD "bot" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "heaptype" (Typ.varT "heaptype" []))] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.caseE "BOT" (Exp.tupE [])), (Exp.varE "heaptype")]) [])

/-- The rules of `Heaptype_sub`. -/
def heaptypeSubRules : List Rule :=
  [hsRefl, hsTrans, hsEqAny, hsI31Eq, hsStructEq, hsArrayEq, hsStruct, hsArray, hsFunc, hsDef, hsIdxL, hsIdxR, hsRecStruct, hsRecArray, hsRecFunc, hsRecSub, hsNone, hsNofunc, hsNoexn, hsNoextern, hsBot]

set_option maxRecDepth 100000 in
/-- `Heaptype_sub` in `simEnv B`. -/
theorem findRel_heaptypeSub : ∃ t, (simEnv B).findRel? "Heaptype_sub" = some ([], "%|-%<:%", t, heaptypeSubRules) :=
  ⟨_, rfl⟩

/-- The rules of `Reftype_sub`. -/
def reftypeSubRules : List Rule :=
  [(Rule.ruleD "nonnull" [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "ht_1" (Typ.varT "heaptype" [])), (Param.expP "ht_2" (Typ.varT "heaptype" []))] "%|-%<:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REF" (Exp.tupE [(Exp.optE none), (Exp.varE "ht_1")])), (Exp.caseE "REF"
  (Exp.tupE [(Exp.optE none), (Exp.varE "ht_2")]))]) [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%" (Exp.tupE
  [(Exp.varE "C"), (Exp.varE "ht_1"), (Exp.varE "ht_2")]))]), (Rule.ruleD "null" [(Param.expP "C"
  (Typ.varT "context" [])), (Param.expP "ht_1" (Typ.varT "heaptype" [])), (Param.expP "ht_2" (Typ.varT "heaptype"
  []))] "%|-%<:%" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REF" (Exp.tupE [(Exp.iterE (Exp.caseE "NULL"
  (Exp.tupE [])) (IterExp.mk Iter.opt [])), (Exp.varE "ht_1")])), (Exp.caseE "REF" (Exp.tupE [(Exp.optE
  (some (Exp.caseE "NULL" (Exp.tupE [])))), (Exp.varE "ht_2")]))]) [(Prem.rulePr "Heaptype_sub" [] "%|-%<:%"
  (Exp.tupE [(Exp.varE "C"), (Exp.varE "ht_1"), (Exp.varE "ht_2")]))])]

set_option maxRecDepth 100000 in
/-- `Reftype_sub` in `simEnv B`. -/
theorem findRel_reftypeSub : ∃ t, (simEnv B).findRel? "Reftype_sub" = some ([], "%|-%<:%", t, reftypeSubRules) :=
  ⟨_, rfl⟩

/-- The rules of `Reftype_ok`. -/
def reftypeOkRules : List Rule :=
  [(Rule.ruleD "" [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "heaptype" (Typ.varT "heaptype"
  []))] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.caseE "REF" (Exp.tupE [(Exp.iterE (Exp.caseE "NULL"
  (Exp.tupE [])) (IterExp.mk Iter.opt [])), (Exp.varE "heaptype")]))]) [(Prem.rulePr "Heaptype_ok"
  [] "%|-%:OK" (Exp.tupE [(Exp.varE "C"), (Exp.varE "heaptype")]))])]

set_option maxRecDepth 100000 in
/-- `Reftype_ok` in `simEnv B`. -/
theorem findRel_reftypeOk : ∃ t, (simEnv B).findRel? "Reftype_ok" = some ([], "%|-%:OK", t, reftypeOkRules) :=
  ⟨_, rfl⟩

/-- **Inversion of `DDerivesB`** at a parameterless relation whose rules are known: some rule
fires, at some alternative of its conclusion, under a typed assignment satisfying its premises. -/
theorem dderivesB_inv {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {v : Value}
    {rules : List Rule} (hx : ∃ t, env.findRel? x = some ([], op, t, rules))
    (h : DDerivesB env O x op [] v) :
    ∃ i nm qs e e' prems σ, rules[i]? = some (.ruleD nm qs op e prems) ∧ e' ∈ conclAlts e ∧
      QuantsOk env (VarEnv.empty.bindVals σ) qs ∧ EvalExp env (VarEnv.empty.bindVals σ) e' v ∧
      ∀ pr ∈ prems, DPremB env O (O x [] i v) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨t, hx⟩ := hx
  cases h with
  | rule hrel hrule halt hps hq he hp =>
    rw [hx] at hrel
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel
    obtain ⟨rfl, -, -, rfl⟩ := hrel
    simp only [bindParams, Option.some.injEq] at hps
    subst hps
    exact ⟨_, _, _, _, _, _, _, hrule, halt, hq, he, hp⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
