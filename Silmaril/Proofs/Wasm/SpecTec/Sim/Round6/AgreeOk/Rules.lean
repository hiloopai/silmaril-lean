module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.RulesBot
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkB.Rules

/-!
# Round 6: the rest of the validation group, located in `simEnv B`

Each lemma locates one rule of the pinned script's validation `rec` group (definition 334) or of
its leaf relations (definitions 324–331) by a kernel `rfl`. Together with track refokbb's
(`RefOkB.Rules`), track reading's (`Reading.Ref`) and track agreety-subintro's
(`AgreeSub.Rules`, `AgreeSub.RulesBot`) these are all the rules a canonical derivation
(`AgreeOk.TyOkB`, `AgreeOk.SubB`) uses:

* validation: `Heaptype_ok/bot`, `Valtype_ok/num`, `vec`, `bot`, `Numtype_ok`, `Vectype_ok`,
  `Packtype_ok`, `Resulttype_ok`, `Storagetype_ok/pack`, `Comptype_ok/array`, `func`;
* subtyping under `RECS`: `Heaptype_sub/rec-struct`, `rec-array`, `rec-func`, `rec-sub`;
* the other sorts: `Valtype_sub/num`, `vec`, `ref`, `bot`, `Numtype_sub`, `Vectype_sub`,
  `Packtype_sub`, `Resulttype_sub`, `Storagetype_sub/val`, `pack`, `Fieldtype_sub/const`, `var`,
  `Comptype_sub/struct`, `array`, `func`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Round6.AgreeSub (ctxP heapP atomE listIterE typeusesE)

variable {B : Builtins}

/-- A variable of sort `x`. -/
def varP (x s : IL.Id) : Param := .expP x (.varT s [])

/-- A list variable of sort `s*`. -/
def listP (x s : IL.Id) : Param := .expP x (.iterT (.varT s []) .list)

/-- A variable `x` of sort `s` used at sort `s'`. -/
def subVarE (x s s' : IL.Id) : Exp := .subE (.varE x) (.varT s []) (.varT s' [])

/-- A premise `r(C, args…)`. -/
def relPrem (r : IL.Id) (op : MixopS) (es : List Exp) : Prem := .rulePr r [] op (.tupE (.varE "C" :: es))

/-- `%(x*)`, a result type written as an iteration. -/
def resE (x : IL.Id) : Exp := .caseE "%" (.tupE [listIterE x])

/-! ## Validation -/

set_option maxRecDepth 100000 in
/-- `Heaptype_ok/bot`. -/
theorem ruleAt_heaptypeOkBot : HasRuleAt (simEnv B) "Heaptype_ok" "%|-%:OK" 2
    (.ruleD "bot" [ctxP] "%|-%:OK" (.tupE [.varE "C", atomE "BOT"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_ok/num`. -/
theorem ruleAt_valtypeOkNum : HasRuleAt (simEnv B) "Valtype_ok" "%|-%:OK" 0
    (.ruleD "num" [ctxP, varP "numtype" "numtype"] "%|-%:OK"
      (.tupE [.varE "C", subVarE "numtype" "numtype" "valtype"])
      [relPrem "Numtype_ok" "%|-%:OK" [.varE "numtype"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_ok/vec`. -/
theorem ruleAt_valtypeOkVec : HasRuleAt (simEnv B) "Valtype_ok" "%|-%:OK" 1
    (.ruleD "vec" [ctxP, varP "vectype" "vectype"] "%|-%:OK"
      (.tupE [.varE "C", subVarE "vectype" "vectype" "valtype"])
      [relPrem "Vectype_ok" "%|-%:OK" [.varE "vectype"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_ok/bot`. -/
theorem ruleAt_valtypeOkBot : HasRuleAt (simEnv B) "Valtype_ok" "%|-%:OK" 3
    (.ruleD "bot" [ctxP] "%|-%:OK" (.tupE [.varE "C", atomE "BOT"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Numtype_ok`. -/
theorem ruleAt_numtypeOk : HasRuleAt (simEnv B) "Numtype_ok" "%|-%:OK" 0
    (.ruleD "" [ctxP, varP "numtype" "numtype"] "%|-%:OK" (.tupE [.varE "C", .varE "numtype"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Vectype_ok`. -/
theorem ruleAt_vectypeOk : HasRuleAt (simEnv B) "Vectype_ok" "%|-%:OK" 0
    (.ruleD "" [ctxP, varP "vectype" "vectype"] "%|-%:OK" (.tupE [.varE "C", .varE "vectype"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Packtype_ok`. -/
theorem ruleAt_packtypeOk : HasRuleAt (simEnv B) "Packtype_ok" "%|-%:OK" 0
    (.ruleD "" [ctxP, varP "packtype" "packtype"] "%|-%:OK"
      (.tupE [.varE "C", .varE "packtype"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Resulttype_ok`. -/
theorem ruleAt_resulttypeOk : HasRuleAt (simEnv B) "Resulttype_ok" "%|-%:OK" 0
    (.ruleD "" [ctxP, listP "t*" "valtype"] "%|-%:OK" (.tupE [.varE "C", resE "t"])
      [.iterPr (relPrem "Valtype_ok" "%|-%:OK" [.varE "t"]) (.mk .list [.mk "t" (.varE "t*")])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Storagetype_ok/pack`. -/
theorem ruleAt_storagetypeOkPack : HasRuleAt (simEnv B) "Storagetype_ok" "%|-%:OK" 1
    (.ruleD "pack" [ctxP, varP "packtype" "packtype"] "%|-%:OK"
      (.tupE [.varE "C", subVarE "packtype" "packtype" "storagetype"])
      [relPrem "Packtype_ok" "%|-%:OK" [.varE "packtype"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Comptype_ok/array`. -/
theorem ruleAt_comptypeOkArray : HasRuleAt (simEnv B) "Comptype_ok" "%|-%:OK" 1
    (.ruleD "array" [ctxP, varP "fieldtype" "fieldtype"] "%|-%:OK"
      (.tupE [.varE "C", .caseE "ARRAY" (.varE "fieldtype")])
      [relPrem "Fieldtype_ok" "%|-%:OK" [.varE "fieldtype"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Comptype_ok/func`. -/
theorem ruleAt_comptypeOkFunc : HasRuleAt (simEnv B) "Comptype_ok" "%|-%:OK" 2
    (.ruleD "func" [ctxP, listP "t_1*" "valtype", listP "t_2*" "valtype"] "%|-%:OK"
      (.tupE [.varE "C", .caseE "FUNC%->%" (.tupE [resE "t_1", resE "t_2"])])
      [relPrem "Resulttype_ok" "%|-%:OK" [resE "t_1"],
       relPrem "Resulttype_ok" "%|-%:OK" [resE "t_2"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Subtyping under `RECS` -/

/-- `C.RECS[i] = SUB final? eps ct`, the premise of `rec-struct`/`rec-array`/`rec-func`. -/
def recNilPrem (ct : Exp) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i"))
    (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
      .listE [], ct])))

/-- The common parameters of `rec-struct`/`rec-array`/`rec-func`. -/
def recParams : List Param :=
  [ctxP, varP "i" "n", .expP "final?" (.iterT (.varT "final" []) .opt)]

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/rec-struct`. -/
theorem ruleAt_recStruct : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 12
    (.ruleD "rec-struct" (recParams ++ [listP "fieldtype*" "fieldtype"]) "%|-%<:%"
      (.tupE [.varE "C", .caseE "REC" (.varE "i"), atomE "STRUCT"])
      [recNilPrem (.caseE "STRUCT" (resE "fieldtype"))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/rec-array`. -/
theorem ruleAt_recArray : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 13
    (.ruleD "rec-array" (recParams ++ [varP "fieldtype" "fieldtype"]) "%|-%<:%"
      (.tupE [.varE "C", .caseE "REC" (.varE "i"), atomE "ARRAY"])
      [recNilPrem (.caseE "ARRAY" (.varE "fieldtype"))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/rec-func`. -/
theorem ruleAt_recFunc : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 14
    (.ruleD "rec-func" (recParams ++ [listP "t_1*" "valtype", listP "t_2*" "valtype"]) "%|-%<:%"
      (.tupE [.varE "C", .caseE "REC" (.varE "i"), atomE "FUNC"])
      [recNilPrem (.caseE "FUNC%->%" (.tupE [resE "t_1", resE "t_2"]))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/rec-sub`. -/
theorem ruleAt_recSub : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 15
    (.ruleD "rec-sub" [ctxP, varP "i" "n", listP "typeuse*" "typeuse", .expP "j" (.numT .natT),
        .expP "final?" (.iterT (.varT "final" []) .opt), varP "ct" "comptype"] "%|-%<:%"
      (.tupE [.varE "C", .caseE "REC" (.varE "i"),
        .subE (.idxE typeusesE (.varE "j")) (.varT "typeuse" []) (.varT "heaptype" [])])
      [.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i"))
        (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
          typeusesE, .varE "ct"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Subtyping at the other sorts -/

/-- A rule `x_1 <: x_2` of sort `s` at sort `s'`, from `r(C, x_1, x_2)`. -/
def subsumeRule (nm x s s' r : IL.Id) : Rule :=
  .ruleD nm [ctxP, varP (x ++ "_1") s, varP (x ++ "_2") s] "%|-%<:%"
    (.tupE [.varE "C", subVarE (x ++ "_1") s s', subVarE (x ++ "_2") s s'])
    [relPrem r "%|-%<:%" [.varE (x ++ "_1"), .varE (x ++ "_2")]]

/-- A reflexive leaf rule `C ⊢ x <: x`. -/
def leafSubRule (x : IL.Id) : Rule :=
  .ruleD "" [ctxP, varP x x] "%|-%<:%" (.tupE [.varE "C", .varE x, .varE x]) []

set_option maxRecDepth 100000 in
/-- `Valtype_sub/num`. -/
theorem ruleAt_valtypeSubNum : HasRuleAt (simEnv B) "Valtype_sub" "%|-%<:%" 0
    (subsumeRule "num" "numtype" "numtype" "valtype" "Numtype_sub") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_sub/vec`. -/
theorem ruleAt_valtypeSubVec : HasRuleAt (simEnv B) "Valtype_sub" "%|-%<:%" 1
    (subsumeRule "vec" "vectype" "vectype" "valtype" "Vectype_sub") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_sub/ref`. -/
theorem ruleAt_valtypeSubRef : HasRuleAt (simEnv B) "Valtype_sub" "%|-%<:%" 2
    (subsumeRule "ref" "reftype" "reftype" "valtype" "Reftype_sub") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_sub/bot`. -/
theorem ruleAt_valtypeSubBot : HasRuleAt (simEnv B) "Valtype_sub" "%|-%<:%" 3
    (.ruleD "bot" [ctxP, varP "valtype" "valtype"] "%|-%<:%"
      (.tupE [.varE "C", atomE "BOT", .varE "valtype"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Numtype_sub`. -/
theorem ruleAt_numtypeSub : HasRuleAt (simEnv B) "Numtype_sub" "%|-%<:%" 0
    (leafSubRule "numtype") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Vectype_sub`. -/
theorem ruleAt_vectypeSub : HasRuleAt (simEnv B) "Vectype_sub" "%|-%<:%" 0
    (leafSubRule "vectype") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Packtype_sub`. -/
theorem ruleAt_packtypeSub : HasRuleAt (simEnv B) "Packtype_sub" "%|-%<:%" 0
    (leafSubRule "packtype") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Resulttype_sub`. -/
theorem ruleAt_resulttypeSub : HasRuleAt (simEnv B) "Resulttype_sub" "%|-%<:%" 0
    (.ruleD "" [ctxP, listP "t_1*" "valtype", listP "t_2*" "valtype"] "%|-%<:%"
      (.tupE [.varE "C", resE "t_1", resE "t_2"])
      [.iterPr (relPrem "Valtype_sub" "%|-%<:%" [.varE "t_1", .varE "t_2"])
        (.mk .list [.mk "t_1" (.varE "t_1*"), .mk "t_2" (.varE "t_2*")])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Storagetype_sub/val`. -/
theorem ruleAt_storagetypeSubVal : HasRuleAt (simEnv B) "Storagetype_sub" "%|-%<:%" 0
    (subsumeRule "val" "valtype" "valtype" "storagetype" "Valtype_sub") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Storagetype_sub/pack`. -/
theorem ruleAt_storagetypeSubPack : HasRuleAt (simEnv B) "Storagetype_sub" "%|-%<:%" 1
    (subsumeRule "pack" "packtype" "packtype" "storagetype" "Packtype_sub") :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `MUT?` as a fixed option. -/
def mutOptE (b : Bool) : Exp := if b then .optE (some (atomE "MUT")) else .optE none

set_option maxRecDepth 100000 in
/-- `Fieldtype_sub/const`. -/
theorem ruleAt_fieldtypeSubConst : HasRuleAt (simEnv B) "Fieldtype_sub" "%|-%<:%" 0
    (.ruleD "const" [ctxP, varP "zt_1" "storagetype", varP "zt_2" "storagetype"] "%|-%<:%"
      (.tupE [.varE "C", .caseE "%%" (.tupE [mutOptE false, .varE "zt_1"]),
        .caseE "%%" (.tupE [mutOptE false, .varE "zt_2"])])
      [relPrem "Storagetype_sub" "%|-%<:%" [.varE "zt_1", .varE "zt_2"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Fieldtype_sub/var`. -/
theorem ruleAt_fieldtypeSubVar : HasRuleAt (simEnv B) "Fieldtype_sub" "%|-%<:%" 1
    (.ruleD "var" [ctxP, varP "zt_1" "storagetype", varP "zt_2" "storagetype"] "%|-%<:%"
      (.tupE [.varE "C", .caseE "%%" (.tupE [mutOptE true, .varE "zt_1"]),
        .caseE "%%" (.tupE [mutOptE true, .varE "zt_2"])])
      [relPrem "Storagetype_sub" "%|-%<:%" [.varE "zt_1", .varE "zt_2"],
       relPrem "Storagetype_sub" "%|-%<:%" [.varE "zt_2", .varE "zt_1"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Comptype_sub/struct`. -/
theorem ruleAt_comptypeSubStruct : HasRuleAt (simEnv B) "Comptype_sub" "%|-%<:%" 0
    (.ruleD "struct" [ctxP, listP "ft_1*" "fieldtype", listP "ft'_1*" "fieldtype",
        listP "ft_2*" "fieldtype"] "%|-%<:%"
      (.tupE [.varE "C",
        .caseE "STRUCT" (.caseE "%" (.tupE [.catE (listIterE "ft_1") (listIterE "ft'_1")])),
        .caseE "STRUCT" (resE "ft_2")])
      [.iterPr (relPrem "Fieldtype_sub" "%|-%<:%" [.varE "ft_1", .varE "ft_2"])
        (.mk .list [.mk "ft_1" (.varE "ft_1*"), .mk "ft_2" (.varE "ft_2*")])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Comptype_sub/array`. -/
theorem ruleAt_comptypeSubArray : HasRuleAt (simEnv B) "Comptype_sub" "%|-%<:%" 1
    (.ruleD "array" [ctxP, varP "ft_1" "fieldtype", varP "ft_2" "fieldtype"] "%|-%<:%"
      (.tupE [.varE "C", .caseE "ARRAY" (.varE "ft_1"), .caseE "ARRAY" (.varE "ft_2")])
      [relPrem "Fieldtype_sub" "%|-%<:%" [.varE "ft_1", .varE "ft_2"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Comptype_sub/func`. -/
theorem ruleAt_comptypeSubFunc : HasRuleAt (simEnv B) "Comptype_sub" "%|-%<:%" 2
    (.ruleD "func" [ctxP, listP "t_11*" "valtype", listP "t_12*" "valtype",
        listP "t_21*" "valtype", listP "t_22*" "valtype"] "%|-%<:%"
      (.tupE [.varE "C", .caseE "FUNC%->%" (.tupE [resE "t_11", resE "t_12"]),
        .caseE "FUNC%->%" (.tupE [resE "t_21", resE "t_22"])])
      [relPrem "Resulttype_sub" "%|-%<:%" [resE "t_21", resE "t_11"],
       relPrem "Resulttype_sub" "%|-%<:%" [resE "t_12", resE "t_22"]]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
