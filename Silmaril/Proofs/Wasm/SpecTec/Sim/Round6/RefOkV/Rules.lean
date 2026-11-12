module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Ref

/-!
# Round 6: the rules of `Ref_ok`, located in `simEnv B`

Each lemma locates one of `Ref_ok`'s nine rules (script definition 627) by a kernel `rfl`;
`null` and `sub` are `ruleAt_refOkNull`, `ruleAt_refOkSub`. `refOkRules` is the
whole rule list, for inversion.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

variable {B : Builtins}

/-- `REF eps ht`, the non-null reference type of a base rule's conclusion. -/
def refNonNullE (e : Exp) : Exp := .caseE "REF" (.tupE [.optE none, e])

/-- The conclusion of a base rule of `Ref_ok`: `s ⊢ C a : REF ht`. -/
def baseConcl (op : MixopS) (a : IL.Id) (e : Exp) : Exp :=
  .tupE [.varE "s", .caseE op (.varE a), refNonNullE e]

/-- `s.F[a].TYPE = dt`, the premise of `Ref_ok/struct`, `array`, `func`. -/
def typePrem (F : AtomS) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.dotE (.idxE (.dotE (.varE "s") F) (.varE "a")) "TYPE") (.varE "dt"))

/-- The quantifiers of `Ref_ok/struct`, `array`, `func`. -/
def addrDtQs : List Param :=
  [.expP "s" (.varT "store" []), .expP "a" (.varT "addr" []), .expP "dt" (.varT "deftype" [])]

/-- `deftype` used as a heap type. -/
def dtHeapE : Exp := .subE (.varE "dt") (.varT "deftype" []) (.varT "heaptype" [])

/-- An abstract heap type, as a conclusion writes it. -/
def absE (op : MixopS) : Exp := .caseE op (.tupE [])

set_option maxRecDepth 100000 in
/-- `Ref_ok/i31`. -/
theorem ruleAt_refOkI31 : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 1
    (.ruleD "i31" [.expP "s" (.varT "store" []), .expP "i" (.varT "u31" [])] "%|-%:%"
      (baseConcl "REF.I31_NUM" "i" (absE "I31")) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Ref_ok/struct`. -/
theorem ruleAt_refOkStruct : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 2
    (.ruleD "struct" addrDtQs "%|-%:%" (baseConcl "REF.STRUCT_ADDR" "a" dtHeapE)
      [typePrem "STRUCTS"]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Ref_ok/array`. -/
theorem ruleAt_refOkArray : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 3
    (.ruleD "array" addrDtQs "%|-%:%" (baseConcl "REF.ARRAY_ADDR" "a" dtHeapE)
      [typePrem "ARRAYS"]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Ref_ok/func`. -/
theorem ruleAt_refOkFunc : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 4
    (.ruleD "func" addrDtQs "%|-%:%" (baseConcl "REF.FUNC_ADDR" "a" dtHeapE)
      [typePrem "FUNCS"]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `s.EXNS[a] = exn`, the premise of `Ref_ok/exn`. -/
def exnPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "s") "EXNS") (.varE "a")) (.varE "exn"))

set_option maxRecDepth 100000 in
/-- `Ref_ok/exn`. -/
theorem ruleAt_refOkExn : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 5
    (.ruleD "exn" [.expP "s" (.varT "store" []), .expP "a" (.varT "addr" []),
      .expP "exn" (.varT "exninst" [])] "%|-%:%" (baseConcl "REF.EXN_ADDR" "a" (absE "EXN"))
      [exnPrem]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Ref_ok/host`. -/
theorem ruleAt_refOkHost : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 6
    (.ruleD "host" [.expP "s" (.varT "store" []), .expP "a" (.varT "addr" [])] "%|-%:%"
      (baseConcl "REF.HOST_ADDR" "a" (absE "ANY")) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The premises of `Ref_ok/extern`. -/
def externPrems : List Prem :=
  [.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref", refNonNullE (absE "ANY")]),
   .ifPr (.cmpE .neOp .boolT (.varE "ref") (.caseE "REF.NULL_ADDR" (.tupE [])))]

set_option maxRecDepth 100000 in
/-- `Ref_ok/extern`. -/
theorem ruleAt_refOkExtern : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 7
    (.ruleD "extern" [.expP "s" (.varT "store" []), .expP "ref" (.varT "ref" [])] "%|-%:%"
      (baseConcl "REF.EXTERN" "ref" (absE "EXTERN")) externPrems) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
