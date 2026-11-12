module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms

/-!
# Round 6: the validation rules the counterexample uses

The rules of the pinned script's validation group (definition 334) that a derivation of
`Reftype_ok {} (REF NULL D_out)` goes through, each located in `simEnv B` by a kernel `rfl`
(copied verbatim from `Raw/…/Scripts/Wasm30/Original/Part1.lean`):

* `Heaptype_ok/typeuse`, `Typeuse_ok/rec`, `Typeuse_ok/deftype`, `Valtype_ok/ref`,
  `Storagetype_ok/val`, `Comptype_ok/struct`;
* `Subtype_ok2` (its only rule), `Rectype_ok2/empty`, `Rectype_ok2/cons`, `Deftype_ok`.

`Deftype_ok`'s first premise checks the group under `{RECS subtype^n} ⊕ C` (`compE`), the
record composition of the evaluator (`Value.comp?`), which **appends** the group's subtypes in
front of `C.RECS`. Core's `Deftype_ok` (`TyOk.defn`) uses `TypeCtx.withRecs`, which replaces
`RECS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- `Heaptype_ok/typeuse`. -/
theorem ruleAt_heaptypeOkUse : HasRuleAt (simEnv B) "Heaptype_ok" "%|-%:OK" 1
    (.ruleD "typeuse" [.expP "C" (.varT "context" []), .expP "typeuse" (.varT "typeuse" [])]
      "%|-%:OK" (.tupE [.varE "C", .subE (.varE "typeuse") (.varT "typeuse" [])
        (.varT "heaptype" [])])
      [.rulePr "Typeuse_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "typeuse"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Typeuse_ok/rec`. -/
theorem ruleAt_typeuseOkRec : HasRuleAt (simEnv B) "Typeuse_ok" "%|-%:OK" 1
    (.ruleD "rec" [.expP "C" (.varT "context" []), .expP "i" (.varT "n" []),
      .expP "st" (.varT "subtype" [])] "%|-%:OK" (.tupE [.varE "C", .caseE "REC" (.varE "i")])
      [.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i")) (.varE "st"))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Typeuse_ok/deftype`. -/
theorem ruleAt_typeuseOkDef : HasRuleAt (simEnv B) "Typeuse_ok" "%|-%:OK" 2
    (.ruleD "deftype" [.expP "C" (.varT "context" []), .expP "deftype" (.varT "deftype" [])]
      "%|-%:OK" (.tupE [.varE "C", .subE (.varE "deftype") (.varT "deftype" [])
        (.varT "typeuse" [])])
      [.rulePr "Deftype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "deftype"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Valtype_ok/ref`. -/
theorem ruleAt_valtypeOkRef : HasRuleAt (simEnv B) "Valtype_ok" "%|-%:OK" 2
    (.ruleD "ref" [.expP "C" (.varT "context" []), .expP "reftype" (.varT "reftype" [])]
      "%|-%:OK" (.tupE [.varE "C", .subE (.varE "reftype") (.varT "reftype" [])
        (.varT "valtype" [])])
      [.rulePr "Reftype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "reftype"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Storagetype_ok/val`. -/
theorem ruleAt_storagetypeOkVal : HasRuleAt (simEnv B) "Storagetype_ok" "%|-%:OK" 0
    (.ruleD "val" [.expP "C" (.varT "context" []), .expP "valtype" (.varT "valtype" [])]
      "%|-%:OK" (.tupE [.varE "C", .subE (.varE "valtype") (.varT "valtype" [])
        (.varT "storagetype" [])])
      [.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "valtype"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `fieldtype*`, as `Comptype_ok/struct` iterates it. -/
def fieldsIt : IterExp := .mk .list [.mk "fieldtype" (.varE "fieldtype*")]

set_option maxRecDepth 100000 in
/-- `Comptype_ok/struct`. -/
theorem ruleAt_comptypeOkStruct : HasRuleAt (simEnv B) "Comptype_ok" "%|-%:OK" 0
    (.ruleD "struct" [.expP "C" (.varT "context" []),
      .expP "fieldtype*" (.iterT (.varT "fieldtype" []) .list)] "%|-%:OK"
      (.tupE [.varE "C", .caseE "STRUCT" (.caseE "%" (.tupE [.iterE (.varE "fieldtype")
        fieldsIt]))])
      [.iterPr (.rulePr "Fieldtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "fieldtype"]))
        fieldsIt]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `typeuse*`, as `Subtype_ok2` iterates it. -/
def usesIt : IterExp := .mk .list [.mk "typeuse" (.varE "typeuse*")]

/-- The iteration of `Subtype_ok2`'s `$unrollht_` premise. -/
def unrollIt : IterExp := .mk .list [.mk "comptype'" (.varE "comptype'*"),
  .mk "typeuse" (.varE "typeuse*"), .mk "typeuse'*" (.varE "typeuse'**")]

/-- `comptype'*`, as `Subtype_ok2`'s `Comptype_sub` premise iterates it. -/
def supsIt : IterExp := .mk .list [.mk "comptype'" (.varE "comptype'*")]

/-- The premises of `Subtype_ok2`. -/
def subtypeOk2Prems : List Prem :=
  [.ifPr (.cmpE .leOp (.numT .natT) (.lenE (.iterE (.varE "typeuse") usesIt))
      (.numE (.natN 1))),
   .iterPr (.rulePr "Typeuse_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "typeuse"])) usesIt,
   .iterPr (.ifPr (.callE "before" [.expA (.varE "typeuse"), .expA (.varE "i")])) usesIt,
   .iterPr (.ifPr (.cmpE .eqOp .boolT (.callE "unrollht_" [.expA (.varE "C"),
      .expA (.subE (.varE "typeuse") (.varT "typeuse" []) (.varT "heaptype" []))])
      (.caseE "SUB" (.tupE [.optE none, .iterE (.varE "typeuse'")
        (.mk .list [.mk "typeuse'" (.varE "typeuse'*")]), .varE "comptype'"])))) unrollIt,
   .rulePr "Comptype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "comptype"]),
   .iterPr (.rulePr "Comptype_sub" [] "%|-%<:%" (.tupE [.varE "C", .varE "comptype",
      .varE "comptype'"])) supsIt]

set_option maxRecDepth 100000 in
/-- `Subtype_ok2`, its only rule. -/
theorem ruleAt_subtypeOk2 : HasRuleAt (simEnv B) "Subtype_ok2" "%|-%:%" 0
    (.ruleD "" [.expP "C" (.varT "context" []),
      .expP "typeuse*" (.iterT (.varT "typeuse" []) .list),
      .expP "comptype" (.varT "comptype" []), .expP "i" (.numT .natT),
      .expP "comptype'*" (.iterT (.varT "comptype" []) .list),
      .expP "typeuse'**" (.iterT (.iterT (.varT "typeuse" []) .list) .list)] "%|-%:%"
      Reading.subtypeOk2Concl subtypeOk2Prems) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Rectype_ok2/empty`. -/
theorem ruleAt_rectypeOk2Empty : HasRuleAt (simEnv B) "Rectype_ok2" "%|-%:%" 0
    (.ruleD "empty" [.expP "C" (.varT "context" []), .expP "i" (.numT .natT)] "%|-%:%"
      (.tupE [.varE "C", .caseE "REC" (.caseE "%" (.tupE [.listE []])),
        .caseE "OK" (.varE "i")]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `subtype*`, as `Rectype_ok2/cons` iterates it. -/
def subsIt : IterExp := .mk .list [.mk "subtype" (.varE "subtype*")]

set_option maxRecDepth 100000 in
/-- `Rectype_ok2/cons`. -/
theorem ruleAt_rectypeOk2Cons : HasRuleAt (simEnv B) "Rectype_ok2" "%|-%:%" 1
    (.ruleD "cons" [.expP "C" (.varT "context" []), .expP "subtype_1" (.varT "subtype" []),
      .expP "subtype*" (.iterT (.varT "subtype" []) .list), .expP "i" (.numT .natT)] "%|-%:%"
      (.tupE [.varE "C", .caseE "REC" (.caseE "%" (.tupE [.catE (.listE [.varE "subtype_1"])
        (.iterE (.varE "subtype") subsIt)])), .caseE "OK" (.varE "i")])
      [.rulePr "Subtype_ok2" [] "%|-%:%" (.tupE [.varE "C", .varE "subtype_1",
        .caseE "OK" (.varE "i")]),
       .rulePr "Rectype_ok2" [] "%|-%:%" (.tupE [.varE "C", .caseE "REC" (.caseE "%"
        (.tupE [.iterE (.varE "subtype") subsIt])), .caseE "OK" (.binE .addOp (.numT .natT)
          (.varE "i") (.numE (.natN 1)))])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `subtype^n`, as `Deftype_ok` iterates it. -/
def subsNIt : IterExp := .mk (.listN (.varE "n") none) [.mk "subtype" (.varE "subtype*")]

/-- `{RECS subtype^n} ⊕ C`, the context `Deftype_ok` checks its group in. -/
def recsCtxE : Exp :=
  .compE (.strE [.mk "TYPES" (.listE []), .mk "TAGS" (.listE []), .mk "GLOBALS" (.listE []),
    .mk "MEMS" (.listE []), .mk "TABLES" (.listE []), .mk "FUNCS" (.listE []),
    .mk "DATAS" (.listE []), .mk "ELEMS" (.listE []), .mk "LOCALS" (.listE []),
    .mk "LABELS" (.listE []), .mk "RETURN" (.optE none), .mk "REFS" (.listE []),
    .mk "RECS" (.iterE (.varE "subtype") subsNIt)]) (.varE "C")

set_option maxRecDepth 100000 in
/-- `Deftype_ok`, its only rule. -/
theorem ruleAt_deftypeOk : HasRuleAt (simEnv B) "Deftype_ok" "%|-%:OK" 0
    (.ruleD "" [.expP "C" (.varT "context" []), .expP "rectype" (.varT "rectype" []),
      .expP "i" (.varT "n" []), .expP "n" (.varT "n" []),
      .expP "subtype*" (.iterT (.varT "subtype" []) .list)] "%|-%:OK"
      (.tupE [.varE "C", .caseE "_DEF" (.tupE [.varE "rectype", .varE "i"])])
      [.rulePr "Rectype_ok2" [] "%|-%:%" (.tupE [recsCtxE, .varE "rectype",
        .caseE "OK" (.numE (.natN 0))]),
       .ifPr (.cmpE .eqOp .boolT (.varE "rectype") (.caseE "REC" (.caseE "%"
        (.tupE [.iterE (.varE "subtype") subsNIt])))),
       .ifPr (.cmpE .ltOp (.numT .natT) (.varE "i") (.varE "n"))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB
