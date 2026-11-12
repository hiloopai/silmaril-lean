module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms

/-!
# Round 6: the subtyping rules, located in `simEnv B`

Each lemma locates one rule of `Heaptype_sub`, `Deftype_sub` or `Reftype_sub` (script
definition 334, the validation `rec` group) by a kernel `rfl`. `Heaptype_sub/bot` and
`Reftype_sub/null` are `ruleAt_heaptypeSubBot`, `ruleAt_reftypeSubNull`.
The rules located here and in `RulesBot.lean` are the ones the canonical derivations of `Sem`
use: here `refl`, `trans`, the four abstract axioms, `struct`/`array`/`func` and `def`; there
`none` and its three siblings, `Deftype_sub/super` and `Reftype_sub/nonnull`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

variable {B : Builtins}

/-- `C : context`. -/
def ctxP : Param := .expP "C" (.varT "context" [])

/-- A variable of sort `heaptype`. -/
def heapP (x : IL.Id) : Param := .expP x (.varT "heaptype" [])

/-- A variable of sort `deftype`. -/
def defP (x : IL.Id) : Param := .expP x (.varT "deftype" [])

/-- A nullary case, as a conclusion writes an abstract heap type. -/
def atomE (op : MixopS) : Exp := .caseE op (.tupE [])

/-- A `deftype` variable used as a heap type. -/
def defHeapE (x : IL.Id) : Exp := .subE (.varE x) (.varT "deftype" []) (.varT "heaptype" [])

/-- The premise `C ⊢ a <: b` of `Heaptype_sub`. -/
def subPrem (a b : Exp) : Prem := .rulePr "Heaptype_sub" [] "%|-%<:%" (.tupE [.varE "C", a, b])

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/refl`. -/
theorem ruleAt_refl : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 0
    (.ruleD "refl" [ctxP, heapP "heaptype"] "%|-%<:%"
      (.tupE [.varE "C", .varE "heaptype", .varE "heaptype"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/trans`. -/
theorem ruleAt_trans : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 1
    (.ruleD "trans" [ctxP, heapP "heaptype_1", heapP "heaptype_2", heapP "heaptype'"] "%|-%<:%"
      (.tupE [.varE "C", .varE "heaptype_1", .varE "heaptype_2"])
      [.rulePr "Heaptype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "heaptype'"]),
       subPrem (.varE "heaptype_1") (.varE "heaptype'"),
       subPrem (.varE "heaptype'") (.varE "heaptype_2")]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/eq-any`. -/
theorem ruleAt_eqAny : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 2
    (.ruleD "eq-any" [ctxP] "%|-%<:%" (.tupE [.varE "C", atomE "EQ", atomE "ANY"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/i31-eq`. -/
theorem ruleAt_i31Eq : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 3
    (.ruleD "i31-eq" [ctxP] "%|-%<:%" (.tupE [.varE "C", atomE "I31", atomE "EQ"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/struct-eq`. -/
theorem ruleAt_structEq : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 4
    (.ruleD "struct-eq" [ctxP] "%|-%<:%" (.tupE [.varE "C", atomE "STRUCT", atomE "EQ"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/array-eq`. -/
theorem ruleAt_arrayEq : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 5
    (.ruleD "array-eq" [ctxP] "%|-%<:%" (.tupE [.varE "C", atomE "ARRAY", atomE "EQ"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `x*` as an iteration over the list variable `x*`. -/
def listIterE (x : IL.Id) : Exp := .iterE (.varE x) (.mk .list [.mk x (.varE (x ++ "*"))])

/-- The premise `deftype ~~ ct` of `Heaptype_sub/struct`, `array`, `func`. -/
def expandPrem (ct : Exp) : Prem := .rulePr "Expand" [] "%~~%" (.tupE [.varE "deftype", ct])

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/struct`. -/
theorem ruleAt_struct : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 6
    (.ruleD "struct" [ctxP, defP "deftype", .expP "fieldtype*" (.iterT (.varT "fieldtype" []) .list)]
      "%|-%<:%" (.tupE [.varE "C", defHeapE "deftype", atomE "STRUCT"])
      [expandPrem (.caseE "STRUCT" (.caseE "%" (.tupE [listIterE "fieldtype"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/array`. -/
theorem ruleAt_array : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 7
    (.ruleD "array" [ctxP, defP "deftype", .expP "fieldtype" (.varT "fieldtype" [])]
      "%|-%<:%" (.tupE [.varE "C", defHeapE "deftype", atomE "ARRAY"])
      [expandPrem (.caseE "ARRAY" (.varE "fieldtype"))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/func`. -/
theorem ruleAt_func : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 8
    (.ruleD "func" [ctxP, defP "deftype", .expP "t_1*" (.iterT (.varT "valtype" []) .list),
        .expP "t_2*" (.iterT (.varT "valtype" []) .list)]
      "%|-%<:%" (.tupE [.varE "C", defHeapE "deftype", atomE "FUNC"])
      [expandPrem (.caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [listIterE "t_1"]),
        .caseE "%" (.tupE [listIterE "t_2"])]))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/def`. -/
theorem ruleAt_def : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 9
    (.ruleD "def" [ctxP, defP "deftype_1", defP "deftype_2"] "%|-%<:%"
      (.tupE [.varE "C", defHeapE "deftype_1", defHeapE "deftype_2"])
      [.rulePr "Deftype_sub" [] "%|-%<:%" (.tupE [.varE "C", .varE "deftype_1", .varE "deftype_2"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub
