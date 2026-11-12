module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Script
public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 6: the validation rules with an optional atom, under `DDerivesB`

The four conclusions round 5 found unreadable now have both alternatives:

* `conclAlts_reftypeOk`: `REF NULL? heaptype` reads as `REF heaptype` or `REF NULL heaptype`;
  `dderivesB_reftypeOk`: **`Reftype_ok` fires at both nullabilities** from `Heaptype_ok`.
* `conclAlts_reftypeSubNull`, `dderivesB_reftypeSub_null`: `Reftype_sub/null` fires at both
  nullabilities of its left-hand side.
* `conclAlts_fieldtypeOk`, `dderivesB_fieldtypeOk`: `Fieldtype_ok` (`MUT?`) fires at both
  mutabilities from `Storagetype_ok`.
* `conclAlts_subtypeOk2`: `Subtype_ok2`'s conclusion (`FINAL?`) has the `none` and the `some`
  alternative (its premises are not discharged here).

and the round-5 counterexample to `RefOkB` is repaired: `dderivesB_refOk_nullAny`, SpecTec now
types `null` at `REF NULL ANY` through `Ref_ok/sub`, like Core (`Round5.RefOk.refOk_nullAny`),
on every typed store, under every reading of `otherwise`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV nullV mutV absV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Validation

variable {B : Builtins}

/-! ## Optional atoms -/

/-- `NULL?`, `MUT?`, `FINAL?`: an optional nullary atom, as an alternative. -/
def atomOptE (op : MixopS) (b : Bool) : Exp :=
  if b then .optE (some (.caseE op (.tupE []))) else .optE none

/-- The value of an optional nullary atom. -/
def atomOptV (op : MixopS) (b : Bool) : Value :=
  .opt (if b then some (.case op (.tuple [])) else none)

/-- An optional nullary atom evaluates to its value. -/
theorem evalExp_atomOptE {env : Env} {ρ : VarEnv} (op : MixopS) (b : Bool) :
    EvalExp env ρ (atomOptE op b) (atomOptV op b) := by
  cases b
  · exact evalExp_optE_none_iff.2 rfl
  · exact evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩),
      rfl⟩

/-- `null?` is an optional `NULL`. -/
theorem nullV_eq (b : Bool) : nullV b = atomOptV "NULL" b := rfl

/-- `mut?` is an optional `MUT`. -/
theorem mutV_eq (m : Mutability) : mutV m = atomOptV "MUT" (m == Mutability.var) := by
  cases m <;> rfl

/-! ## The four conclusions -/

/-- `Reftype_ok`'s conclusion, `(C, REF NULL? heaptype)`. -/
def reftypeOkConcl : Exp :=
  .tupE [.varE "C", .caseE "REF" (.tupE [.iterE (.caseE "NULL" (.tupE [])) (.mk .opt []),
    .varE "heaptype"])]

/-- **`REF NULL? heaptype` reads as `REF heaptype` or `REF NULL heaptype`.** -/
theorem conclAlts_reftypeOk (b : Bool) :
    .tupE [.varE "C", .caseE "REF" (.tupE [atomOptE "NULL" b, .varE "heaptype"])] ∈
      conclAlts reftypeOkConcl := by
  cases b <;> simp [conclAlts, reftypeOkConcl, hasOptNil, hasOptNilL, optAlts, optAltsL, prod2,
    atomOptE]

/-- `Reftype_sub/null`'s conclusion, `(C, REF NULL? ht_1, REF NULL ht_2)`. -/
def reftypeSubNullConcl : Exp :=
  .tupE [.varE "C", .caseE "REF" (.tupE [.iterE (.caseE "NULL" (.tupE [])) (.mk .opt []),
    .varE "ht_1"]), .caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .varE "ht_2"])]

/-- **`Reftype_sub/null` reads at both nullabilities of its left-hand side.** -/
theorem conclAlts_reftypeSubNull (b : Bool) :
    .tupE [.varE "C", .caseE "REF" (.tupE [atomOptE "NULL" b, .varE "ht_1"]),
      .caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .varE "ht_2"])] ∈
      conclAlts reftypeSubNullConcl := by
  cases b <;> simp [conclAlts, reftypeSubNullConcl, hasOptNil, hasOptNilL, hasOptNilO, optAlts,
    optAltsL, optAltsO, prod2, atomOptE]

/-- `Fieldtype_ok`'s conclusion, `(C, MUT? storagetype)`. -/
def fieldtypeOkConcl : Exp :=
  .tupE [.varE "C", .caseE "%%" (.tupE [.iterE (.caseE "MUT" (.tupE [])) (.mk .opt []),
    .varE "storagetype"])]

/-- **`MUT? storagetype` reads at both mutabilities.** -/
theorem conclAlts_fieldtypeOk (b : Bool) :
    .tupE [.varE "C", .caseE "%%" (.tupE [atomOptE "MUT" b, .varE "storagetype"])] ∈
      conclAlts fieldtypeOkConcl := by
  cases b <;> simp [conclAlts, fieldtypeOkConcl, hasOptNil, hasOptNilL, optAlts, optAltsL, prod2,
    atomOptE]

/-- `Subtype_ok2`'s conclusion, `(C, SUB FINAL? typeuse* comptype, OK i)`. -/
def subtypeOk2Concl : Exp :=
  .tupE [.varE "C", .caseE "SUB" (.tupE [.iterE (.caseE "FINAL" (.tupE [])) (.mk .opt []),
    .iterE (.varE "typeuse") (.mk .list [.mk "typeuse" (.varE "typeuse*")]), .varE "comptype"]),
    .caseE "OK" (.varE "i")]

/-- **`SUB FINAL? …` reads at both finalities.** -/
theorem conclAlts_subtypeOk2 (b : Bool) :
    .tupE [.varE "C", .caseE "SUB" (.tupE [atomOptE "FINAL" b,
      .iterE (.varE "typeuse") (.mk .list [.mk "typeuse" (.varE "typeuse*")]), .varE "comptype"]),
      .caseE "OK" (.varE "i")] ∈ conclAlts subtypeOk2Concl := by
  cases b <;> simp [conclAlts, subtypeOk2Concl, hasOptNil, hasOptNilL, optAlts, optAltsL, prod2,
    atomOptE]

/-! ## The rules, in `simEnv B` -/

set_option maxRecDepth 100000 in
/-- `Reftype_ok`'s only rule. -/
theorem ruleAt_reftypeOk : HasRuleAt (simEnv B) "Reftype_ok" "%|-%:OK" 0
    (.ruleD "" [.expP "C" (.varT "context" []), .expP "heaptype" (.varT "heaptype" [])] "%|-%:OK"
      reftypeOkConcl [.rulePr "Heaptype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "heaptype"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_ok/abs`. -/
theorem ruleAt_heaptypeOkAbs : HasRuleAt (simEnv B) "Heaptype_ok" "%|-%:OK" 0
    (.ruleD "abs" [.expP "C" (.varT "context" []), .expP "absheaptype" (.varT "absheaptype" [])]
      "%|-%:OK" (.tupE [.varE "C", .subE (.varE "absheaptype") (.varT "absheaptype" [])
        (.varT "heaptype" [])]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Reftype_sub/null`. -/
theorem ruleAt_reftypeSubNull : HasRuleAt (simEnv B) "Reftype_sub" "%|-%<:%" 1
    (.ruleD "null" [.expP "C" (.varT "context" []), .expP "ht_1" (.varT "heaptype" []),
      .expP "ht_2" (.varT "heaptype" [])] "%|-%<:%" reftypeSubNullConcl
      [.rulePr "Heaptype_sub" [] "%|-%<:%" (.tupE [.varE "C", .varE "ht_1", .varE "ht_2"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Heaptype_sub/bot`. -/
theorem ruleAt_heaptypeSubBot : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" 20
    (.ruleD "bot" [.expP "C" (.varT "context" []), .expP "heaptype" (.varT "heaptype" [])]
      "%|-%<:%" (.tupE [.varE "C", .caseE "BOT" (.tupE []), .varE "heaptype"]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Fieldtype_ok`'s only rule. -/
theorem ruleAt_fieldtypeOk : HasRuleAt (simEnv B) "Fieldtype_ok" "%|-%:OK" 0
    (.ruleD "" [.expP "C" (.varT "context" []), .expP "storagetype" (.varT "storagetype" [])]
      "%|-%:OK" fieldtypeOkConcl
      [.rulePr "Storagetype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "storagetype"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The empty context `{}`, as the cast rules write it. -/
def ctx0E : Exp :=
  .strE [.mk "TYPES" (.listE []), .mk "TAGS" (.listE []), .mk "GLOBALS" (.listE []),
    .mk "MEMS" (.listE []), .mk "TABLES" (.listE []), .mk "FUNCS" (.listE []),
    .mk "DATAS" (.listE []), .mk "ELEMS" (.listE []), .mk "LOCALS" (.listE []),
    .mk "LABELS" (.listE []), .mk "RETURN" (.optE none), .mk "REFS" (.listE []),
    .mk "RECS" (.listE [])]

/-- The value of `{}`. -/
def ctx0V : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list []), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list [])]

set_option maxRecDepth 100000 in
/-- `Ref_ok/null`. -/
theorem ruleAt_refOkNull : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 0
    (.ruleD "null" [.expP "s" (.varT "store" [])] "%|-%:%" (.tupE [.varE "s",
      .caseE "REF.NULL_ADDR" (.tupE []), .caseE "REF" (.tupE [.optE (some (.caseE "NULL"
        (.tupE []))), .caseE "BOT" (.tupE [])])]) []) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Ref_ok/sub`. -/
theorem ruleAt_refOkSub : HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" 8
    (.ruleD "sub" [.expP "s" (.varT "store" []), .expP "ref" (.varT "ref" []),
      .expP "rt" (.varT "reftype" []), .expP "rt'" (.varT "reftype" [])] "%|-%:%"
      (.tupE [.varE "s", .varE "ref", .varE "rt"])
      [.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref", .varE "rt'"]),
       .rulePr "Reftype_ok" [] "%|-%:OK" (.tupE [ctx0E, .varE "rt"]),
       .rulePr "Reftype_sub" [] "%|-%<:%" (.tupE [ctx0E, .varE "rt'", .varE "rt"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Typing and evaluating `{}` -/

set_option maxRecDepth 100000 in
/-- The IL type `context`. -/
theorem findTyp_context : (simEnv B).findTyp? "context" = some ([], [.instD [] [] (.structT
    [.mk "TYPES" (.iterT (.varT "deftype" []) .list) [] [],
     .mk "TAGS" (.iterT (.varT "tagtype" []) .list) [] [],
     .mk "GLOBALS" (.iterT (.varT "globaltype" []) .list) [] [],
     .mk "MEMS" (.iterT (.varT "memtype" []) .list) [] [],
     .mk "TABLES" (.iterT (.varT "tabletype" []) .list) [] [],
     .mk "FUNCS" (.iterT (.varT "deftype" []) .list) [] [],
     .mk "DATAS" (.iterT (.varT "datatype" []) .list) [] [],
     .mk "ELEMS" (.iterT (.varT "elemtype" []) .list) [] [],
     .mk "LOCALS" (.iterT (.varT "localtype" []) .list) [] [],
     .mk "LABELS" (.iterT (.varT "resulttype" []) .list) [] [],
     .mk "RETURN" (.iterT (.varT "resulttype" []) .opt) [] [],
     .mk "REFS" (.iterT (.varT "funcidx" []) .list) [] [],
     .mk "RECS" (.iterT (.varT "subtype" []) .list) [] []])]) := rfl

/-- **`{}` is a typed `context`.** -/
theorem typedV_ctx0 : TypedV (simEnv B) (.varT "context" []) ctx0V :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  Round5.Pos.typedV_struct findTyp_context <|
    Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <| Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <|
    Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <| Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <|
    Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <| Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <|
    Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <| Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <|
    Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <| Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of Round5.RefOk.typedV_listNil <|
    Round5.Pos.hasTypFields_one Round5.RefOk.typedV_listNil

/-- **`{}` evaluates to `ctx0V`.** -/
theorem evalExp_ctx0 {env : Env} {ρ : VarEnv} : EvalExp env ρ ctx0E ctx0V :=
  ⟨6, by simp [ctx0E, ctx0V, evalExp, evalExpFields, evalExps]⟩

/-! ## Typing the abstract heap types -/

set_option maxRecDepth 100000 in
/-- The IL type `absheaptype`. -/
theorem findTyp_absheaptype : (simEnv B).findTyp? "absheaptype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d92 0))]) := rfl

/-- **Every abstract heap type is an `absheaptype`.** -/
theorem typedV_absheaptype (a : AbsHeapType) :
    TypedV (simEnv B) (.varT "absheaptype" []) (absV a) := by
  cases a <;> exact Typing.typedV_closedCase findTyp_absheaptype rfl hasTyp_tupT_nil

/-- A bounded heap type is a `heaptype`. -/
theorem typedV_heaptype {h : Ty .heap} (hb : Round4.tyBnd h = true) :
    TypedV (simEnv B) (.varT "heaptype" []) (tyV h) := Round5.Pos.tyT_tyV h hb

/-- A bounded reference type is a `reftype`. -/
theorem typedV_reftype {rt : CRefType} (hb : Round4.tyBnd rt = true) :
    TypedV (simEnv B) (.varT "reftype" []) (tyV rt) := (Round5.Pos.tyT_tyV rt hb).1

/-! ## Derivations under the new reading -/

/-- The scope of an assignment binds term variables only. -/
theorem valsOnly_bind (σ : List (IL.Id × Value)) : ValsOnly (VarEnv.empty.bindVals σ) :=
  ⟨rfl, rfl, rfl⟩

/-- One premise, under the new reading. -/
theorem premsB_one {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    (h : DPremB env O els ρ pr) : ∀ p ∈ [pr], DPremB env O els ρ p := by
  intro p hp
  rw [List.mem_singleton.1 hp]
  exact h

/-- No premises, under the new reading. -/
theorem premsB_nil {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} :
    ∀ p ∈ ([] : List Prem), DPremB env O els ρ p := fun _ h => absurd h List.not_mem_nil

/-- **`Heaptype_ok/abs`**: every abstract heap type is valid in a typed context. -/
theorem dderivesB_heaptypeOk_abs (O : ElseI) {c : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c) (a : AbsHeapType) :
    DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, absV a]) :=
  dderivesB_of_ruleAt ruleAt_heaptypeOkAbs (self_mem_conclAlts _)
    [("C", c), ("absheaptype", absV a)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_absheaptype a _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl))) premsB_nil

/-- **`Reftype_ok` fires at both nullabilities**: from `Heaptype_ok`, in a typed context, at a
typed heap type. -/
theorem dderivesB_reftypeOk (O : ElseI) {c h : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hh : TypedV (simEnv B) (.varT "heaptype" []) h) (n : Bool)
    (hd : DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, h])) :
    DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [c, .case "REF" (.tuple [nullV n, h])]) :=
  dderivesB_of_ruleAt ruleAt_reftypeOk (conclAlts_reftypeOk n) [("C", c), ("heaptype", h)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hh _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_tup2 (evalExp_atomOptE "NULL" n)
      (evalExp_var rfl))))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Heaptype_sub/bot`**: `BOT` is below every typed heap type. -/
theorem dderivesB_heaptypeSub_bot (O : ElseI) {c h : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hh : TypedV (simEnv B) (.varT "heaptype" []) h) :
    DDerivesB (simEnv B) O "Heaptype_sub" "%|-%<:%" [] (.tuple [c, .case "BOT" (.tuple []), h]) :=
  dderivesB_of_ruleAt ruleAt_heaptypeSubBot (self_mem_conclAlts _) [("C", c), ("heaptype", h)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hh _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_var rfl)) premsB_nil

/-- **`Reftype_sub/null` fires at both nullabilities of its left-hand side**, from
`Heaptype_sub`. -/
theorem dderivesB_reftypeSub_null (O : ElseI) {c h₁ h₂ : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hh₁ : TypedV (simEnv B) (.varT "heaptype" []) h₁)
    (hh₂ : TypedV (simEnv B) (.varT "heaptype" []) h₂) (n : Bool)
    (hd : DDerivesB (simEnv B) O "Heaptype_sub" "%|-%<:%" [] (.tuple [c, h₁, h₂])) :
    DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" []
      (.tuple [c, .case "REF" (.tuple [nullV n, h₁]), .case "REF" (.tuple [nullV true, h₂])]) :=
  dderivesB_of_ruleAt ruleAt_reftypeSubNull (conclAlts_reftypeSubNull n)
    [("C", c), ("ht_1", h₁), ("ht_2", h₂)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hh₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hh₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl)
      (evalExp_case (evalExp_tup2 (evalExp_atomOptE "NULL" n) (evalExp_var rfl)))
      (evalExp_case (evalExp_tup2 (evalExp_atomOptE "NULL" true) (evalExp_var rfl))))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Fieldtype_ok` fires at both mutabilities**, from `Storagetype_ok`. -/
theorem dderivesB_fieldtypeOk (O : ElseI) {c st : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hs : TypedV (simEnv B) (.varT "storagetype" []) st) (m : Mutability)
    (hd : DDerivesB (simEnv B) O "Storagetype_ok" "%|-%:OK" [] (.tuple [c, st])) :
    DDerivesB (simEnv B) O "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, .case "%%" (.tuple [mutV m, st])]) :=
  by
  rw [mutV_eq m]
  exact dderivesB_of_ruleAt ruleAt_fieldtypeOk (conclAlts_fieldtypeOk (m == Mutability.var))
    [("C", c), ("storagetype", st)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hs _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_tup2
      (evalExp_atomOptE "MUT" (m == Mutability.var)) (evalExp_var rfl))))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd))

/-! ## The round-5 counterexample is repaired -/

section Null

variable {H : Type}
open Silmaril.Wasm.Execution.Core

/-- `Ref_ok/null`, under the new reading. -/
theorem dderivesB_refOk_null (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue .null,
      tyV (Ty.ref true .bot : CRefType)]) :=
  dderivesB_of_ruleAt ruleAt_refOkNull (self_mem_conclAlts _) [("s", sv)]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      Round5.RefOk.evalExp_refNullBot) premsB_nil

/-- **SpecTec now types `null` at `REF NULL ANY`**, through `Ref_ok/sub`, on every typed store
and under every reading of `otherwise`: the round-5 counterexample to `RefOkB`
(`Round5.RefOk.not_refOkAt_nullAny`) is none under `DDerivesB`. -/
theorem dderivesB_refOk_nullAny (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue .null,
      tyV Round5.RefOk.nullAny]) :=
  have hb : TypedV (simEnv B) (.varT "reftype" []) (tyV (Ty.ref true .bot : CRefType)) :=
    typedV_reftype rfl
  have hok : DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [ctx0V, tyV Round5.RefOk.nullAny]) :=
    dderivesB_reftypeOk O typedV_ctx0 (typedV_heaptype rfl) true
      (dderivesB_heaptypeOk_abs O typedV_ctx0 .any)
  have hsub : DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" []
      (.tuple [ctx0V, tyV (Ty.ref true .bot : CRefType), tyV Round5.RefOk.nullAny]) :=
    dderivesB_reftypeSub_null O typedV_ctx0 (typedV_heaptype rfl) (typedV_heaptype rfl) true
      (dderivesB_heaptypeSub_bot O typedV_ctx0 (typedV_heaptype rfl))
  dderivesB_of_ruleAt ruleAt_refOkSub (self_mem_conclAlts _)
    [("s", sv), ("ref", refToValue .null), ("rt", tyV Round5.RefOk.nullAny),
      ("rt'", tyV (Ty.ref true .bot : CRefType))]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_ref .null _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_reftype rfl _ (valsOnly_bind _)) (QuantsOk.cons rfl (hb _ (valsOnly_bind _))
          QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
    (fun pr hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl
      · exact .rulePr (evalArgs_nil _ _)
          (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
          (dderivesB_refOk_null O hs)
      · exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 evalExp_ctx0 (evalExp_var rfl)) hok
      · exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 evalExp_ctx0 (evalExp_var rfl) (evalExp_var rfl))
          hsub)

/-- **The counterexample, both sides**: on every store with a typed image, SpecTec's `Ref_ok`
under the new reading and Core's `RefOk` both type `null` at `REF NULL ANY`. -/
theorem refOkAtB_nullAny_null (hn : H → String) (s : Store H)
    (hs : TypedV (simEnv B) storeT (storeV hn s)) (O : ElseI) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
        (.tuple [storeV hn s, refToValue .null, CT.elemType Round5.RefOk.nullAny]) ∧
      RefOk s .null Round5.RefOk.nullAny :=
  ⟨dderivesB_refOk_nullAny O hs, Round5.RefOk.refOk_nullAny s⟩

end Null

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
