module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WRefl
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms

/-!
# Module typing of the wasm-3.0 script, passive data segments

`Data_ok` (definition 374) and the `passive` rule of `Datamode_ok` (definition 373), located in
`simEnv B` by a kernel `rfl`, and fired at the image `dataV d = DATA(b*, PASSIVE)` of every data
segment, in every typed context value:

* `dd_datamodePassive`: `Datamode_ok(C, PASSIVE, OK)`;
* `dd_dataOk`: `Data_ok(C, DATA(b*, PASSIVE), OK)`;
* `typedV_dataV`, `typedV_okV`, `ctxT_ctxMD`: `dataV d` is a `data`, `OK` is a `datatype`, and
  `{MEMS mt*, DATAS ok*}` is a typed context value.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT ctxP)

variable {B : Builtins}

/-! ## The rules -/

/-- `Datamode_ok/passive`. -/
def datamodePassiveRule : Rule :=
  .ruleD "passive" [ctxP] "%|-%:%"
    (.tupE [.varE "C", .caseE "PASSIVE" (.tupE []), .caseE "OK" (.tupE [])]) []

set_option maxRecDepth 100000 in
/-- **`Datamode_ok/passive`**, rule 0 of `simEnv B`. -/
theorem ruleAt_datamodePassive : HasRuleAt (simEnv B) "Datamode_ok" "%|-%:%" 0 datamodePassiveRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Data_ok`'s rule (definition 374). -/
def dataOkRule : Rule :=
  .ruleD "" [ctxP, .expP "b*" (.iterT (.varT "byte" []) .list), .expP "datamode" (.varT "datamode" [])]
    "%|-%:%" (.tupE [.varE "C", .caseE "DATA" (.tupE [.iterE (.varE "b") (.mk .list [.mk "b" (.varE "b*")]),
      .varE "datamode"]), .caseE "OK" (.tupE [])])
    [.rulePr "Datamode_ok" [] "%|-%:%" (.tupE [.varE "C", .varE "datamode", .caseE "OK" (.tupE [])])]

set_option maxRecDepth 100000 in
/-- **`Data_ok`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_dataOk : HasRuleAt (simEnv B) "Data_ok" "%|-%:%" 0 dataOkRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Typing -/

set_option maxRecDepth 100000 in
theorem findTyp_datamode : (simEnv B).findTyp? "datamode" = some ([], [.instD [] [] (.variantT
    [.mk "ACTIVE" (.tupT [.mk "memidx" (.varT "memidx" []), .mk "expr" (.varT "expr" [])]) [] [],
     .mk "PASSIVE" (.tupT []) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_datatype : (simEnv B).findTyp? "datatype" = some ([], [.instD [] [] (.variantT
    [.mk "OK" (.tupT []) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_data : (simEnv B).findTyp? "data" = some ([], [.instD [] [] (.variantT
    [.mk "DATA" (.tupT [.mk "byte*" (.iterT (.varT "byte" []) .list),
      .mk "datamode" (.varT "datamode" [])]) [] []])]) := rfl

/-- The empty tuple is a `()`. -/
theorem hasTyp_unit : HasTyp (simEnv B) VarEnv.empty (.tupT []) (.tuple []) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_nil_iff.2 rfl⟩

/-- `PASSIVE` is a `datamode`. -/
theorem typedV_passive : TypedV (simEnv B) (.varT "datamode" []) (.case "PASSIVE" (.tuple [])) :=
  Typing.typedV_closedCase findTyp_datamode rfl hasTyp_unit

/-- **`OK` is a `datatype`.** -/
theorem typedV_okV : TypedV (simEnv B) (.varT "datatype" []) okV :=
  Typing.typedV_closedCase findTyp_datatype rfl hasTyp_unit

/-- **`DATA(b*, PASSIVE)` is a `data`.** -/
theorem typedV_dataV (d : Silmaril.Wasm.Data) : TypedV (simEnv B) (.varT "data" []) (dataV d) :=
  Typing.typedV_closedCase findTyp_data rfl
    (Round5.Pos.hasTyp_tup2 (fun _ hρ => FwdMem.hasTyp_bytes hρ d.bytes) typedV_passive)

/-- **`{MEMS ms, DATAS oks}` is a typed context** when its entries are memory types and `OK`s. -/
theorem ctxT_ctxMD {ms oks : List Value}
    (hm : ∀ u ∈ ms, TypedV (simEnv B) (.varT "memtype" []) u)
    (ho : ∀ u ∈ oks, TypedV (simEnv B) (.varT "datatype" []) u) : CtxT B (ctxMD ms oks) :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  Round5.Pos.typedV_struct Round6.Reading.findTyp_context <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hm) <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 ho) <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_one h0

/-! ## Firing -/

/-- `()` evaluates to the empty tuple. -/
theorem evalExp_unitCase {env : Env} {ρ : VarEnv} (a : MixopS) :
    EvalExp env ρ (.caseE a (.tupE [])) (.case a (.tuple [])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_nil, rfl⟩)

/-- **`Datamode_ok(C, PASSIVE, OK)`**, in every typed context. -/
theorem dd_datamodePassive (O : ElseI) {c : Value} (hc : CtxT B c) :
    DDerivesB (simEnv B) O "Datamode_ok" "%|-%:%" []
      (.tuple [c, .case "PASSIVE" (.tuple []), okV]) :=
  dderivesB_of_ruleAt ruleAt_datamodePassive (self_mem_conclAlts _) [("C", c)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_unitCase _) (evalExp_unitCase _))
    (fun _ h => nomatch h)

/-- **`Data_ok(C, DATA(b*, PASSIVE), OK)`** at the image of every data segment, in every typed
context. -/
theorem dd_dataOk (O : ElseI) {c : Value} (hc : CtxT B c) (d : Silmaril.Wasm.Data) :
    DDerivesB (simEnv B) O "Data_ok" "%|-%:%" [] (.tuple [c, dataV d, okV]) := by
  have hρ := valsOnly_bind [("C", c), ("b*", .list (FwdMem.bytesV d.bytes)),
    ("datamode", .case "PASSIVE" (.tuple []))]
  refine dderivesB_of_ruleAt ruleAt_dataOk (self_mem_conclAlts _) _
    (QuantsOk.cons rfl (hc _ hρ) <| QuantsOk.cons rfl (FwdMem.hasTyp_bytes hρ d.bytes) <|
      QuantsOk.cons rfl (typedV_passive _ hρ) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup2
      (Instr30Z.evalExp_star (by decide) rfl) (Sim.evalExp_var rfl))) (evalExp_unitCase _)) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  subst hpr
  exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
    (evalExp_unitCase _)) (dd_datamodePassive O hc)

end Silmaril.Wasm.SpecTec.Institution.Instr30W
