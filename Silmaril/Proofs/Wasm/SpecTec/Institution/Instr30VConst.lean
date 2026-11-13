module

public import Silmaril.Wasm.SpecTec.Institution.Instr30V.Defs
public import Silmaril.Wasm.SpecTec.Institution.Instr30W.Thms

/-!
# Module typing of the wasm-3.0 script, ws5 constant offsets and active data

The rules of constant-expression typing and of active data, located in `simEnv B` by a kernel
`rfl` (copied from `Raw/…/Scripts/Wasm30/Original/Part3.lean`, definitions 363 to 365, 373 and
374), and fired at an offset that is one integer constant, in every typed context value:

* `dd_instrConstInt`: `Instr_const/const`, `C ⊢ CONST nt c CONST`;
* `dd_exprConst1`: `Expr_const` at one constant instruction;
* `dd_exprOk1`: `Expr_ok(C, [i], %([t]))` from `Instr_ok(C, i, [] -> [t])`;
* `dd_exprOkConstInt`: `Expr_ok_const(C, [CONST nt c], nt)`;
* `dd_datamodeActive`: `Datamode_ok/active` when `C.MEMS[x] = at lim` and the offset is `at.const c`;
* `dd_dataOkA`: `Data_ok(C, dataVA d, OK)` at every passive or constant-active segment whose
  memory is in `C.MEMS`;
* `typedV_modeV`, `typedV_dataVA`: the images are typed (`ACTIVE(x, [CONST nt c])`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV idxV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil)
open Silmaril.Wasm.SpecTec.Institution.Instr30W (okV evalExp_unitCase dataOkRule ruleAt_dataOk
  typedV_okV dd_datamodePassive findTyp_datamode findTyp_data hasTyp_unit)

variable {B : Builtins}

/-! ## The rules -/

/-- `instr*` iterated over its own domain. -/
def instrsE : Exp := .iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")])

/-- `Instr_const/const`. -/
def instrConstRule : Rule :=
  .ruleD "const" [ctxP, .expP "nt" (.varT "numtype" []), .expP "c_nt" (.varT "num_" [.expA (.varE "nt")])]
    "%|-%CONST" (.tupE [.varE "C", .caseE "CONST" (.tupE [.varE "nt", .varE "c_nt"])]) []

set_option maxRecDepth 100000 in
/-- **`Instr_const/const`**, rule 0 of `simEnv B`. -/
theorem ruleAt_instrConst : HasRuleAt (simEnv B) "Instr_const" "%|-%CONST" 0 instrConstRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Expr_const`'s rule. -/
def exprConstRule : Rule :=
  .ruleD "" [ctxP, .expP "instr*" (.iterT (.varT "instr" []) .list)] "%|-%CONST"
    (.tupE [.varE "C", instrsE])
    [.iterPr (.rulePr "Instr_const" [] "%|-%CONST" (.tupE [.varE "C", .varE "instr"]))
      (.mk .list [.mk "instr" (.varE "instr*")])]

set_option maxRecDepth 100000 in
/-- **`Expr_const`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_exprConst : HasRuleAt (simEnv B) "Expr_const" "%|-%CONST" 0 exprConstRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `t*` iterated over its own domain. -/
def tsE : Exp := .iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")])

/-- `Expr_ok`'s rule. -/
def exprOkRule : Rule :=
  .ruleD "" [ctxP, .expP "instr*" (.iterT (.varT "instr" []) .list),
      .expP "t*" (.iterT (.varT "valtype" []) .list)] "%|-%:%"
    (.tupE [.varE "C", instrsE, .caseE "%" (.tupE [tsE])])
    [.rulePr "Instrs_ok" [] "%|-%:%" (.tupE [.varE "C", instrsE,
      .caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.listE []]), .listE [], .caseE "%" (.tupE [tsE])])])]

set_option maxRecDepth 100000 in
/-- **`Expr_ok`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_exprOk : HasRuleAt (simEnv B) "Expr_ok" "%|-%:%" 0 exprOkRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Expr_ok_const`'s rule. -/
def exprOkConstRule : Rule :=
  .ruleD "" [ctxP, .expP "expr" (.varT "expr" []), .expP "t" (.varT "valtype" [])] "%|-%:%CONST"
    (.tupE [.varE "C", .varE "expr", .varE "t"])
    [.rulePr "Expr_ok" [] "%|-%:%" (.tupE [.varE "C", .varE "expr",
      .caseE "%" (.tupE [.listE [.varE "t"]])]),
     .rulePr "Expr_const" [] "%|-%CONST" (.tupE [.varE "C", .varE "expr"])]

set_option maxRecDepth 100000 in
/-- **`Expr_ok_const`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_exprOkConst : HasRuleAt (simEnv B) "Expr_ok_const" "%|-%:%CONST" 0 exprOkConstRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `C.MEMS[x.0]`. -/
def memsAtE : Exp := .idxE (.dotE (.varE "C") "MEMS") (.projE (.uncaseE (.varE "x") "%") (0 : Int))

/-- `Datamode_ok/active`. -/
def datamodeActiveRule : Rule :=
  .ruleD "active" [ctxP, .expP "x" (.varT "idx" []), .expP "expr" (.varT "expr" []),
      .expP "at" (.varT "addrtype" []), .expP "lim" (.varT "limits" [])] "%|-%:%"
    (.tupE [.varE "C", .caseE "ACTIVE" (.tupE [.varE "x", .varE "expr"]), .caseE "OK" (.tupE [])])
    [.ifPr (.cmpE .eqOp .boolT memsAtE (.caseE "%%PAGE" (.tupE [.varE "at", .varE "lim"]))),
     .rulePr "Expr_ok_const" [] "%|-%:%CONST" (.tupE [.varE "C", .varE "expr",
       .subE (.varE "at") (.varT "addrtype" []) (.varT "valtype" [])])]

set_option maxRecDepth 100000 in
/-- **`Datamode_ok/active`**, rule 1 of `simEnv B`. -/
theorem ruleAt_datamodeActive :
    HasRuleAt (simEnv B) "Datamode_ok" "%|-%:%" 1 datamodeActiveRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Typing -/

set_option maxRecDepth 100000 in
theorem findTyp_expr : (simEnv B).findTyp? "expr" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]) := rfl

/-- **A list of typed instructions is an `expr`.** -/
theorem typedV_expr {is : List Value} (h : ∀ i ∈ is, TypedV (simEnv B) (.varT "instr" []) i) :
    TypedV (simEnv B) (.varT "expr" []) (.list is) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_expr Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (typedV_list_iff.2 h VarEnv.empty ⟨rfl, rfl, rfl⟩)))

/-- An integer constant is a typed `instr`. -/
theorem typedV_intConst (t : IntType) (b : BitVec t.width) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.intConst t b)) :=
  Round5.Pos.typedV_instrToV_of _ rfl rfl fun _ hb => by simp [Instr.bodies] at hb

/-- `[at.const c]` is an `expr`. -/
theorem typedV_constExpr (t : IntType) (b : BitVec t.width) :
    TypedV (simEnv B) (.varT "expr" []) (.list (instrsToV [.intConst t b])) :=
  typedV_expr fun i hi => by
    obtain rfl := List.mem_singleton.1 hi
    exact typedV_intConst t b

/-! ## Firing -/

/-- **`Instr_const/const`** at an integer constant, in every typed context. -/
theorem dd_instrConstInt (O : ElseI) {c : Value} (hc : CtxT B c) (t : IntType)
    (b : BitVec t.width) :
    DDerivesB (simEnv B) O "Instr_const" "%|-%CONST" [] (.tuple [c, instrToV (.intConst t b)]) :=
  dderivesB_of_ruleAt ruleAt_instrConst (self_mem_conclAlts _)
    [("C", c), ("nt", IntNumeric.ntV t), ("c_nt", Silmaril.SpecTec.Equiv.bvV b)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (IntNumeric.hasTyp_numtype (valsOnly_bind _) t) (QuantsOk.cons rfl
      (IntNumeric.hasTyp_num b (Sim.evalExp_var rfl)) QuantsOk.nil)))
    (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl)
      (Sim.evalExp_var rfl))))
    (fun _ h => absurd h List.not_mem_nil)

/-- **`Expr_const`** at a list of instructions that are each `Instr_const`. -/
theorem dd_exprConst (O : ElseI) {c : Value} (hc : CtxT B c) {is : List Value}
    (hi : ∀ i ∈ is, TypedV (simEnv B) (.varT "instr" []) i)
    (hd : ∀ i ∈ is, DDerivesB (simEnv B) O "Instr_const" "%|-%CONST" [] (.tuple [c, i])) :
    DDerivesB (simEnv B) O "Expr_const" "%|-%CONST" [] (.tuple [c, .list is]) :=
  dderivesB_of_ruleAt ruleAt_exprConst (self_mem_conclAlts _) [("C", c), ("instr*", .list is)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hi _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup2 (Sim.evalExp_var rfl) (Instr30Z.evalExp_star (by decide) rfl))
    (premsB_one (Round6.AgreeOk.dpremB_iter1 rfl fun w hw =>
      .rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var (by simp [VarEnv.findVal?,
        VarEnv.bindVals, Map.binds, Map.bind, Map.find?]))
        (Sim.evalExp_var (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind])))
        (hd w hw)))

/-- **`Expr_ok(C, instr*, %(t*))`** from `Instrs_ok(C, instr*, [] -> t*)`. -/
theorem dd_exprOk (O : ElseI) {c : Value} (hc : CtxT B c) {is ts : List Value}
    (hi : ∀ i ∈ is, TypedV (simEnv B) (.varT "instr" []) i)
    (ht : ∀ t ∈ ts, TypedV (simEnv B) (.varT "valtype" []) t)
    (hd : DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, itV [] [] ts])) :
    DDerivesB (simEnv B) O "Expr_ok" "%|-%:%" []
      (.tuple [c, .list is, .case "%" (.tuple [.list ts])]) :=
  dderivesB_of_ruleAt ruleAt_exprOk (self_mem_conclAlts _)
    [("C", c), ("instr*", .list is), ("t*", .list ts)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hi _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 ht _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl) (Instr30Z.evalExp_star (by decide) rfl)
      (Instr30Z.evalExp_pctStar (by decide) rfl))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl)
      (Instr30Z.evalExp_star (by decide) rfl) (evalExp_case (evalExp_tup3 Instr30.evalExp_resNil
        evalExp_nil (Instr30Z.evalExp_pctStar (by decide) rfl)))) hd))

/-- **`Expr_ok_const(C, e, t)`** from `Expr_ok(C, e, %([t]))` and `Expr_const(C, e)`. -/
theorem dd_exprOkConst (O : ElseI) {c e t : Value} (hc : CtxT B c)
    (he : TypedV (simEnv B) (.varT "expr" []) e) (ht : TypedV (simEnv B) (.varT "valtype" []) t)
    (hok : DDerivesB (simEnv B) O "Expr_ok" "%|-%:%" [] (.tuple [c, e, .case "%" (.tuple [.list [t]])]))
    (hcst : DDerivesB (simEnv B) O "Expr_const" "%|-%CONST" [] (.tuple [c, e])) :
    DDerivesB (simEnv B) O "Expr_ok_const" "%|-%:%CONST" [] (.tuple [c, e, t]) := by
  refine dderivesB_of_ruleAt ruleAt_exprOkConst (self_mem_conclAlts _)
    [("C", c), ("expr", e), ("t", t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (he _ (valsOnly_bind _))
      (QuantsOk.cons rfl (ht _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_list1 (Sim.evalExp_var rfl))
        evalExps_nil, rfl⟩))) hok
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) hcst

/-- **`Expr_ok_const(C, [CONST nt c], nt)`**, in every typed context. -/
theorem dd_exprOkConstInt (O : ElseI) {c : Value} (hc : CtxT B c) (t : IntType)
    (b : BitVec t.width) :
    DDerivesB (simEnv B) O "Expr_ok_const" "%|-%:%CONST" []
      (.tuple [c, .list (instrsToV [.intConst t b]), tyV (.num (.int t))]) :=
  have hi : ∀ i ∈ instrsToV [.intConst t b], TypedV (simEnv B) (.varT "instr" []) i :=
    fun i hi => by
      obtain rfl := List.mem_singleton.1 hi
      exact typedV_intConst t b
  have ht : TypedV (simEnv B) (.varT "valtype" []) (tyV (.num (.int t))) :=
    Instr30.typedV_val rfl
  dd_exprOkConst O hc (typedV_constExpr t b) ht
    (dd_exprOk O hc hi (fun _ h => (List.mem_singleton.1 h) ▸ ht)
      (Instr30.dd_instrsInstr O hc (typedV_intConst t b) (fun _ h => absurd h List.not_mem_nil)
        (fun _ h => absurd h List.not_mem_nil) (fun _ h => (List.mem_singleton.1 h) ▸ ht)
        (Instr30X.dd_intConst O hc t b)))
    (dd_exprConst O hc hi fun i hi => by
      obtain rfl := List.mem_singleton.1 hi
      exact dd_instrConstInt O hc t b)

/-! ## Active data -/

/-- An address type's image is its value type's. -/
theorem toValue_addr (a : AddrType) : (Encode.toValue a : Value) = tyV (.num (.int a.intType)) := by
  cases a <;> rfl

/-- `C.MEMS[x.0]` evaluates to the `x`-th memory of `{MEMS ms, DATAS oks}`. -/
theorem evalExp_memsAt {env : Env} {ρ : VarEnv} {ms oks : List Value} {n : Nat} {u : Value}
    (hC : ρ.findVal? "C" = some (Instr30W.ctxMD ms oks)) (hx : ρ.findVal? "x" = some (idxV n))
    (hu : ms[n]? = some u) : EvalExp env ρ memsAtE u := by
  refine evalExp_idxE_iff.2 ⟨.list ms, n, evalExp_dotE_iff.2 ⟨_, Sim.evalExp_var hC, ?_⟩,
    evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (Sim.evalExp_var hx), le_refl _, rfl⟩,
    by simpa [Value.idx?] using hu⟩
  rfl

/-- The scope of `Datamode_ok/active`. -/
def activeσ (c : Value) (x : MemIdx) (mt : MemoryType) (b : BitVec mt.address.intType.width) :
    List (IL.Id × Value) :=
  [("C", c), ("x", Encode.toValue x), ("expr", .list (instrsToV [.intConst mt.address.intType b])),
   ("at", Encode.toValue mt.address), ("lim", Encode.toValue mt.limits)]

/-- **`Datamode_ok/active`** at a constant offset `at.const c`, when the `x`-th memory of
`C = {MEMS ms, DATAS oks}` is `at lim`. -/
theorem dd_datamodeActive (O : ElseI) {ms oks : List Value} (hc : CtxT B (Instr30W.ctxMD ms oks))
    (x : MemIdx) {mt : MemoryType} (hm : ms[x.toNat]? = some (Encode.toValue mt))
    (b : BitVec mt.address.intType.width) :
    DDerivesB (simEnv B) O "Datamode_ok" "%|-%:%" []
      (.tuple [Instr30W.ctxMD ms oks, modeV (.active x [.intConst mt.address.intType b]), okV]) := by
  have hρ := valsOnly_bind (activeσ (Instr30W.ctxMD ms oks) x mt b)
  refine dderivesB_of_ruleAt ruleAt_datamodeActive (self_mem_conclAlts _)
    (activeσ (Instr30W.ctxMD ms oks) x mt b)
    (QuantsOk.cons rfl (hc _ hρ) <| QuantsOk.cons rfl (Typing.typedV_idx x _ hρ) <|
      QuantsOk.cons rfl (typedV_constExpr _ b _ hρ) <|
      QuantsOk.cons rfl (Typing.typedV_addrtype _ _ hρ) <|
      QuantsOk.cons rfl (Round5.Pos.typedV_limits _ _ hρ) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl)
      (Sim.evalExp_var rfl))) (evalExp_unitCase _)) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .ifPr (Instr30X.evalExp_eqTrue (evalExp_memsAt rfl rfl hm)
      (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl))))
  · refine .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
      (evalExp_subE_iff.2 (Sim.evalExp_var rfl))) ?_
    rw [toValue_addr]
    exact dd_exprOkConstInt O hc _ b

/-- **`Data_ok(C, DATA(b*, mode), OK)`** from `Datamode_ok(C, mode, OK)`. -/
theorem dd_dataOkOf (O : ElseI) {c mv : Value} (hc : CtxT B c)
    (hmv : TypedV (simEnv B) (.varT "datamode" []) mv) (bs : ByteArray)
    (hd : DDerivesB (simEnv B) O "Datamode_ok" "%|-%:%" [] (.tuple [c, mv, okV])) :
    DDerivesB (simEnv B) O "Data_ok" "%|-%:%" []
      (.tuple [c, .case "DATA" (.tuple [.list (FwdMem.bytesV bs), mv]), okV]) := by
  have hρ := valsOnly_bind [("C", c), ("b*", .list (FwdMem.bytesV bs)), ("datamode", mv)]
  refine dderivesB_of_ruleAt ruleAt_dataOk (self_mem_conclAlts _) _
    (QuantsOk.cons rfl (hc _ hρ) <| QuantsOk.cons rfl (FwdMem.hasTyp_bytes hρ bs) <|
      QuantsOk.cons rfl (hmv _ hρ) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup2
      (Instr30Z.evalExp_star (by decide) rfl) (Sim.evalExp_var rfl))) (evalExp_unitCase _)) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  subst hpr
  exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
    (evalExp_unitCase _)) hd

set_option maxRecDepth 100000 in
theorem findTyp_memidx : (simEnv B).findTyp? "memidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

/-- **`ACTIVE(x, [at.const c])` is a `datamode`.** -/
theorem typedV_modeActive (x : MemIdx) (t : IntType) (b : BitVec t.width) :
    TypedV (simEnv B) (.varT "datamode" []) (modeV (.active x [.intConst t b])) :=
  Typing.typedV_closedCase findTyp_datamode rfl
    (Round5.Pos.hasTyp_tup2 (Typing.typedV_alias findTyp_memidx (Typing.typedV_idx x))
      (typedV_constExpr t b))

/-- `PASSIVE` is a `datamode`. -/
theorem typedV_modePassive : TypedV (simEnv B) (.varT "datamode" []) (modeV .passive) :=
  Instr30W.typedV_passive

/-- **The image of a passive or constant-active data segment is a `datamode`.** -/
theorem typedV_modeV_of {mts : List MemoryType} {d : Data} (h : DataShape mts d) :
    TypedV (simEnv B) (.varT "datamode" []) (modeV d.mode) := by
  rcases h with hp | ⟨x, mt, b, hm, -⟩
  · unfold Instr30W.Passive at hp
    split at hp
    · rename_i he
      rw [he]
      exact typedV_modePassive
    · exact hp.elim
  · rw [hm]
    exact typedV_modeActive x _ b

/-- **The image of a passive or constant-active data segment is a `data`.** -/
theorem typedV_dataVA {mts : List MemoryType} {d : Data} (h : DataShape mts d) :
    TypedV (simEnv B) (.varT "data" []) (dataVA d) :=
  Typing.typedV_closedCase findTyp_data rfl
    (Round5.Pos.hasTyp_tup2 (fun _ hρ => FwdMem.hasTyp_bytes hρ d.bytes) (typedV_modeV_of h))

/-- **`Datamode_ok` holds at the image of every passive or constant-active data segment** whose
memory is the corresponding one of `C = {MEMS mt*, DATAS oks}`. -/
theorem dd_datamodeShape (O : ElseI) {mts : List MemoryType} {oks : List Value}
    (hc : CtxT B (Instr30W.ctxMD (mts.map Encode.toValue) oks)) {d : Data} (h : DataShape mts d) :
    DDerivesB (simEnv B) O "Datamode_ok" "%|-%:%" []
      (.tuple [Instr30W.ctxMD (mts.map Encode.toValue) oks, modeV d.mode, okV]) := by
  rcases h with hp | ⟨x, mt, b, hm, hx⟩
  · unfold Instr30W.Passive at hp
    split at hp
    · rename_i he
      rw [he]
      exact dd_datamodePassive O hc
    · exact hp.elim
  · rw [hm]
    exact dd_datamodeActive O hc x (by simp [hx]) b

/-- **`Data_ok(C, dataVA d, OK)`** at every passive or constant-active data segment, in
`C = {MEMS mt*, DATAS oks}`. -/
theorem dd_dataOkA (O : ElseI) {mts : List MemoryType} {oks : List Value}
    (hc : CtxT B (Instr30W.ctxMD (mts.map Encode.toValue) oks)) {d : Data} (h : DataShape mts d) :
    DDerivesB (simEnv B) O "Data_ok" "%|-%:%" []
      (.tuple [Instr30W.ctxMD (mts.map Encode.toValue) oks, dataVA d, okV]) :=
  dd_dataOkOf O hc (typedV_modeV_of h) d.bytes (dd_datamodeShape O hc h)

/-- A passive segment's two images agree. -/
theorem dataVA_passive {d : Data} (h : Instr30W.Passive d) : dataVA d = Instr30W.dataV d := by
  unfold Instr30W.Passive at h
  unfold dataVA Instr30W.dataV
  split at h
  · rename_i he
    rw [he]
    rfl
  · exact h.elim

end Silmaril.Wasm.SpecTec.Institution.Instr30V
