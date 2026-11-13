module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30YFlat
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModFns

/-!
# Instruction typing of the wasm-3.0 script, `Instrs_ok/sub`

`Instrs_ok/sub` (rule 3) concludes `C ⊢ instr* : it'` from `C ⊢ instr* : it`, `C ⊢ it <: it'` and
`C ⊢ it' : OK`. Its middle premise is `Instrtype_sub`, whose one rule asks for `Resulttype_sub`
contravariantly on the parameters and covariantly on the results, and for
`x* = $setminus_(localidx, x_2*, x_1*)` with every `x` set in `C.LOCALS`.

* `ruleAt_instrsSub`, `ruleAt_instrtypeSub`: the two rules, located by a kernel `rfl`;
* `evalExp_setminusNil`: `$setminus_(localidx, [], [])` is `[]`, by its first clause
  (`fd_setminus`), evaluated clause by clause;
* `dd_instrtypeSub`: `Instrtype_sub` at types without initialised locals, from `Resulttype_sub`
  at both sides; `dd_instrsSub`: `Instrs_ok/sub` from its three premises;
* `resulttypeSub_numVec`: `Resulttype_sub` in any typed context from Core's `ResultSub` towards
  number and vector types (`valtypeSub_numVec` pointwise).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Y

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV instrtypeV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT listIterE)
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (resE listP varP evalExp_resE evalExp_listIterV
  dpremB_iter2)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV itE evalExp_nil findVal_bind1)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (defSig defClauses memTyp_X)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d15)

variable {B : Builtins}

/-! ## The rules -/

set_option maxRecDepth 100000 in
/-- `Instrs_ok/sub`. -/
theorem ruleAt_instrsSub : HasRuleAt (simEnv B) "Instrs_ok" "%|-%:%" 3
    (.ruleD "sub" [ctxP, listP "instr*" "instr", varP "it'" "instrtype", varP "it" "instrtype"]
      "%|-%:%" (.tupE [.varE "C", listIterE "instr", .varE "it'"])
      [.rulePr "Instrs_ok" [] "%|-%:%" (.tupE [.varE "C", listIterE "instr", .varE "it"]),
       .rulePr "Instrtype_sub" [] "%|-%<:%" (.tupE [.varE "C", .varE "it", .varE "it'"]),
       .rulePr "Instrtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "it'"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `x* = $setminus_(localidx, x_2*, x_1*)`. -/
def setminusPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (listIterE "x") (.callE "setminus_" [.typA (.varT "localidx" []),
    .expA (listIterE "x_2"), .expA (listIterE "x_1")]))

/-- `(C.LOCALS[x] = SET t)*`. -/
def setLocalsPrem : Prem :=
  .iterPr (.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "LOCALS")
    (.projE (.uncaseE (.varE "x") "%") (0 : Int))) (.caseE "%%" (.tupE [.caseE "SET" (.tupE []),
      .varE "t"])))) (.mk .list [.mk "t" (.varE "t*"), .mk "x" (.varE "x*")])

set_option maxRecDepth 100000 in
/-- `Instrtype_sub`, its only rule. -/
theorem ruleAt_instrtypeSub : HasRuleAt (simEnv B) "Instrtype_sub" "%|-%<:%" 0
    (.ruleD "" [ctxP, listP "t_11*" "valtype", listP "x_1*" "idx", listP "t_12*" "valtype",
      listP "t_21*" "valtype", listP "x_2*" "idx", listP "t_22*" "valtype", listP "x*" "idx",
      listP "t*" "valtype"] "%|-%<:%"
      (.tupE [.varE "C", itE "t_11" "x_1" "t_12", itE "t_21" "x_2" "t_22"])
      [.rulePr "Resulttype_sub" [] "%|-%<:%" (.tupE [.varE "C", resE "t_21", resE "t_11"]),
       .rulePr "Resulttype_sub" [] "%|-%<:%" (.tupE [.varE "C", resE "t_12", resE "t_22"]),
       setminusPrem, setLocalsPrem]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `$setminus_`'s clauses. -/
theorem fd_setminus : (simEnv B).findDef? "setminus_" =
    some ((defSig Original.d15).1, (defSig Original.d15).2, defClauses Original.d15) :=
  rfl

/-! ## Firing them -/

/-- The scope of `Instrtype_sub` without initialised locals. -/
def subσ (c : Value) (ps₁ rs₁ ps₂ rs₂ : List Value) : List (IL.Id × Value) :=
  [("C", c), ("t_11*", .list ps₁), ("x_1*", .list []), ("t_12*", .list rs₁), ("t_21*", .list ps₂),
    ("x_2*", .list []), ("t_22*", .list rs₂), ("x*", .list []), ("t*", .list [])]

/-- **`$setminus_(localidx, [], [])` is `[]`**: the side condition of `Instrtype_sub` holds
without initialised locals, by `$setminus_`'s first clause. -/
theorem dpremB_setminus (O : ElseI) (els : Prop) (c : Value) (ps₁ rs₁ ps₂ rs₂ : List Value) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (subσ c ps₁ rs₁ ps₂ rs₂)) setminusPrem :=
  .ifPr ⟨60, by
    simp [listIterE, evalExp, matchIterE, matchIterList, matchRounds, iterCols, iterCol, evalExps, callDef, evalArgs, evalArg, tryClauses, matchArg,
      matchExp, premsHold, VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind,
      Res.ofOption, Pure.pure, Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses,
      defSig, Original.d15, fd_setminus, evalIterE, evalDoms, domSrc, domVar, VarEnv.findVal?,
      VarEnv.bindVals, subσ, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds,
      Value.asList?, iterRows, Functor.map, Except.map, matchTypV, resolveTyp, VarEnv.findTyp?,
      VarEnv.bindTyp, memTyp_X, cmpValues]⟩

/-- A premise list holds when its head and its tail do. -/
theorem premsB_cons {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem} {prs : List Prem}
    (h : DPremB env O els ρ pr) (hs : ∀ p ∈ prs, DPremB env O els ρ p) :
    ∀ p ∈ pr :: prs, DPremB env O els ρ p := fun p hp =>
  (List.mem_cons.1 hp).elim (fun e => e ▸ h) (hs p)

/-- **`Instrtype_sub`** at types without initialised locals, from `Resulttype_sub` at both sides
(contravariant parameters, covariant results). -/
theorem dd_instrtypeSub (O : ElseI) {c : Value} (hc : CtxT B c) {ps₁ rs₁ ps₂ rs₂ : List Value}
    (hp₁ : ∀ t ∈ ps₁, TypedV (simEnv B) (.varT "valtype" []) t)
    (hr₁ : ∀ t ∈ rs₁, TypedV (simEnv B) (.varT "valtype" []) t)
    (hp₂ : ∀ t ∈ ps₂, TypedV (simEnv B) (.varT "valtype" []) t)
    (hr₂ : ∀ t ∈ rs₂, TypedV (simEnv B) (.varT "valtype" []) t)
    (h₁ : DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list ps₂]), .case "%" (.tuple [.list ps₁])]))
    (h₂ : DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list rs₁]), .case "%" (.tuple [.list rs₂])])) :
    DDerivesB (simEnv B) O "Instrtype_sub" "%|-%<:%" [] (.tuple [c, itV ps₁ [] rs₁, itV ps₂ [] rs₂]) := by
  have hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals (subσ c ps₁ rs₁ ps₂ rs₂))
      [ctxP, listP "t_11*" "valtype", listP "x_1*" "idx", listP "t_12*" "valtype",
        listP "t_21*" "valtype", listP "x_2*" "idx", listP "t_22*" "valtype", listP "x*" "idx",
        listP "t*" "valtype"] :=
    QuantsOk.cons rfl (hc _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hp₁ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (Instr30.typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hr₁ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hp₂ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (Instr30.typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hr₂ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (Instr30.typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (Instr30.typedV_nilList _ (valsOnly_bind _)) QuantsOk.nil
  have hres {x : IL.Id} {ws : List Value} (hx : x ≠ "_")
      (h : (VarEnv.empty.bindVals (subσ c ps₁ rs₁ ps₂ rs₂)).findVal? (x ++ "*") = some (.list ws)) :
      EvalExp (simEnv B) (VarEnv.empty.bindVals (subσ c ps₁ rs₁ ps₂ rs₂)) (resE x)
        (.case "%" (.tuple [.list ws])) :=
    evalExp_resE h (findVal_bind1 hx)
  have hlist {x : IL.Id} {ws : List Value} (hx : x ≠ "_")
      (h : (VarEnv.empty.bindVals (subσ c ps₁ rs₁ ps₂ rs₂)).findVal? (x ++ "*") = some (.list ws)) :
      EvalExp (simEnv B) (VarEnv.empty.bindVals (subσ c ps₁ rs₁ ps₂ rs₂)) (listIterE x) (.list ws) :=
    evalExp_listIterV h (findVal_bind1 hx)
  refine dderivesB_of_ruleAt ruleAt_instrtypeSub (self_mem_conclAlts _) (subσ c ps₁ rs₁ ps₂ rs₂) hq
    (evalExp_tup3 (Sim.evalExp_var rfl)
      (evalExp_case (evalExp_tup3 (hres (by decide) rfl) (hlist (by decide) rfl) (hres (by decide) rfl)))
      (evalExp_case (evalExp_tup3 (hres (by decide) rfl) (hlist (by decide) rfl) (hres (by decide) rfl))))
    (premsB_cons (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (Sim.evalExp_var rfl) (hres (by decide) rfl) (hres (by decide) rfl)) h₁)
    (premsB_cons (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (Sim.evalExp_var rfl) (hres (by decide) rfl) (hres (by decide) rfl)) h₂)
    (premsB_cons (dpremB_setminus O _ c ps₁ rs₁ ps₂ rs₂)
    (premsB_one (dpremB_iter2 (ps := []) rfl rfl fun _ h => absurd h List.not_mem_nil)))))

/-- The scope of `Instrs_ok/sub`. -/
def instrsSubσ (c : Value) (is : List Value) (it it' : Value) : List (IL.Id × Value) :=
  [("C", c), ("instr*", .list is), ("it'", it'), ("it", it)]

/-- **`Instrs_ok/sub`**, from its three premises. -/
theorem dd_instrsSub (O : ElseI) {c : Value} (hc : CtxT B c) {is : List Value} {it it' : Value}
    (hi : ∀ i ∈ is, TypedV (simEnv B) (.varT "instr" []) i)
    (hit : TypedV (simEnv B) (.varT "instrtype" []) it)
    (hit' : TypedV (simEnv B) (.varT "instrtype" []) it')
    (h : DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, it]))
    (hs : DDerivesB (simEnv B) O "Instrtype_sub" "%|-%<:%" [] (.tuple [c, it, it']))
    (hok : DDerivesB (simEnv B) O "Instrtype_ok" "%|-%:OK" [] (.tuple [c, it'])) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, it']) := by
  have hlist : EvalExp (simEnv B) (VarEnv.empty.bindVals (instrsSubσ c is it it')) (listIterE "instr")
      (.list is) := evalExp_listIterV rfl (findVal_bind1 (by decide))
  refine dderivesB_of_ruleAt ruleAt_instrsSub (self_mem_conclAlts _) (instrsSubσ c is it it')
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hi _ (valsOnly_bind _)) (QuantsOk.cons rfl (hit' _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hit _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) hlist (Sim.evalExp_var rfl)) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) hlist (Sim.evalExp_var rfl)) h
  · exact .rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) hs
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) hok

set_option maxRecDepth 100000 in
/-- `instrtype`'s definition. -/
theorem findTyp_instrtype : (simEnv B).findTyp? "instrtype" = some ([], [.instD [] [] (.variantT
    [.mk "%->_%%" (.tupT [.mk "resulttype" (.varT "resulttype" []),
      .mk "localidx*" (.iterT (.varT "localidx" []) .list), .mk "resulttype" (.varT "resulttype" [])])
      [] []])]) :=
  rfl

/-- An instruction type without initialised locals, with typed value types and results of
`u32` length, is a typed `instrtype`. -/
theorem typedV_itV {ps rs : List Value} (hlp : ps.length < 2 ^ 32) (hlr : rs.length < 2 ^ 32)
    (hp : ∀ t ∈ ps, TypedV (simEnv B) (.varT "valtype" []) t)
    (hr : ∀ t ∈ rs, TypedV (simEnv B) (.varT "valtype" []) t) :
    TypedV (simEnv B) (.varT "instrtype" []) (itV ps [] rs) :=
  Typing.typedV_closedCase findTyp_instrtype rfl
    (Round5.Pos.hasTyp_tup3 (Round5.Pos.typedV_resulttype hlp hp) Instr30.typedV_nilList
      (Round5.Pos.typedV_resulttype hlr hr))

/-- A pointwise relation between two lists of value types, read as a list of pairs of images. -/
theorem pairs_of_forall₂ {R : CValType → CValType → Prop} :
    ∀ {ts ts' : List CValType}, List.Forall₂ R ts ts' → ∃ ps : List (Value × Value),
      ps.map Prod.fst = ts.map tyV ∧ ps.map Prod.snd = ts'.map tyV ∧
        ∀ p ∈ ps, ∃ t t', R t t' ∧ t' ∈ ts' ∧ p = (tyV t, tyV t')
  | _, _, .nil => ⟨[], rfl, rfl, fun _ h => absurd h List.not_mem_nil⟩
  | _, _, .cons (a := t) (b := t') hr hl => by
    obtain ⟨ps, h₁, h₂, h₃⟩ := pairs_of_forall₂ hl
    refine ⟨(tyV t, tyV t') :: ps, by simp [h₁], by simp [h₂], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨t, t', hr, List.mem_cons_self .., rfl⟩
    · obtain ⟨u, u', hu, hm, rfl⟩ := h₃ p hp
      exact ⟨u, u', hu, List.mem_cons_of_mem _ hm, rfl⟩

/-- **`Resulttype_sub` towards number and vector types**, in any typed context, from Core's
`ResultSub`. -/
theorem resulttypeSub_numVec (O : ElseI) {c : Value} (hc : CtxT B c) {Δ : TypeCtx}
    {ts ts' : List CValType} (hs : ResultSub Δ ts ts') (hnv : ∀ t ∈ ts', t.IsNumOrVec) :
    DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list (ts.map tyV)]), .case "%" (.tuple [.list (ts'.map tyV)])]) := by
  obtain ⟨ps, h₁, h₂, h₃⟩ := pairs_of_forall₂ hs
  have key := Round6.AgreeOk.dd_resulttypeSub O hc (ps := ps)
    (fun p hp => by
      obtain ⟨t, t', hr, hm, rfl⟩ := h₃ p hp
      exact ⟨typedV_flat (flat_of_sub hr (hnv t' hm)), typedV_flat (flat_numVec (hnv t' hm))⟩)
    (fun p hp => by
      obtain ⟨t, t', hr, hm, rfl⟩ := h₃ p hp
      exact valtypeSub_numVec O hc hr (hnv t' hm))
  rw [h₁, h₂] at key
  exact key

end Silmaril.Wasm.SpecTec.Institution.Instr30Y
