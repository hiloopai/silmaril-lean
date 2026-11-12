module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30YVar

/-!
# Instruction typing of the wasm-3.0 script, flat types, `select`, and any context

Round 6's canonical validity derivations (`AgreeOk.okD_of`) are stated at the contexts
`ctxOf Δ`, which carry only `RECS`, so `Instr30` could fire `Instr_ok/drop` and `unreachable`
only in `{}`. For the **flat** value types (numbers, vectors, `BOT` and references to abstract
heap types: `Flat`) the derivations of `Valtype_ok` and `Valtype_sub` use no field of the context
(`Numtype_ok`, `Vectype_ok`, `Heaptype_ok/abs`, `Valtype_ok/bot`, …), so they hold in every typed
context value:

* `valtypeOk_flat`, `resulttypeOk_flat`, `instrtypeOk_flat`: `Valtype_ok`, `Resulttype_ok`,
  `Instrtype_ok` at flat types, in any typed context;
* `valtypeSub_numVec`: `Valtype_sub` from a flat subtype of a number or vector type;
* `Instr_ok/select-expl` (rule 3) and `select-impl` (rule 4), located by a kernel `rfl` and fired by
  `dd_selectExpl`, `dd_selectImpl`;
* `parametric_preserves`: every Core typing of `nop`, `unreachable`, `drop` and `select` in any
  Core context, at flat types (and, for `select t`, at a source type without type indices,
  `SrcFlat`), is an `Instr_ok` fact in any typed context value. For `select` without annotation
  the types are flat by Core's own premises (`sub_num_inv`, `sub_vec_inv`).
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
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (dd_valtypeOkNum dd_valtypeOkVec dd_valtypeOkBot
  dd_subsumeSub dd_leafSub ruleAt_valtypeSubNum ruleAt_valtypeSubVec ruleAt_numtypeSub
  ruleAt_vectypeSub typedV_numtypeV typedV_vectypeV dd_valtypeSubBot)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil evalExp_resNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (itLXE)

variable {B : Builtins}

/-! ## Flat types -/

/-- Flat types are bounded. -/
theorem tyBnd_flat {t : CValType} (h : Flat t = true) : Round4.tyBnd t = true := by
  match t, h with
  | .num t, _ => rcases t with t | t <;> cases t <;> rfl
  | .vec t, _ => cases t; rfl
  | .botv, _ => rfl
  | .refv (.ref n (.abs a)), _ => cases n <;> cases a <;> rfl

/-- Flat types have typed images. -/
theorem typedV_flat {t : CValType} (h : Flat t = true) :
    TypedV (simEnv B) (.varT "valtype" []) (tyV t) := Instr30.typedV_val (tyBnd_flat h)

/-- **`Valtype_ok` at a flat type**, in any typed context. -/
theorem valtypeOk_flat (O : ElseI) {c : Value} (hc : CtxT B c) {t : CValType} (h : Flat t = true) :
    DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, tyV t]) :=
  match t, h with
  | .num t, _ => dd_valtypeOkNum O hc t
  | .vec t, _ => dd_valtypeOkVec O hc t
  | .botv, _ => dd_valtypeOkBot O hc
  | .refv (.ref n (.abs a)), _ =>
    Round6.RefOkB.dderivesB_valtypeOkRef O hc (Round6.Reading.typedV_reftype (by cases n <;> cases a <;> rfl))
      (Round6.Reading.dderivesB_reftypeOk O hc
        (Round6.Reading.typedV_heaptype (by cases a <;> rfl)) n
        (Round6.Reading.dderivesB_heaptypeOk_abs O hc a))

/-- **`Resulttype_ok` at flat types**, in any typed context. -/
theorem resulttypeOk_flat (O : ElseI) {c : Value} (hc : CtxT B c) {ts : List CValType}
    (h : ∀ t ∈ ts, Flat t = true) :
    DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" [] (.tuple [c, .case "%" (.tuple [.list (ts.map tyV)])]) :=
  Round6.AgreeOk.dd_resulttypeOk O hc
    (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact typedV_flat (h t ht))
    fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact valtypeOk_flat O hc (h t ht)

/-- **`Instrtype_ok` at flat types without initialised locals**, in any typed context. -/
theorem instrtypeOk_flat (O : ElseI) {c : Value} (hc : CtxT B c) {ps rs : List CValType}
    (hp : ∀ t ∈ ps, Flat t = true) (hr : ∀ t ∈ rs, Flat t = true) :
    DDerivesB (simEnv B) O "Instrtype_ok" "%|-%:OK" [] (.tuple [c, instrtypeV (.plain ps rs)]) :=
  Instr30.dd_instrtypeOk O hc
    (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact typedV_flat (hp t ht))
    (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact typedV_flat (hr t ht))
    (resulttypeOk_flat O hc hp) (resulttypeOk_flat O hc hr)

/-- The image of a number type. -/
theorem tyV_num (t : NumType) : tyV (.num t) = Silmaril.SpecTec.Equiv.Validation.numtypeV t := rfl

/-- The image of a vector type. -/
theorem tyV_vec (t : VecType) : tyV (.vec t) = Silmaril.SpecTec.Equiv.Validation.vectypeV t := rfl

/-- Core's subtypes of a number type are itself and `BOT`. -/
theorem sub_num_inv {Δ : TypeCtx} {a : CValType} {n : NumType} (h : Sub Δ a (.num n)) :
    a = .num n ∨ a = .botv := by
  cases h <;> simp

/-- Core's subtypes of a vector type are itself and `BOT`. -/
theorem sub_vec_inv {Δ : TypeCtx} {a : CValType} {v : VecType} (h : Sub Δ a (.vec v)) :
    a = .vec v ∨ a = .botv := by
  cases h <;> simp

/-- **`Valtype_sub` from a subtype of a number or vector type**, in any typed context. Core's
subtypes of `t'` are `t'` and `BOT` (`sub_num_inv`, `sub_vec_inv`). -/
theorem valtypeSub_numVec (O : ElseI) {c : Value} (hc : CtxT B c) {Δ : TypeCtx} {t t' : CValType}
    (hs : Sub Δ t t') (hnv : t'.IsNumOrVec) :
    DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, tyV t, tyV t']) := by
  match t', hnv with
  | .num n, _ =>
    rcases sub_num_inv hs with rfl | rfl
    · exact dd_subsumeSub O hc ruleAt_valtypeSubNum (typedV_numtypeV n) (typedV_numtypeV n)
        (dd_leafSub O hc ruleAt_numtypeSub (typedV_numtypeV n))
    · exact dd_valtypeSubBot O hc (typedV_flat (t := .num n) rfl)
  | .vec v, _ =>
    rcases sub_vec_inv hs with rfl | rfl
    · exact dd_subsumeSub O hc ruleAt_valtypeSubVec (typedV_vectypeV v) (typedV_vectypeV v)
        (dd_leafSub O hc ruleAt_vectypeSub (typedV_vectypeV v))
    · exact dd_valtypeSubBot O hc (typedV_flat (t := .vec v) rfl)

/-! ## `select` -/

/-- `%([t, t, I32]) ->_[] %([t])`. -/
def itSelE : Exp := itLXE [.varE "t", .varE "t", .caseE "I32" (.tupE [])] [] [.varE "t"]

set_option maxRecDepth 100000 in
/-- `Instr_ok/select-expl`. -/
theorem ruleAt_selectExpl : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 3
    (.ruleD "select-expl" [ctxP, .expP "t" (.varT "valtype" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "SELECT" (.optE (some (.listE [.varE "t"]))), itSelE])
      [.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "t"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `t' = numtype \/ t' = vectype`. -/
def numOrVecE : Exp :=
  .binE .orOp .boolT
    (.cmpE .eqOp .boolT (.varE "t'") (.subE (.varE "numtype") (.varT "numtype" []) (.varT "valtype" [])))
    (.cmpE .eqOp .boolT (.varE "t'") (.subE (.varE "vectype") (.varT "vectype" []) (.varT "valtype" [])))

set_option maxRecDepth 100000 in
/-- `Instr_ok/select-impl`. -/
theorem ruleAt_selectImpl : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 4
    (.ruleD "select-impl" [ctxP, .expP "t" (.varT "valtype" []), .expP "t'" (.varT "valtype" []),
      .expP "numtype" (.varT "numtype" []), .expP "vectype" (.varT "vectype" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "SELECT" (.optE none), itSelE])
      [.rulePr "Valtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "t"]),
       .rulePr "Valtype_sub" [] "%|-%<:%" (.tupE [.varE "C", .varE "t", .varE "t'"]),
       .ifPr numOrVecE]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `%([t, t, I32]) ->_[] %([t])` evaluates. -/
theorem evalExp_itSel {env : Env} {ρ : VarEnv} {t : Value} (h : ρ.findVal? "t" = some t) :
    EvalExp env ρ itSelE (itV [t, t, tyV .i32] [] [t]) :=
  evalExp_case (evalExp_tup3
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_listE_iff.2 ⟨_,
      evalExps_cons (Sim.evalExp_var h) (evalExps_cons (Sim.evalExp_var h)
        (evalExps_cons Instr30X.evalExp_i32 evalExps_nil)), rfl⟩) evalExps_nil, rfl⟩))
    evalExp_nil (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_list1
      (Sim.evalExp_var h)) evalExps_nil, rfl⟩)))

/-- **`Instr_ok/select-expl`**, from `Valtype_ok` at the annotation. -/
theorem dd_selectExpl (O : ElseI) {c t : Value} (hc : CtxT B c)
    (ht : TypedV (simEnv B) (.varT "valtype" []) t)
    (hd : DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, t])) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, .case "SELECT" (.opt (some (.list [t]))), itV [t, t, tyV .i32] [] [t]]) :=
  dderivesB_of_ruleAt ruleAt_selectExpl (self_mem_conclAlts _) [("C", c), ("t", t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (ht _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (Sim.evalExp_var rfl)
      (evalExp_case (evalExp_optE_some_iff.2 ⟨_, evalExp_list1 (Sim.evalExp_var rfl), rfl⟩))
      (evalExp_itSel rfl))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl)
      (Sim.evalExp_var rfl)) hd))

/-- The scope of `select-impl`. -/
def selσ (c t t' n v : Value) : List (IL.Id × Value) :=
  [("C", c), ("t", t), ("t'", t'), ("numtype", n), ("vectype", v)]

/-- The side condition of `select-impl` at a number type. -/
theorem evalExp_numOrVec_num {env : Env} {c t : Value} (n : NumType) (v : VecType) :
    EvalExp env (VarEnv.empty.bindVals (selσ c t (tyV (.num n)) (tyV (.num n)) (tyV (.vec v))))
      numOrVecE (.bool true) :=
  evalExp_binE_iff.2 ⟨_, evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl,
    evalExp_subE_iff.2 (Sim.evalExp_var rfl), Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩,
    .inl rfl⟩

/-- Distinct images of a number and a vector type. -/
theorem tyV_num_ne_vec (n : NumType) (v : VecType) : tyV (.num n) ≠ tyV (.vec v) := by
  rw [tyV_num, tyV_vec]
  rcases n with n | n <;> cases n <;> cases v <;>
    simp [Silmaril.SpecTec.Equiv.Validation.numtypeV, Silmaril.SpecTec.Equiv.Validation.vectypeV]

/-- The side condition of `select-impl` at a vector type. -/
theorem evalExp_numOrVec_vec {env : Env} {c t : Value} (n : NumType) (v : VecType) :
    EvalExp env (VarEnv.empty.bindVals (selσ c t (tyV (.vec v)) (tyV (.num n)) (tyV (.vec v))))
      numOrVecE (.bool true) := by
  refine evalExp_binE_iff.2 ⟨.bool false, evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl,
    evalExp_subE_iff.2 (Sim.evalExp_var rfl), ?_⟩, .inr ⟨rfl, .bool true,
    evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, evalExp_subE_iff.2 (Sim.evalExp_var rfl),
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩, rfl⟩⟩
  have hne : (tyV (.vec v) == tyV (.num n)) = false := beq_eq_false_iff_ne.2 (tyV_num_ne_vec n v).symm
  simp only [cmpValues, hne]

/-- A subtype of a number or vector type is flat. -/
theorem flat_of_sub {Δ : TypeCtx} {t t' : CValType} (hs : Sub Δ t t') (hnv : t'.IsNumOrVec) :
    Flat t = true := by
  match t', hnv with
  | .num _, _ => exact (sub_num_inv hs).elim (fun h => h ▸ rfl) (fun h => h ▸ rfl)
  | .vec _, _ => exact (sub_vec_inv hs).elim (fun h => h ▸ rfl) (fun h => h ▸ rfl)

/-- Number and vector types are flat. -/
theorem flat_numVec {t' : CValType} (hnv : t'.IsNumOrVec) : Flat t' = true := by
  match t', hnv with
  | .num _, _ => rfl
  | .vec _, _ => rfl

/-- `select-impl` fires from its two premises and an evaluated side condition, at any choice of
the `numtype` and `vectype` quantifiers. -/
theorem dd_selectImpl' (O : ElseI) {c : Value} (hc : CtxT B c) {t t' : CValType}
    (hft : Flat t = true) (hft' : Flat t' = true)
    (hok : DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, tyV t]))
    (hsub : DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, tyV t, tyV t']))
    (n : NumType) (v : VecType)
    (he : EvalExp (simEnv B) (VarEnv.empty.bindVals (selσ c (tyV t) (tyV t') (tyV (.num n))
      (tyV (.vec v)))) numOrVecE (.bool true)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, .case "SELECT" (.opt none), itV [tyV t, tyV t, tyV .i32] [] [tyV t]]) := by
  refine dderivesB_of_ruleAt ruleAt_selectImpl (self_mem_conclAlts _)
    (selσ c (tyV t) (tyV t') (tyV (.num n)) (tyV (.vec v)))
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_flat hft _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_flat hft' _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_numtypeV n _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_vectypeV v _ (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (evalExp_optE_none_iff.2 rfl))
      (evalExp_itSel rfl)) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) hok
  · exact .rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) hsub
  · exact .ifPr he

/-- **`Instr_ok/select-impl`**, from Core's premises at a number or vector type `t'`. -/
theorem dd_selectImpl (O : ElseI) {c : Value} (hc : CtxT B c) {Δ : TypeCtx} {t t' : CValType}
    (hs : Sub Δ t t') (hnv : t'.IsNumOrVec) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, .case "SELECT" (.opt none), itV [tyV t, tyV t, tyV .i32] [] [tyV t]]) := by
  have hft : Flat t = true := flat_of_sub hs hnv
  have hok : DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, tyV t]) :=
    valtypeOk_flat O hc hft
  have hsub : DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, tyV t, tyV t']) :=
    valtypeSub_numVec O hc hs hnv
  match t', hnv with
  | .num n, _ =>
    exact dd_selectImpl' O hc hft rfl hok hsub n .v128 (evalExp_numOrVec_num n .v128)
  | .vec v, _ =>
    exact dd_selectImpl' O hc hft rfl hok hsub (.int .i32) v (evalExp_numOrVec_vec (.int .i32) v)

/-! ## The parametric instructions, preserved -/

/-- A source type without type indices closes to a flat type. -/
theorem flat_closeVal (C : Context) {t : ValType} (h : SrcFlat t = true) : Flat (C.closeVal t) = true := by
  match t, h with
  | .num t, _ => rfl
  | .vec t, _ => rfl
  | .ref ⟨n, .abstract a⟩, _ => rfl

/-- The encoding of a source type without type indices is the image of its closure. -/
theorem toValue_closeVal (C : Context) {t : ValType} (h : SrcFlat t = true) :
    Encode.toValue t = tyV (C.closeVal t) := by
  match t, h with
  | .num t, _ => rcases t with t | t <;> cases t <;> rfl
  | .vec t, _ => cases t; rfl
  | .ref ⟨n, .abstract a⟩, _ => cases n <;> cases a <;> rfl

/-- `select` without annotation. -/
theorem instrToV_selectNone : instrToV (.select none) = .case "SELECT" (.opt none) := rfl

/-- `Instr_ok/unreachable` at flat types, in any typed context. -/
theorem dd_unreachableFlat (O : ElseI) {c : Value} (hc : CtxT B c) {t₁ t₂ : List CValType}
    (hp : ∀ t ∈ t₁, Flat t = true) (hr : ∀ t ∈ t₂, Flat t = true) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV .unreachable, instrtypeV (.plain t₁ t₂)]) :=
  Instr30.dd_unreachable O hc
    (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact typedV_flat (hp t ht))
    (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact typedV_flat (hr t ht))
    (instrtypeOk_flat O hc hp hr)

/-- `Instr_ok/select-expl` at a source annotation without type indices, in any typed context. -/
theorem dd_selectExplFlat (O : ElseI) {C : Context} {c : Value} (hc : CtxT B c) {t : ValType}
    (hst : SrcFlat t = true) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, instrToV (.select (some [t])),
      instrtypeV (.plain [C.closeVal t, C.closeVal t, .i32] [C.closeVal t])]) := by
  have hft : Flat (C.closeVal t) = true := flat_closeVal C hst
  have e : instrToV (.select (some [t])) =
      .case "SELECT" (.opt (some (.list [tyV (C.closeVal t)]))) := by
    show Value.case "SELECT" (.opt (some (.list [Encode.toValue t]))) = _
    rw [toValue_closeVal C hst]
  rw [e]
  exact dd_selectExpl O hc (typedV_flat hft) (valtypeOk_flat O hc hft)

/-- **The parametric instructions are preserved, in any context**: a Core typing of `nop`,
`unreachable`, `drop` or `select` in any Core context, at flat types and (for `select t`) a source
annotation without type indices, is an `Instr_ok` fact of `simEnv B` in every typed context
value. -/
theorem parametric_preserves (O : ElseI) {C : Context} {c : Value} (hc : CtxT B c) {i : Instr}
    {it : InstrType} (h : ParametricInstrOk C i it)
    (hf : ∀ t ∈ it.params ++ it.results, Flat t = true)
    (hs : ∀ ts, i = .select (some ts) → ∀ t ∈ ts, SrcFlat t = true) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, instrToV i, instrtypeV it]) := by
  cases h with
  | nop => exact Instr30.dd_nop O hc
  | @unreachable t₁ t₂ _ =>
    exact dd_unreachableFlat O hc (fun t ht => hf t (List.mem_append_left _ ht))
      (fun t ht => hf t (List.mem_append_right _ ht))
  | @drop t _ =>
    have ht : Flat t = true := hf t (by simp)
    exact Instr30.dd_drop O hc (typedV_flat ht) (valtypeOk_flat O hc ht)
  | @selectExpl t _ =>
    exact dd_selectExplFlat O hc (hs [t] rfl t (List.mem_singleton_self t))
  | selectImpl _ hsub hnv => exact dd_selectImpl O hc hsub hnv

end Silmaril.Wasm.SpecTec.Institution.Instr30Y
