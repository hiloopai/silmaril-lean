module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Typing

/-!
# Parametric instructions: Core → SpecTec (`Forward.parametric`)

`unreachable`, `nop`, `drop`, `select-true`, `select-false` (`Step_pure` 0–4). The dropped and
selected values are typed `val` by `TypingFacts.vals`; the `select` annotation `(valtype*)?` is
typed by inverting the typing of the `SELECT` instruction against the fixed script's `instr`
(`Original.d271`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d271)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

/-! ## Evaluating `e?` over one domain -/

/-- `e?` with its one domain bound to an option: absent gives absent, present evaluates the body
with the domain variable bound to the payload. -/
theorem evalExp_iterOpt {env : Env} {ρ : VarEnv} {b : Exp} {x y : IL.Id} {o : Option Value}
    {v : Option Value} (h : ρ.findVal? y = some (.opt o))
    (hb : ∀ w, o = some w → ∃ u, v = some u ∧ EvalExp env (ρ.bindVals [(x, w)]) b u)
    (hn : o = none → v = none) :
    EvalExp env ρ (.iterE b (.mk .opt [.mk x (.varE y)])) (.opt v) := by
  refine evalExp_iterE_iff.2 ?_
  cases o with
  | none =>
      rw [hn rfl]
      refine ⟨3, ?_⟩
      simp [evalIterE, evalDoms, domVar, domSrc, evalExp, h, Res.ofOption, Value.asOpt?,
        Res.assert]
  | some w =>
      obtain ⟨u, rfl, ⟨k, hk⟩⟩ := hb w rfl
      refine ⟨k + 3, ?_⟩
      have hk' : evalExp (k + 2) env (ρ.bindVals [(x, w)]) b = .ok u :=
        evalExp_ok_of_le (by omega) hk
      simp [evalIterE, evalDoms, domVar, domSrc, evalExp, h, Res.ofOption, Value.asOpt?,
        Res.assert, hk']

/-- The annotation `(t*)?` of `SELECT`, bound to an option of lists. -/
theorem evalExp_selectAnnot {env : Env} {ρ : VarEnv} {o : Option (List Value)}
    (h : ρ.findVal? "t*?" = some (.opt (o.map .list))) :
    EvalExp env ρ (.iterE (.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")]))
      (.mk .opt [.mk "t*" (.varE "t*?")])) (.opt (o.map .list)) := by
  refine evalExp_iterOpt h (fun w hw => ⟨w, hw, ?_⟩) (fun hn => hn)
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  exact Equiv.Execution.evalExp_iterPat (by decide) (by simp [VarEnv.findVal?, VarEnv.bindVals,
    Map.binds, Map.bind])

/-! ## `select-true`, `select-false` -/

/-- The scope of the two `select` rules. -/
def scopeSel (v₁ v₂ c a : Value) : VarEnv :=
  VarEnv.empty.bindVals [("val_1", v₁), ("val_2", v₂), ("c", c), ("t*?", a)]

/-- The left-hand side both `select` rules share, evaluated. -/
theorem evalExp_selectLhs {env : Env} {v₁ v₂ c : Value} {o : Option (List Value)} :
    EvalExp env (scopeSel v₁ v₂ c (.opt (o.map .list)))
      (.listE [.subE (.varE "val_1") (.varT "val" []) (.varT "instr" []),
        .subE (.varE "val_2") (.varT "val" []) (.varT "instr" []),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c"]),
        .caseE "SELECT" (.iterE (.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")]))
          (.mk .opt [.mk "t*" (.varE "t*?")]))])
      (.list [v₁, v₂, .case "CONST" (.tuple [.case "I32" (.tuple []), c]),
        .case "SELECT" (.opt (o.map .list))]) :=
  evalExp_list4 (evalExp_subE_iff.2 (evalExp_var rfl)) (evalExp_subE_iff.2 (evalExp_var rfl))
    (evalExp_case (evalExp_tup2 evalExp_i32 (evalExp_var rfl)))
    (evalExp_case (evalExp_selectAnnot rfl))
where
  evalExp_list4 {e₁ e₂ e₃ e₄ : Exp} {u₁ u₂ u₃ u₄ : Value} {ρ : VarEnv}
      (h₁ : EvalExp env ρ e₁ u₁) (h₂ : EvalExp env ρ e₂ u₂) (h₃ : EvalExp env ρ e₃ u₃)
      (h₄ : EvalExp env ρ e₄ u₄) :
      EvalExp env ρ (.listE [e₁, e₂, e₃, e₄]) (.list [u₁, u₂, u₃, u₄]) :=
    evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ (evalExps_cons h₃
      (evalExps_cons h₄ evalExps_nil))), rfl⟩

/-- The four quantifier typings of the `select` rules. -/
structure SelTyped (env : Env) (v₁ v₂ c a : Value) : Prop where
  h₁ : HasTyp env (scopeSel v₁ v₂ c a) (.varT "val" []) v₁
  h₂ : HasTyp env (scopeSel v₁ v₂ c a) (.varT "val" []) v₂
  hc : HasTyp env (scopeSel v₁ v₂ c a) (.varT "num_" [.expA (.caseE "I32" (.tupE []))]) c
  ha : HasTyp env (scopeSel v₁ v₂ c a) (.iterT (.iterT (.varT "valtype" []) .list) .opt) a

/-- `Step_pure/select-true`. -/
theorem spure_selectTrue {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 3 Equiv.Execution.selectTrueRule)
    {v₁ v₂ : Value} {n : Nat} {o : Option (List Value)}
    (hty : SelTyped env v₁ v₂ (.case "%" (.tuple [natV n])) (.opt (o.map .list))) (hn : n ≠ 0) :
    SPure env [v₁, v₂,
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [natV n])]),
      .case "SELECT" (.opt (o.map .list))] [v₁] := by
  have hne : EvalExp env (scopeSel v₁ v₂ (.case "%" (.tuple [natV n])) (.opt (o.map .list)))
      (.cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") 0) (.numE (.natN 0)))
      (.bool true) := by
    have he := evalExp_ne (t := .boolT) (evalExp_pctPayload (env := env) (x := "c") (n := n)
      (ρ := scopeSel v₁ v₂ (.case "%" (.tuple [natV n])) (.opt (o.map .list))) rfl)
      (evalExp_num (m := .natN 0))
    have hb : (!(Value.num (.natN n) == Value.num (.natN 0))) = true := by simp [hn]
    rwa [hb] at he
  exact dderives_of_ruleAt h _
    (QuantsOk.cons rfl hty.h₁ (QuantsOk.cons rfl hty.h₂ (QuantsOk.cons rfl hty.hc
      (QuantsOk.cons rfl hty.ha QuantsOk.nil))))
    (evalExp_tup2 evalExp_selectLhs (evalExp_list1 (evalExp_subE_iff.2 (evalExp_var rfl))))
    (prems_one (.ifPr hne))

/-- `Step_pure/select-false`. -/
theorem spure_selectFalse {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 4 Equiv.Execution.selectFalseRule)
    {v₁ v₂ : Value} {o : Option (List Value)}
    (hty : SelTyped env v₁ v₂ (.case "%" (.tuple [natV 0])) (.opt (o.map .list))) :
    SPure env [v₁, v₂,
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [natV 0])]),
      .case "SELECT" (.opt (o.map .list))] [v₂] := by
  have heq : EvalExp env (scopeSel v₁ v₂ (.case "%" (.tuple [natV 0])) (.opt (o.map .list)))
      (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE "c") "%") 0) (.numE (.natN 0)))
      (.bool true) := by
    have he := evalExp_eq (t := .boolT) (evalExp_pctPayload (env := env) (x := "c") (n := 0)
      (ρ := scopeSel v₁ v₂ (.case "%" (.tuple [natV 0])) (.opt (o.map .list))) rfl)
      (evalExp_num (m := .natN 0))
    simpa using he
  exact dderives_of_ruleAt h _
    (QuantsOk.cons rfl hty.h₁ (QuantsOk.cons rfl hty.h₂ (QuantsOk.cons rfl hty.hc
      (QuantsOk.cons rfl hty.ha QuantsOk.nil))))
    (evalExp_tup2 evalExp_selectLhs (evalExp_list1 (evalExp_subE_iff.2 (evalExp_var rfl))))
    (prems_one (.ifPr heq))

/-! ## Inverting the typing of an instruction -/

/-- The cases of the `k`-th instance of the `i`-th type of a recursive group. -/
def recCases (d : Def) (i k : Nat) : List TypCase :=
  match d with
  | .recD ds => match ds[i]? with
    | some d' => instCases d' k
    | none => []
  | _ => []

set_option maxRecDepth 100000 in
theorem findTyp_instr' (B : Builtins) : (simEnv B).findTyp? "instr" =
    some ([], [.instD [] [] (.variantT (recCases Original.d271 0 0))]) := rfl

/-- A payload typed by a variant's case is typed by the case's type. -/
theorem hasTyp_of_hasTypCase {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {t : Typ} {prems : List Prem} {w : Value},
      HasTypCase env σ cs op w → findCase cs op = some (t, prems) → HasTyp env σ t w
  | [], _, _, _, _, h, _ => absurd h not_hasTypCase_nil
  | .mk o t' _ prems' :: cs, op, t, prems, w, h, hf => by
      by_cases ho : o = op
      · simp only [findCase, ho, ite_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact ((hasTypCase_cons_hit_iffQ ho).1 h).1
      · simp only [findCase, ho, ite_false] at hf
        exact hasTyp_of_hasTypCase ((hasTypCase_cons_miss_iff ho).1 h) hf

/-- Matching no argument patterns leaves the scope as it is. -/
theorem matchArgs_nil_scope {env : Env} {ρ σ : VarEnv} {ws : List ArgV}
    (h : MatchArgs env ρ [] ws σ) : σ = ρ := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [matchArgs] at h
  | succ n => cases ws <;> simp [matchArgs] at h ⊢; exact h.symm

/-- **Inversion of `instr`**: a typed injection carries a payload of its case's type. -/
theorem hasTyp_instr_inv {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {op : MixopS} {w : Value}
    {t : Typ} {prems : List Prem} (h : HasTyp (simEnv B) ρ (.varT "instr" []) (.case op w))
    (hf : findCase (recCases Original.d271 0 0) op = some (t, prems)) :
    HasTyp (simEnv B) VarEnv.empty t w := by
  have hl : localTyp? ρ "instr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_instr'] at htd
  cases htd
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hi'
  · obtain rfl := matchArgs_nil_scope hm
    obtain ⟨op', w', he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    exact hasTyp_of_hasTypCase hc hf
  · exact absurd hi' not_hasTypInsts_nil

/-- A closed type name is typed alike in every scope binding term variables only. -/
theorem hasTyp_varT_nil_congr {env : Env} {ρ ρ' : VarEnv} (hρ : ValsOnly ρ) (hρ' : ValsOnly ρ')
    {x : IL.Id} {v : Value} (h : HasTyp env ρ (.varT x []) v) : HasTyp env ρ' (.varT x []) v := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hl' : localTyp? ρ' x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ'.1]
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hargs
  exact (hasTyp_varT_global_iff hl').2 ⟨td, [], htd, Equiv.evalArgs_nil, hi⟩

/-- The `select` annotation type `(valtype*)?`, in any scope binding term variables only. -/
theorem hasTyp_selAnnot_congr {env : Env} {ρ ρ' : VarEnv} (hρ : ValsOnly ρ) (hρ' : ValsOnly ρ')
    {v : Value} (h : HasTyp env ρ (.iterT (.iterT (.varT "valtype" []) .list) .opt) v) :
    HasTyp env ρ' (.iterT (.iterT (.varT "valtype" []) .list) .opt) v := by
  rcases hasTyp_iterT_opt_iff.1 h with rfl | ⟨w, rfl, hw⟩
  · exact hasTyp_iterT_opt_iff.2 (.inl rfl)
  · obtain ⟨l, rfl, hl⟩ := hasTyp_iterT_list_iff.1 hw
    refine hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, hasTyp_iterT_list_iff.2 ⟨l, rfl, ?_⟩⟩)
    exact hasTypList_iff.2 fun u hu => hasTyp_varT_nil_congr hρ hρ' (hasTypList_iff.1 hl u hu)


/-! ## The forward obligations -/

variable {H : Type} {hn : H → String} {B : Builtins}

/-- The image of `select t*?`. -/
theorem instrToV_select (ts : Option (List ValType)) :
    instrToV (.select ts) =
      .case "SELECT" (.opt ((ts.map (·.map Encode.toValue)).map .list)) := by
  cases ts <;> rfl

/-- Values on a typed instruction sequence are typed `val`, in any scope of term variables. -/
theorem typedV_val (T : TypingFacts (simEnv B) hn) {vs : List Val}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs)))) {v : Val} (hv : v ∈ vs)
    {ρ : VarEnv} (hρ : ValsOnly ρ) : HasTyp (simEnv B) ρ (.varT "val" []) (valV v) := by
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 (T.vals vs h ρ hρ)
  have hmap : adminsToV (vals vs) = vs.map valV := by
    simp [adminsToV_eq_map, vals, adminToV_toAdmin]
  rw [hmap] at hl
  cases hl
  exact hasTypList_iff.1 hall _ (List.mem_map_of_mem hv)

/-- The `instr` at the end of a typed sequence is typed `instr`. -/
theorem typedV_last (a : List Value) (i : Value)
    (h : TypedV (simEnv B) instrsT (.list (a ++ [i]))) :
    HasTyp (simEnv B) VarEnv.empty (.varT "instr" []) i := by
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 (h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  cases hl
  exact hasTypList_iff.1 hall _ (by simp)

/-- The typings of a `select` instance, from the typed configuration. -/
theorem selTyped (T : TypingFacts (simEnv B) hn) {v₁ v₂ : Val} {c : BitVec 32}
    {ts : Option (List ValType)}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV (vals [v₁, v₂, Val.i32 c]) ++
      [instrToV (.select ts)]))) :
    SelTyped (simEnv B) (valV v₁) (valV v₂) (bvV c)
      (.opt ((ts.map (·.map Encode.toValue)).map .list)) := by
  have hρ : ValsOnly (scopeSel (valV v₁) (valV v₂) (bvV c)
      (.opt ((ts.map (·.map Encode.toValue)).map .list))) := ⟨rfl, rfl, rfl⟩
  have hvs := ((T.append _ _).1 h).1
  have hi := typedV_last _ _ h
  rw [instrToV_select] at hi
  exact ⟨typedV_val T hvs (by simp) hρ, typedV_val T hvs (by simp) hρ,
    hasTyp_num (t := .i32) c evalExp_i32,
    hasTyp_selAnnot_congr ⟨rfl, rfl, rfl⟩ hρ (hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ hi rfl)⟩

/-- `ParametricStep.drop`. -/
theorem fwd_drop (T : TypingFacts (simEnv B) hn) {s : Store H} {f : Frame} (v : Val) :
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, .plain .drop]⟩ ⟨s, f, []⟩ := by
  intro hc hc'
  obtain ⟨-, hcode⟩ := (T.config _).1 hc
  have hv : HasTyp (simEnv B) (VarEnv.empty.bindVals [("val", valV v)]) (.varT "val" [])
      (valV v) :=
    typedV_val T ((T.append (adminsToV (vals [v])) [instrToV .drop]).1 hcode).1
      (List.mem_singleton_self v) ⟨rfl, rfl, rfl⟩
  have hp : SPure (simEnv B) (adminsToV [v.toAdmin, .plain .drop]) (adminsToV []) := by
    show SPure (simEnv B) [adminToV v.toAdmin, .case "DROP" (.tuple [])] []
    rw [adminToV_toAdmin]
    exact spure_drop (hasPureRules_simEnv B).drop hv
  exact fwd_of_spure T (hasStepRules_simEnv B).pure hp hc hc'

/-- `ParametricStep.selectTrue`. -/
theorem fwd_selectTrue (T : TypingFacts (simEnv B) hn) {s : Store H} {f : Frame} {v₁ v₂ : Val}
    {c : BitVec 32} {ts : Option (List ValType)} (hc0 : c ≠ 0) :
    FwdP (simEnv B) hn ⟨s, f, [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]⟩
      ⟨s, f, [v₁.toAdmin]⟩ := by
  intro hc hc'
  obtain ⟨-, hcode⟩ := (T.config _).1 hc
  have hty := selTyped T (v₁ := v₁) (v₂ := v₂) (c := c) (ts := ts) hcode
  have hn0 : c.toNat ≠ 0 := fun h0 => hc0 (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hp : SPure (simEnv B) (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c,
      .plain (.select ts)]) (adminsToV [v₁.toAdmin]) := by
    show SPure (simEnv B) [adminToV v₁.toAdmin, adminToV v₂.toAdmin, adminToV (constI32 c),
      instrToV (.select ts)] [adminToV v₁.toAdmin]
    rw [adminToV_toAdmin, adminToV_toAdmin, instrToV_select]
    exact spure_selectTrue (hasPureRules_simEnv B).selectTrue hty hn0
  exact fwd_of_spure T (hasStepRules_simEnv B).pure hp hc hc'

/-- `ParametricStep.selectFalse`. -/
theorem fwd_selectFalse (T : TypingFacts (simEnv B) hn) {s : Store H} {f : Frame} (v₁ v₂ : Val)
    (ts : Option (List ValType)) :
    FwdP (simEnv B) hn ⟨s, f, [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)]⟩
      ⟨s, f, [v₂.toAdmin]⟩ := by
  intro hc hc'
  obtain ⟨-, hcode⟩ := (T.config _).1 hc
  have hty := selTyped T (v₁ := v₁) (v₂ := v₂) (c := 0) (ts := ts) hcode
  have hp : SPure (simEnv B) (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 0,
      .plain (.select ts)]) (adminsToV [v₂.toAdmin]) := by
    show SPure (simEnv B) [adminToV v₁.toAdmin, adminToV v₂.toAdmin, adminToV (constI32 0),
      instrToV (.select ts)] [adminToV v₂.toAdmin]
    rw [adminToV_toAdmin, adminToV_toAdmin, instrToV_select]
    exact spure_selectFalse (hasPureRules_simEnv B).selectFalse hty
  exact fwd_of_spure T (hasStepRules_simEnv B).pure hp hc hc'

/-- **`Forward.parametric` in `simEnv B`**: `unreachable`, `nop`, `drop`, `select`. -/
theorem fwd_parametric (T : TypingFacts (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {is is' : List Admin} (_ : ParametricStep is is'),
      FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is is' h
  cases h with
  | unreachable =>
      exact fwd_of_spure T (hasStepRules_simEnv B).pure
        (spure_unreachable (hasPureRules_simEnv B).unreachable)
  | nop =>
      exact fwd_of_spure T (hasStepRules_simEnv B).pure (spure_nopRule (hasPureRules_simEnv B).nop)
  | drop v => exact fwd_drop T v
  | selectTrue hc0 => exact fwd_selectTrue T hc0
  | selectFalse v₁ v₂ ts => exact fwd_selectFalse T v₁ v₂ ts

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
