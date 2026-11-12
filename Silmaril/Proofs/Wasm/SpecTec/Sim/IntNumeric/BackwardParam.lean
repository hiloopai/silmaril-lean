module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Backward

/-!
# Parametric instructions: SpecTec → Core (`Step_pure` 0–4)

`drop` and `select` quantify over `val`: the typed reading makes the operands values, which is what
lets them be decoded back to Core values (`dec_val`). Without the quantifier typing (the evaluator
reading), `drop` would fire on any instruction.
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
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d269)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {hn : H → String} {B : Builtins} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-! ## Values of type `val` are Core values -/

/-- A case not declared by a variant does not inhabit it. -/
theorem not_hasTypCase_of_findCase_none {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {w : Value}, findCase cs op = none →
      ¬ HasTypCase env σ cs op w
  | [], _, _, _, h => not_hasTypCase_nil h
  | .mk o t _ prems :: cs, op, w, hf, h => by
      by_cases ho : o = op
      · simp [findCase, ho] at hf
      · simp only [findCase, ho, ite_false] at hf
        exact not_hasTypCase_of_findCase_none hf ((hasTypCase_cons_miss_iff ho).1 h)

set_option maxRecDepth 100000 in
theorem findTyp_val : (simEnv B).findTyp? "val" =
    some ([], [.instD [] [] (.variantT (instCases Original.d269 0))]) := rfl

/-- A value of type `val` is an injection by a case `val` declares. -/
theorem val_tag {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "val" []) v) :
    ∃ op w, v = .case op w ∧ findCase (instCases Original.d269 0) op ≠ none := by
  have hl : localTyp? ρ "val" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_val] at htd
  cases htd
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hi'
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    exact ⟨op, w, rfl, fun hn => not_hasTypCase_of_findCase_none hn hc⟩
  · exact absurd hi' not_hasTypInsts_nil

/-- The `val` tag of an instruction's image. -/
theorem instr_val_tag {i : Instr} {op : String} {w : Value} (h : instrToV i = .case op w)
    (hop : findCase (instCases Original.d269 0) op ≠ none) :
    ∃ v : Val, Admin.plain i = v.toAdmin := by
  cases i
  all_goals (try cases_type* ConvertOp IntUnOp IntBinOp IntTestOp IntRelOp)
  all_goals (try cases_type* FloatUnOp FloatBinOp FloatRelOp)
  all_goals (try cases_type* IntType FloatType Signedness PackSize)
  all_goals (try cases_type* Option)
  all_goals first
    | exact ⟨.num ⟨.int _, _⟩, rfl⟩
    | exact ⟨.num ⟨.float _, _⟩, rfl⟩
    | exact ⟨.vec _, rfl⟩
    | (injection h with h1; subst h1; exact absurd hop (by decide))
    | cases h
    | (have h1 := vec_tag rfl h; rw [Silmaril.Wasm.SpecTec.encodeInstruction] at h1;
       simp only at h1; subst h1; exact absurd hop (by decide))

/-- **An admin typed `val` is a Core value.** -/
theorem dec_val {ρ : VarEnv} (hρ : ValsOnly ρ) {a : Admin}
    (h : HasTyp (simEnv B) ρ (.varT "val" []) (adminToV a)) : ∃ v : Val, a = v.toAdmin := by
  obtain ⟨op, w, hw, hop⟩ := val_tag hρ h
  cases a with
  | plain i => exact instr_val_tag hw hop
  | ref r => exact ⟨.ref r, rfl⟩
  | _ => injection hw with h1; subst h1; exact absurd hop (by decide)

/-- A typed quantifier, read off `QuantsOk`. -/
theorem quant_typed {env : Env} {ρ : VarEnv} {qs : List Param} (h : QuantsOk env ρ qs) {x : IL.Id}
    {t : Typ} (hx : Param.expP x t ∈ qs) : ∃ w, ρ.findVal? x = some w ∧ HasTyp env ρ t w :=
  h x t hx

/-! ## The five rules -/

/-- `adminsToV` of a one-element sequence. -/
theorem adminsToV_eq_one {is : List Admin} {u : Value} (h : adminsToV is = [u]) :
    ∃ a, is = [a] ∧ adminToV a = u := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨a, rfl, h⟩

/-- `adminsToV` of a four-element sequence. -/
theorem adminsToV_eq_four {is : List Admin} {u₁ u₂ u₃ u₄ : Value}
    (h : adminsToV is = [u₁, u₂, u₃, u₄]) :
    ∃ a₁ a₂ a₃ a₄, is = [a₁, a₂, a₃, a₄] ∧ adminToV a₁ = u₁ ∧ adminToV a₂ = u₂ ∧
      adminToV a₃ = u₃ ∧ adminToV a₄ = u₄ := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a₁, a₂, a₃, a₄], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨a₁, a₂, a₃, a₄, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- A nullary case `OP`, inverted. -/
theorem evalExp_nullary_inv {env : Env} {ρ : VarEnv} {op : MixopS} {v : Value}
    (h : EvalExp env ρ (.caseE op (.tupE [])) v) : v = .case op (.tuple []) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  rw [Equiv.Validation.evalExps_nil_iff.1 hus]

/-- **`Step_pure/unreachable` (0), backward.** -/
theorem bwd_unreachable {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 0 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, -⟩ := fires_body (hasPureRules_simEnv B).unreachable hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨vs, hvs, h1⟩ := evalExp_listE_inv hl
  obtain ⟨ws, hws, h2⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₁, h1⟩
  cases h1
  rcases h2 with _ | ⟨e₂, h2⟩
  cases h2
  obtain rfl := evalExp_nullary_inv e₁
  obtain rfl := evalExp_nullary_inv e₂
  cases hws
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one (Value.list.inj hvs)
  obtain ⟨i, rfl, hi⟩ := dec_admin_plain ha (by decide)
  obtain rfl := dec_unreachable hi
  exact ⟨[.trap], rfl, .parametric .unreachable⟩

/-- **`Step_pure/nop` (1), backward.** -/
theorem bwd_nop {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 1 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, -⟩ := fires_body (hasPureRules_simEnv B).nop hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨vs, hvs, h1⟩ := evalExp_listE_inv hl
  obtain ⟨ws, hws, h2⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₁, h1⟩
  cases h1
  cases h2
  obtain rfl := evalExp_nullary_inv e₁
  cases hws
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one (Value.list.inj hvs)
  obtain ⟨i, rfl, hi⟩ := dec_admin_plain ha (by decide)
  obtain rfl := dec_nop hi
  exact ⟨[], rfl, .parametric .nop⟩

/-- A `val`-typed quantifier bound to an admin's image makes that admin a Core value. -/
theorem val_of_quant {σ : List (IL.Id × Value)} {x : IL.Id} {qs : List Param} {a : Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hx : Param.expP x (.varT "val" []) ∈ qs)
    (ha : (VarEnv.empty.bindVals σ).findVal? x = some (adminToV a)) : ∃ v : Val, a = v.toAdmin := by
  obtain ⟨u, hu, hty⟩ := quant_typed hq hx
  have hua : u = adminToV a := Option.some.inj (hu.symm.trans ha)
  exact dec_val ⟨rfl, rfl, rfl⟩ (hua ▸ hty)

/-- `drop`'s left-hand side, decoded. -/
theorem drop_lhs_inv {σ : List (IL.Id × Value)} {is : List Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) [.expP "val" (.varT "val" [])])
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.subE (.varE "val") (.varT "val" []) (.varT "instr" []),
        .caseE "DROP" (.tupE [])]) (.list (adminsToV is))) :
    ∃ v : Val, is = [v.toAdmin, .plain .drop] := by
  obtain ⟨vs, hvs, h2⟩ := evalExp_listE_inv hl
  rcases h2 with _ | ⟨e₁, _ | ⟨e₂, h2⟩⟩
  cases h2
  obtain ⟨a₁, a₂, rfl, ha₁, ha₂⟩ := adminsToV_eq_two (Value.list.inj hvs)
  have hd : a₂ = .plain .drop := by
    obtain ⟨i, rfl, hi⟩ := dec_admin_plain (ha₂.trans (evalExp_nullary_inv e₂)) (by decide)
    rw [dec_drop hi]
  have hv : (VarEnv.empty.bindVals σ).findVal? "val" = some (adminToV a₁) :=
    ha₁ ▸ evalExp_varE_iff.1 (evalExp_subE_iff.1 e₁)
  obtain ⟨v, rfl⟩ := val_of_quant hq (List.mem_singleton_self _) hv
  exact ⟨v, by rw [hd]⟩

/-- **`Step_pure/drop` (2), backward.** The dropped operand is typed `val`, hence a Core value. -/
theorem bwd_drop {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 2 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, hq, he, -⟩ := fires_body (hasPureRules_simEnv B).drop hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨v, rfl⟩ := drop_lhs_inv hq hl
  have hw : w = .list [] := by
    obtain ⟨ws, rfl, h2⟩ := evalExp_listE_inv hr
    cases h2
    rfl
  exact ⟨[], hw, .parametric (.drop v)⟩

/-- The `select` left-hand side, split into four admins with their bindings. -/
theorem select_lhs_split {σ : List (IL.Id × Value)} {is : List Admin}
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.subE (.varE "val_1") (.varT "val" []) (.varT "instr" []),
        .subE (.varE "val_2") (.varT "val" []) (.varT "instr" []),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c"]),
        .caseE "SELECT" (.iterE (.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")]))
          (.mk .opt [.mk "t*" (.varE "t*?")]))]) (.list (adminsToV is))) :
    ∃ a₁ a₂ a₃ a₄ c p, is = [a₁, a₂, a₃, a₄] ∧
      (VarEnv.empty.bindVals σ).findVal? "val_1" = some (adminToV a₁) ∧
      (VarEnv.empty.bindVals σ).findVal? "val_2" = some (adminToV a₂) ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some c ∧
      adminToV a₃ = .case "CONST" (.tuple [ntV .i32, c]) ∧ adminToV a₄ = .case "SELECT" p := by
  obtain ⟨vs, hvs, h4⟩ := evalExp_listE_inv hl
  rcases h4 with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, _ | ⟨e₄, h4⟩⟩⟩⟩
  cases h4
  obtain ⟨c, hc, rfl⟩ := evalExp_constI32_inv e₃
  obtain ⟨p, -, rfl⟩ := evalExp_caseE_iff.1 e₄
  obtain ⟨a₁, a₂, a₃, a₄, rfl, ha₁, ha₂, ha₃, ha₄⟩ := adminsToV_eq_four (Value.list.inj hvs)
  exact ⟨a₁, a₂, a₃, a₄, c, p, rfl, ha₁ ▸ evalExp_varE_iff.1 (evalExp_subE_iff.1 e₁),
    ha₂ ▸ evalExp_varE_iff.1 (evalExp_subE_iff.1 e₂), hc, ha₃, ha₄⟩

/-- The shared left-hand side of the two `select` rules, decoded: two Core values, an `i32`
constant and a `select`. -/
theorem select_lhs_inv {is : List Admin} {σ : List (IL.Id × Value)}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ)
      [.expP "val_1" (.varT "val" []), .expP "val_2" (.varT "val" []),
        .expP "c" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
        .expP "t*?" (.iterT (.iterT (.varT "valtype" []) .list) .opt)])
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.subE (.varE "val_1") (.varT "val" []) (.varT "instr" []),
        .subE (.varE "val_2") (.varT "val" []) (.varT "instr" []),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c"]),
        .caseE "SELECT" (.iterE (.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")]))
          (.mk .opt [.mk "t*" (.varE "t*?")]))]) (.list (adminsToV is))) :
    ∃ (v₁ v₂ : Val) (b : BitVec 32) (ts : Option (List ValType)),
      is = [v₁.toAdmin, v₂.toAdmin, constI32 b, .plain (.select ts)] ∧
      (VarEnv.empty.bindVals σ).findVal? "val_1" = some (adminToV v₁.toAdmin) ∧
      (VarEnv.empty.bindVals σ).findVal? "val_2" = some (adminToV v₂.toAdmin) ∧
      (VarEnv.empty.bindVals σ).findVal? "c" = some (bvV b) := by
  obtain ⟨a₁, a₂, a₃, a₄, c, p, rfl, h₁, h₂, hc, ha₃, ha₄⟩ := select_lhs_split hl
  obtain ⟨v₁, rfl⟩ := val_of_quant hq (by simp) h₁
  obtain ⟨v₂, rfl⟩ := val_of_quant hq (by simp) h₂
  obtain ⟨b, rfl, rfl⟩ := dec_intConst (t := .i32) ha₃
  obtain ⟨i₄, rfl, hi₄⟩ := dec_admin_plain ha₄ (by decide)
  obtain ⟨ts, rfl, -⟩ := dec_select hi₄
  exact ⟨v₁, v₂, b, ts, rfl, h₁, h₂, hc⟩

/-- The `c!%.0` of a bit pattern `c`. -/
theorem payload_eq {ρ : VarEnv} {b : BitVec 32} {v : Value} (hc : ρ.findVal? "c" = some (bvV b))
    (h : EvalExp (simEnv B) ρ (.projE (.uncaseE (.varE "c") "%") 0) v) : v = natV b.toNat :=
  h.unique (Equiv.evalExp_uNV_payload hc)

/-- **`Step_pure/select-true` (3), backward.** -/
theorem bwd_selectTrue {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 3 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, hq, he, hp⟩ := fires_body (hasPureRules_simEnv B).selectTrue hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨v₁, v₂, b, ts, rfl, h₁, -, hc⟩ := select_lhs_inv hq hl
  obtain ⟨ws, hws, h1⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₅, h1⟩
  cases h1
  have h₅ := evalExp_varE_iff.1 (evalExp_subE_iff.1 e₅)
  rw [h₁] at h₅
  cases h₅
  cases hws
  obtain ⟨x₁, x₂, hx₁, hx₂, hne⟩ := evalExp_cmpE_iff.1 (prem_if hp)
  obtain rfl := payload_eq hc hx₁
  obtain rfl := evalExp_numE_iff.1 hx₂
  have hb : b ≠ 0 := by
    intro h0
    subst h0
    simp [cmpValues, natV] at hne
  exact ⟨[v₁.toAdmin], rfl, .parametric (.selectTrue hb)⟩

/-- **`Step_pure/select-false` (4), backward.** -/
theorem bwd_selectFalse {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 4 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, hq, he, hp⟩ := fires_body (hasPureRules_simEnv B).selectFalse hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨v₁, v₂, b, ts, rfl, -, h₂, hc⟩ := select_lhs_inv hq hl
  obtain ⟨ws, hws, h1⟩ := evalExp_listE_inv hr
  rcases h1 with _ | ⟨e₅, h1⟩
  cases h1
  have h₅ := evalExp_varE_iff.1 (evalExp_subE_iff.1 e₅)
  rw [h₂] at h₅
  cases h₅
  cases hws
  obtain ⟨v, hx₁, hx₂⟩ := evalExp_eq_true (prem_if hp)
  obtain rfl := payload_eq hc hx₁
  have h0 : b.toNat = 0 := by
    have := evalExp_numE_iff.1 hx₂
    simpa [natV] using this
  have hb : b = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hb
  exact ⟨[v₂.toAdmin], rfl, .parametric (.selectFalse v₁ v₂ ts)⟩


end Silmaril.Wasm.SpecTec.Sim.IntNumeric
