module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Decode
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Main

/-!
# Integer numerics and parametric instructions: SpecTec → Core

Each `bwd_*` inverts one `Step_pure` rule at the image of a Core instruction sequence: whatever the
rule derives is the image of a Core step. The rule body is unpacked (`fires_body`), its conclusion
inverted to values, the instruction sequence decoded (`Decode.lean`), and the premise's call
identified with `IntegerN` by the uniqueness of `Applies` (`applies_binop_int` & co.).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-! ## Unpacking a rule body -/

/-- `Fires` at a rule the environment contains: an assignment whose conclusion evaluates to the
value and whose premises hold. -/
theorem fires_body {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e prems)) {v : Value}
    (hf : Fires env x k v) :
    ∃ σ : List (IL.Id × Value), QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env)) (otherwise env x [] k v)
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := hf
  obtain ⟨ps, t', rules', hrel', rfl, hk⟩ := h
  rw [hrel] at hrel'
  obtain ⟨rfl, rfl⟩ : t = t' ∧ rules = rules' := by
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hrel'
    exact hrel'
  rw [hr] at hk
  cases hk
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := hb
  simp only [bindParams, Option.some.injEq] at hps
  subst hps
  exact ⟨σ, hq, he, hp⟩

/-- A two-component tuple, inverted. -/
theorem evalExp_tup2_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  cases hv
  obtain ⟨a, xs, h1, ha, hxs⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  cases h1
  obtain ⟨b, ys, h2, hb, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hxs
  cases h2
  exact ⟨ha, hb⟩

/-- A list of expressions, inverted elementwise. -/
theorem evalExp_listE_inv {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {v : Value}, EvalExp env ρ (.listE es) v →
      ∃ vs : List Value, v = .list vs ∧ List.Forall₂ (EvalExp env ρ) es vs := by
  intro es v h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  refine ⟨vs, rfl, ?_⟩
  clear h
  induction es generalizing vs with
  | nil => rw [Equiv.Validation.evalExps_nil_iff.1 hvs]; exact .nil
  | cons e es ih =>
      obtain ⟨a, xs, rfl, ha, hxs⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
      exact .cons ha (ih _ hxs)

/-- `OP (x, y)` with `x`, `y` variables, inverted. -/
theorem evalExp_opVars_inv {env : Env} {ρ : VarEnv} {op : MixopS} {x y : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE op (.tupE [.varE x, .varE y])) v) :
    ∃ a b, ρ.findVal? x = some a ∧ ρ.findVal? y = some b ∧ v = .case op (.tuple [a, b]) := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨a, xs, rfl, ha, hxs⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, ys, rfl, hb, hys⟩ := Equiv.Validation.evalExps_cons_iff.1 hxs
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hys
  exact ⟨a, b, evalExp_varE_iff.1 ha, evalExp_varE_iff.1 hb, rfl⟩

/-- `adminsToV` of a sequence equal to a literal list of three: three admins. -/
theorem adminsToV_eq_three {is : List Admin} {u₁ u₂ u₃ : Value}
    (h : adminsToV is = [u₁, u₂, u₃]) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ adminToV a₁ = u₁ ∧ adminToV a₂ = u₂ ∧ adminToV a₃ = u₃ := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a₁, a₂, a₃], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨a₁, a₂, a₃, rfl, h.1, h.2.1, h.2.2⟩

/-- `adminsToV` of a sequence equal to a literal list of two: two admins. -/
theorem adminsToV_eq_two {is : List Admin} {u₁ u₂ : Value} (h : adminsToV is = [u₁, u₂]) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ adminToV a₁ = u₁ ∧ adminToV a₂ = u₂ := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a₁, a₂], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨a₁, a₂, rfl, h.1, h.2⟩

/-! ## Decoding administrative instructions -/

/-- The tags only administrative instructions and references carry. -/
def adminTags : List String :=
  ["CALL_REF", "RETURN_CALL_REF", "LABEL_%{%}%", "HANDLER_%{%}%", "FRAME_%{%}%", "TRAP",
    "REF.I31_NUM", "REF.NULL_ADDR", "REF.STRUCT_ADDR", "REF.ARRAY_ADDR", "REF.FUNC_ADDR",
    "REF.EXN_ADDR", "REF.HOST_ADDR", "REF.EXTERN"]

/-- An admin whose image carries an instruction tag is a plain instruction. -/
theorem dec_admin_plain {a : Admin} {op : String} {p : Value} (h : adminToV a = .case op p)
    (hop : op ∉ adminTags) : ∃ i, a = .plain i ∧ instrToV i = .case op p := by
  cases a with
  | plain i => exact ⟨i, rfl, h⟩
  | ref r =>
      exfalso
      cases r <;> (injection h with h1; subst h1; exact hop (by decide))
  | _ => exfalso; injection h with h1; subst h1; exact hop (by decide)

/-- `ntV` is injective. -/
theorem ntV_inj {t t' : IntType} (h : ntV t = ntV t') : t = t' := by
  cases t <;> cases t' <;> first | rfl | (injection h with h1; exact absurd h1 (by decide))

/-- A float type is not an integer type. -/
theorem float_ne_ntV (t : FloatType) (t' : IntType) :
    Encode.toValue (NumType.float t) ≠ ntV t' := by
  intro h
  cases t <;> cases t' <;> (injection h with h1; exact absurd h1 (by decide))

/-- A constant at an integer type is an integer constant. -/
theorem dec_intConst {a : Admin} {t : IntType} {c : Value}
    (h : adminToV a = .case "CONST" (.tuple [ntV t, c])) :
    ∃ b : BitVec t.width, a = .plain (.intConst t b) ∧ c = bvV b := by
  obtain ⟨i, rfl, hi⟩ := dec_admin_plain h (by decide)
  rcases dec_const hi with ⟨t', b, rfl, hp⟩ | ⟨t', b, rfl⟩
  · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
    obtain ⟨ht, rfl⟩ := hp
    obtain rfl := ntV_inj ht
    exact ⟨b, rfl, rfl⟩
  · exfalso
    injection hi with _ h2
    injection h2 with h3
    injection h3 with h4
    exact float_ne_ntV t' t h4


/-! ## Premises with a call -/

/-- The `if` premise of a one-premise rule. -/
theorem prem_if {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {e : Exp}
    (h : ∀ pr ∈ [Prem.ifPr e], PremW env D els ρ pr) : EvalExp env ρ e (.bool true) := by
  have h1 := h _ (List.mem_singleton_self _)
  cases h1 with
  | ifPr he => exact he

/-- Membership in a list of bit patterns. -/
theorem memValue_list_true {v : Value} {l : List Value}
    (h : memValue v (.list l) = .ok (.bool true)) :
    v ∈ l := by
  simp only [memValue, Except.ok.injEq, Value.bool.injEq, List.contains_iff_mem] at h
  exact h

/-- An equality premise that holds equates its sides. -/
theorem evalExp_eq_true {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.cmpE .eqOp t e₁ e₂) (.bool true)) :
    ∃ v, EvalExp env ρ e₁ v ∧ EvalExp env ρ e₂ v := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have hb : (v₁ == v₂) = true := by
    simp only [cmpValues, Except.ok.injEq, Value.bool.injEq] at hc
    exact hc
  have hv : v₁ = v₂ := by simpa using hb
  subst hv
  exact ⟨v₁, h₁, h₂⟩

/-- `CONST I32 c` with `c` a variable, inverted. -/
theorem evalExp_constI32_inv {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE x])) v) :
    ∃ c, ρ.findVal? x = some c ∧ v = .case "CONST" (.tuple [ntV .i32, c]) := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨a, xs, rfl, ha, hxs⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, ys, rfl, hb, hys⟩ := Equiv.Validation.evalExps_cons_iff.1 hxs
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hys
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 ha
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hus
  exact ⟨b, evalExp_varE_iff.1 hb, rfl⟩

/-! ## Decoding the left-hand sides -/

/-- `a`'s image is `o (x, y)` with `x`, `y` bound in `ρ`. -/
def OpAt (ρ : VarEnv) (a : Admin) (o : MixopS) (x y : IL.Id) : Prop :=
  ∃ u v, ρ.findVal? x = some u ∧ ρ.findVal? y = some v ∧ adminToV a = .case o (.tuple [u, v])

/-- One `o (x, y)` element of a left-hand side, inverted. -/
theorem opAt_of_eval {env : Env} {ρ : VarEnv} {a : Admin} {o : MixopS} {x y : IL.Id}
    (h : EvalExp env ρ (.caseE o (.tupE [.varE x, .varE y])) (adminToV a)) : OpAt ρ a o x y :=
  let ⟨u, v, hu, hv, he⟩ := evalExp_opVars_inv h
  ⟨u, v, hu, hv, he⟩

/-- A left-hand side of three `o (x, y)` cases, inverted. -/
theorem list3_inv {env : Env} {ρ : VarEnv} {o₁ o₂ o₃ : MixopS} {x₁ y₁ x₂ y₂ x₃ y₃ : IL.Id}
    {is : List Admin}
    (h : EvalExp env ρ (.listE [.caseE o₁ (.tupE [.varE x₁, .varE y₁]),
      .caseE o₂ (.tupE [.varE x₂, .varE y₂]), .caseE o₃ (.tupE [.varE x₃, .varE y₃])])
      (.list (adminsToV is))) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ OpAt ρ a₁ o₁ x₁ y₁ ∧ OpAt ρ a₂ o₂ x₂ y₂ ∧
      OpAt ρ a₃ o₃ x₃ y₃ := by
  obtain ⟨vs, hvs, h3⟩ := evalExp_listE_inv h
  rcases h3 with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, h3⟩⟩⟩
  cases h3
  obtain ⟨a₁, a₂, a₃, rfl, ha₁, ha₂, ha₃⟩ := adminsToV_eq_three (Value.list.inj hvs)
  exact ⟨a₁, a₂, a₃, rfl, opAt_of_eval (ha₁ ▸ e₁), opAt_of_eval (ha₂ ▸ e₂),
    opAt_of_eval (ha₃ ▸ e₃)⟩

/-- A left-hand side of two `o (x, y)` cases, inverted. -/
theorem list2_inv {env : Env} {ρ : VarEnv} {o₁ o₂ : MixopS} {x₁ y₁ x₂ y₂ : IL.Id}
    {is : List Admin}
    (h : EvalExp env ρ (.listE [.caseE o₁ (.tupE [.varE x₁, .varE y₁]),
      .caseE o₂ (.tupE [.varE x₂, .varE y₂])]) (.list (adminsToV is))) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ OpAt ρ a₁ o₁ x₁ y₁ ∧ OpAt ρ a₂ o₂ x₂ y₂ := by
  obtain ⟨vs, hvs, h2⟩ := evalExp_listE_inv h
  rcases h2 with _ | ⟨e₁, _ | ⟨e₂, h2⟩⟩
  cases h2
  obtain ⟨a₁, a₂, rfl, ha₁, ha₂⟩ := adminsToV_eq_two (Value.list.inj hvs)
  exact ⟨a₁, a₂, rfl, opAt_of_eval (ha₁ ▸ e₁), opAt_of_eval (ha₂ ▸ e₂)⟩

/-- An integer constant at the type bound to `nt`. -/
theorem intConst_at {ρ : VarEnv} {a : Admin} {t : IntType} {x : IL.Id}
    (hnt : ρ.findVal? "nt" = some (ntV t)) (h : OpAt ρ a "CONST" "nt" x) :
    ∃ b : BitVec t.width, a = .plain (.intConst t b) ∧ ρ.findVal? x = some (bvV b) := by
  obtain ⟨u, c, hu, hc, ha⟩ := h
  rw [hnt] at hu
  cases hu
  obtain ⟨b, rfl, rfl⟩ := dec_intConst ha
  exact ⟨b, rfl, hc⟩

/-- An integer binary operator sequence, or a float operator. -/
theorem binop_dec {ρ : VarEnv} {a₁ a₂ a₃ : Admin} (h₁ : OpAt ρ a₁ "CONST" "nt" "c_1")
    (h₂ : OpAt ρ a₂ "CONST" "nt" "c_2") (h₃ : OpAt ρ a₃ "BINOP" "nt" "binop") :
    (∃ (t : IntType) (bop : IntBinOp) (x y : BitVec t.width), a₁ = .plain (.intConst t x) ∧
      a₂ = .plain (.intConst t y) ∧ a₃ = .plain (.intBinOp t bop) ∧
      ρ.findVal? "nt" = some (ntV t) ∧ ρ.findVal? "c_1" = some (bvV x) ∧
      ρ.findVal? "c_2" = some (bvV y) ∧ ρ.findVal? "binop" = some (ibinopV bop)) ∨
      (∃ t op, a₃ = .plain (.floatBinOp t op)) := by
  obtain ⟨nt, op, hnt, hop, ha₃⟩ := h₃
  obtain ⟨i₃, rfl, hi₃⟩ := dec_admin_plain ha₃ (by decide)
  rcases dec_binop hi₃ with ⟨t, bop, rfl, hp₃⟩ | ⟨t, bop, rfl⟩
  · have hpe : nt = ntV t ∧ op = ibinopV bop := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hp₃
    rw [hpe.1] at hnt
    rw [hpe.2] at hop
    obtain ⟨x, rfl, hx⟩ := intConst_at hnt h₁
    obtain ⟨y, rfl, hy⟩ := intConst_at hnt h₂
    exact .inl ⟨t, bop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩
  · exact .inr ⟨t, bop, rfl⟩

/-- An integer comparison sequence, or a float comparison. -/
theorem relop_dec {ρ : VarEnv} {a₁ a₂ a₃ : Admin} (h₁ : OpAt ρ a₁ "CONST" "nt" "c_1")
    (h₂ : OpAt ρ a₂ "CONST" "nt" "c_2") (h₃ : OpAt ρ a₃ "RELOP" "nt" "relop") :
    (∃ (t : IntType) (rop : IntRelOp) (x y : BitVec t.width), a₁ = .plain (.intConst t x) ∧
      a₂ = .plain (.intConst t y) ∧ a₃ = .plain (.intRelOp t rop) ∧
      ρ.findVal? "nt" = some (ntV t) ∧ ρ.findVal? "c_1" = some (bvV x) ∧
      ρ.findVal? "c_2" = some (bvV y) ∧ ρ.findVal? "relop" = some (irelopV rop)) ∨
      (∃ t op, a₃ = .plain (.floatRelOp t op)) := by
  obtain ⟨nt, op, hnt, hop, ha₃⟩ := h₃
  obtain ⟨i₃, rfl, hi₃⟩ := dec_admin_plain ha₃ (by decide)
  rcases dec_relop hi₃ with ⟨t, rop, rfl, hp₃⟩ | ⟨t, rop, rfl⟩
  · have hpe : nt = ntV t ∧ op = irelopV rop := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hp₃
    rw [hpe.1] at hnt
    rw [hpe.2] at hop
    obtain ⟨x, rfl, hx⟩ := intConst_at hnt h₁
    obtain ⟨y, rfl, hy⟩ := intConst_at hnt h₂
    exact .inl ⟨t, rop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩
  · exact .inr ⟨t, rop, rfl⟩

/-- An integer unary operator sequence (valid), or a float operator. -/
theorem unop_dec {ρ : VarEnv} {a₁ a₂ : Admin} (h₁ : OpAt ρ a₁ "CONST" "nt" "c_1")
    (h₂ : OpAt ρ a₂ "UNOP" "nt" "unop") :
    (∃ (t : IntType) (uop : IntUnOp) (x : BitVec t.width), uop.valid t = true ∧
      a₁ = .plain (.intConst t x) ∧ a₂ = .plain (.intUnOp t uop) ∧
      ρ.findVal? "nt" = some (ntV t) ∧ ρ.findVal? "c_1" = some (bvV x) ∧
      ρ.findVal? "unop" = some (iunopV uop)) ∨
      (∃ t op, a₂ = .plain (.floatUnOp t op)) := by
  obtain ⟨nt, op, hnt, hop, ha₂⟩ := h₂
  obtain ⟨i₂, rfl, hi₂⟩ := dec_admin_plain ha₂ (by decide)
  rcases dec_unop hi₂ with ⟨t, uop, rfl, hv, hp₂⟩ | ⟨t, uop, rfl⟩
  · have hpe : nt = ntV t ∧ op = iunopV uop := by
      simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hp₂
    rw [hpe.1] at hnt
    rw [hpe.2] at hop
    obtain ⟨x, rfl, hx⟩ := intConst_at hnt h₁
    exact .inl ⟨t, uop, x, hv, rfl, rfl, hnt, hx, hop⟩
  · exact .inr ⟨t, uop, rfl⟩

/-! ## The premises, with the call identified -/

variable {H : Type} {hn : H → String} {B : Builtins} {P : Profile} {host : HostSemantics H}

/-- The right-hand side `[CONST nt c]`, inverted. -/
theorem rhs_const_inv {env : Env} {ρ : VarEnv} {x y : IL.Id} {w : Value}
    (h : EvalExp env ρ (.listE [.caseE "CONST" (.tupE [.varE x, .varE y])]) w) :
    ∃ u v, ρ.findVal? x = some u ∧ ρ.findVal? y = some v ∧
      w = .list [.case "CONST" (.tuple [u, v])] := by
  obtain ⟨ws, rfl, h1⟩ := evalExp_listE_inv h
  rcases h1 with _ | ⟨e, h1⟩
  cases h1
  obtain ⟨u, v, hu, hv, rfl⟩ := evalExp_opVars_inv e
  exact ⟨u, v, hu, hv, rfl⟩

/-- The right-hand side `[CONST I32 c]`, inverted. -/
theorem rhs_constI32_inv {env : Env} {ρ : VarEnv} {w : Value}
    (h : EvalExp env ρ (.listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c"])]) w) :
    ∃ c, ρ.findVal? "c" = some c ∧ w = .list [.case "CONST" (.tuple [ntV .i32, c])] := by
  obtain ⟨ws, rfl, h1⟩ := evalExp_listE_inv h
  rcases h1 with _ | ⟨e, h1⟩
  cases h1
  obtain ⟨c, hc, rfl⟩ := evalExp_constI32_inv e
  exact ⟨c, hc, rfl⟩

/-- The right-hand side `[TRAP]`, inverted. -/
theorem rhs_trap_inv {env : Env} {ρ : VarEnv} {w : Value}
    (h : EvalExp env ρ (.listE [.caseE "TRAP" (.tupE [])]) w) :
    w = .list [.case "TRAP" (.tuple [])] := by
  obtain ⟨ws, rfl, h1⟩ := evalExp_listE_inv h
  rcases h1 with _ | ⟨e, h1⟩
  cases h1
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 e
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  rw [Equiv.Validation.evalExps_nil_iff.1 hus]

/-- `binop-val`'s premise and right-hand side, at an integer operator. -/
theorem binopVal_finish (hB : IntB B) {σ : List (IL.Id × Value)} {t : IntType} {bop : IntBinOp}
    {x y : BitVec t.width} {w : Value} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (ntV t))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (bvV x))
    (hy : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (bvV y))
    (hop : (VarEnv.empty.bindVals σ).findVal? "binop" = some (ibinopV bop))
    (hr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])]) w)
    (hp : ∀ pr ∈ [Prem.ifPr (.memE (.varE "c") (.callE "binop_" [.expA (.varE "nt"),
      .expA (.varE "binop"), .expA (.varE "c_1"), .expA (.varE "c_2")]))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    ∃ z, intBinOp t bop x y = .ok z ∧ w = .list (adminsToV [.plain (.intConst t z)]) := by
  obtain ⟨u, c, hu, hc, rfl⟩ := rhs_const_inv hr
  rw [hnt] at hu
  cases hu
  obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 (prem_if hp)
  have hv₁' : v₁ = c := by simpa [hc] using (evalExp_varE_iff.1 hv₁).symm
  have happ : Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV bop), .val (bvV x),
      .val (bvV y)] v₂ :=
    (applies_iff_callDef rfl (evalArgs_four hnt hop hx hy)).2 (evalExp_callE_iff.1 hv₂)
  have hv₂eq : v₂ = .list ((ibinop_ t.width bop x y).toList.map bvV) :=
    happ.unique (applies_binop_int hB t bop x y)
  rw [hv₂eq, hv₁'] at hmem
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (memValue_list_true hmem)
  have hz' : (intBinOp t bop x y).toOption = some z := by
    rw [← ibinop_agree]; exact Option.mem_toList.1 hz
  have hok : intBinOp t bop x y = .ok z := by
    cases hres : intBinOp t bop x y <;> simp_all [Except.toOption]
  exact ⟨z, hok, rfl⟩

/-- **`Step_pure/binop-val` (48), backward.** At the image of a Core sequence, the rule derives
the image of a Core `intBinOp` step, unless the operator is a float operator (the float
family's case). -/
theorem bwd_binopVal (hB : IntB B) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 48 (.tuple [.list (adminsToV is), w])) :
    (∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩) ∨
      (∃ t op, Admin.plain (.floatBinOp t op) ∈ is) := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).binopVal hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := list3_inv hl
  rcases binop_dec h₁ h₂ h₃ with ⟨t, bop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩ |
    ⟨t, bop, rfl⟩
  · obtain ⟨z, hz, rfl⟩ := binopVal_finish hB hnt hx hy hop hr hp
    exact .inl ⟨_, rfl, .numeric (.intBinOp hz)⟩
  · exact .inr ⟨t, bop, by simp⟩

/-- `binop-trap`'s premise, at an integer operator. -/
theorem binopTrap_finish (hB : IntB B) {σ : List (IL.Id × Value)} {t : IntType}
    {bop : IntBinOp} {x y : BitVec t.width} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (ntV t))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (bvV x))
    (hy : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (bvV y))
    (hop : (VarEnv.empty.bindVals σ).findVal? "binop" = some (ibinopV bop))
    (hp : ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.callE "binop_" [.expA (.varE "nt"),
      .expA (.varE "binop"), .expA (.varE "c_1"), .expA (.varE "c_2")]) (.listE []))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    ∃ e, intBinOp t bop x y = .error e := by
  obtain ⟨v, hv₁, hv₂⟩ := evalExp_eq_true (prem_if hp)
  have happ : Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV bop), .val (bvV x),
      .val (bvV y)] v :=
    (applies_iff_callDef rfl (evalArgs_four hnt hop hx hy)).2 (evalExp_callE_iff.1 hv₁)
  have hveq : v = .list ((ibinop_ t.width bop x y).toList.map bvV) :=
    happ.unique (applies_binop_int hB t bop x y)
  have hnil : v = .list [] := by
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    rw [Equiv.Validation.evalExps_nil_iff.1 hvs]
  have hnone : (intBinOp t bop x y).toOption = none := by
    rw [← ibinop_agree]
    cases h : ibinop_ t.width bop x y <;> simp_all
  cases hres : intBinOp t bop x y <;> simp_all [Except.toOption]

/-- **`Step_pure/binop-trap` (49), backward.** -/
theorem bwd_binopTrap (hB : IntB B) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 49 (.tuple [.list (adminsToV is), w])) :
    (∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩) ∨
      (∃ t op, Admin.plain (.floatBinOp t op) ∈ is) := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).binopTrap hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := list3_inv hl
  rcases binop_dec h₁ h₂ h₃ with ⟨t, bop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩ |
    ⟨t, bop, rfl⟩
  · obtain ⟨e, he⟩ := binopTrap_finish hB hnt hx hy hop hp
    exact .inl ⟨[.trap], rhs_trap_inv hr, .numeric (.intBinOpTrap he)⟩
  · exact .inr ⟨t, bop, by simp⟩

/-- `unop-val`'s premise and right-hand side, at a valid integer operator. -/
theorem unopVal_finish (hB : IntB B) {σ : List (IL.Id × Value)} {t : IntType} {uop : IntUnOp}
    (hv : uop.valid t = true) {x : BitVec t.width} {w : Value} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (ntV t))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (bvV x))
    (hop : (VarEnv.empty.bindVals σ).findVal? "unop" = some (iunopV uop))
    (hr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])]) w)
    (hp : ∀ pr ∈ [Prem.ifPr (.memE (.varE "c") (.callE "unop_" [.expA (.varE "nt"),
      .expA (.varE "unop"), .expA (.varE "c_1")]))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    w = .list (adminsToV [.plain (.intConst t (Numerics.intUnOp t uop x))]) := by
  obtain ⟨u, c, hu, hc, rfl⟩ := rhs_const_inv hr
  rw [hnt] at hu
  cases hu
  obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 (prem_if hp)
  have hv₁' : v₁ = c := by simpa [hc] using (evalExp_varE_iff.1 hv₁).symm
  have happ : Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV uop), .val (bvV x)] v₂ :=
    (applies_iff_callDef rfl (evalArgs_three hnt hop hx)).2 (evalExp_callE_iff.1 hv₂)
  have hv₂eq : v₂ = .list [bvV (iunop_ t.width uop x)] :=
    happ.unique (applies_unop_int hB t uop hv x)
  rw [hv₂eq, hv₁'] at hmem
  have hc' : c = bvV (iunop_ t.width uop x) := by
    simpa using memValue_list_true hmem
  rw [hc', iunop_agree]
  rfl

/-- **`Step_pure/unop-val` (46), backward.** -/
theorem bwd_unopVal (hB : IntB B) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 46 (.tuple [.list (adminsToV is), w])) :
    (∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩) ∨
      (∃ t op, Admin.plain (.floatUnOp t op) ∈ is) := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).unopVal hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := list2_inv hl
  rcases unop_dec h₁ h₂ with ⟨t, uop, x, hv, rfl, rfl, hnt, hx, hop⟩ | ⟨t, uop, rfl⟩
  · exact .inl ⟨_, unopVal_finish hB hv hnt hx hop hr hp, .numeric .intUnOp⟩
  · exact .inr ⟨t, uop, by simp⟩

/-- `unop-trap`'s premise never holds at a valid integer operator. -/
theorem unopTrap_finish (hB : IntB B) {σ : List (IL.Id × Value)} {t : IntType} {uop : IntUnOp}
    (hv : uop.valid t = true) {x : BitVec t.width} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (ntV t))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (bvV x))
    (hop : (VarEnv.empty.bindVals σ).findVal? "unop" = some (iunopV uop))
    (hp : ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.callE "unop_" [.expA (.varE "nt"),
      .expA (.varE "unop"), .expA (.varE "c_1")]) (.listE []))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := evalExp_eq_true (prem_if hp)
  have happ : Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV uop), .val (bvV x)] v :=
    (applies_iff_callDef rfl (evalArgs_three hnt hop hx)).2 (evalExp_callE_iff.1 hv₁)
  have hveq : v = .list [bvV (iunop_ t.width uop x)] :=
    happ.unique (applies_unop_int hB t uop hv x)
  obtain ⟨vs, hvs, hv'⟩ := evalExp_listE_iff.1 hv₂
  rw [Equiv.Validation.evalExps_nil_iff.1 hvs, hveq] at hv'
  cases hv'

/-- **`Step_pure/unop-trap` (47), backward.** It never fires on an integer operator: `$unop_` is
total there (one result). -/
theorem bwd_unopTrap (hB : IntB B) {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 47 (.tuple [.list (adminsToV is), w])) :
    ∃ t op, Admin.plain (.floatUnOp t op) ∈ is := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).unopTrap hf
  obtain ⟨hl, -⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := list2_inv hl
  rcases unop_dec h₁ h₂ with ⟨t, uop, x, hv, rfl, rfl, hnt, hx, hop⟩ | ⟨t, uop, rfl⟩
  · exact (unopTrap_finish hB hv hnt hx hop hp).elim
  · exact ⟨t, uop, by simp⟩

/-- `testop`/`relop`'s premise `c = $op(…)` and right-hand side. -/
theorem cmp_finish {σ : List (IL.Id × Value)} {x : IL.Id} {args : List Arg} {r w : Value}
    {els : Prop}
    (happ : ∀ v, EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.callE x args) v → v = r)
    (hr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c"])]) w)
    (hp : ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE x args))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    w = .list [.case "CONST" (.tuple [ntV .i32, r])] := by
  obtain ⟨c, hc, rfl⟩ := rhs_constI32_inv hr
  obtain ⟨v, hv₁, hv₂⟩ := evalExp_eq_true (prem_if hp)
  have hvc : v = c := by simpa [hc] using (evalExp_varE_iff.1 hv₁).symm
  rw [← hvc, happ v hv₂]

/-- **`Step_pure/testop` (50), backward.** Only integer types have a test. -/
theorem bwd_testop {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 50 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).testop hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, rfl, h₁, ⟨nt, op, hnt, hop, ha₂⟩⟩ := list2_inv hl
  obtain ⟨i₂, rfl, hi₂⟩ := dec_admin_plain ha₂ (by decide)
  obtain ⟨t, top, rfl, hp₂⟩ := dec_testop hi₂
  have hpe : nt = ntV t ∧ op = itestopV top := by
    simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hp₂
  rw [hpe.1] at hnt
  rw [hpe.2] at hop
  obtain ⟨x, rfl, hx⟩ := intConst_at hnt h₁
  have hw := cmp_finish (r := bvV (itestop_ t.width top x)) (fun v hv =>
    ((applies_iff_callDef rfl (evalArgs_three hnt hop hx)).2 (evalExp_callE_iff.1 hv)).unique
      (applies_testop_int t top x)) hr hp
  rw [itestop_agree] at hw
  exact ⟨[constI32 (Numerics.intTestOp t top x)], hw, .numeric .intTestOp⟩

/-- **`Step_pure/relop` (51), backward.** -/
theorem bwd_relop {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 51 (.tuple [.list (adminsToV is), w])) :
    (∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩) ∨
      (∃ t op, Admin.plain (.floatRelOp t op) ∈ is) := by
  obtain ⟨σ, -, he, hp⟩ := fires_body (hasNumericRules_simEnv B).relop hf
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := list3_inv hl
  rcases relop_dec h₁ h₂ h₃ with ⟨t, rop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩ |
    ⟨t, rop, rfl⟩
  · have hw := cmp_finish (r := bvV (irelop_ t.width rop x y)) (fun v hv =>
      ((applies_iff_callDef rfl (evalArgs_four hnt hop hx hy)).2
        (evalExp_callE_iff.1 hv)).unique (applies_relop_int t rop x y)) hr hp
    rw [irelop_agree] at hw
    exact .inl ⟨[constI32 (Numerics.intRelOp t rop x y)], hw, .numeric .intRelOp⟩
  · exact .inr ⟨t, rop, by simp⟩

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
