module

public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms

/-!
# Decoders and rule inversion

Decoders of `adminToV` at the tags of the reference instructions (`head_*`, by the typing track's
`admin_head_inv`), the decoder of a `ref`-typed image (`ref_of_typed`: the IL type `ref`'s cases
are the images of Core's references), and the inversion of a firing `Step_pure` rule whose
left-hand side is a two- or three-element list (`fires_two`, `fires_three`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Typing (adminHead instrHead refHead adminToV_case)

/-! ## Heads -/

theorem head_refIsNull {a : Admin} (h : adminHead a = "REF.IS_NULL") : a = .plain .refIsNull := by
  revert h
  admin_head_inv

theorem head_refAsNonNull {a : Admin} (h : adminHead a = "REF.AS_NON_NULL") :
    a = .plain .refAsNonNull := by
  revert h
  admin_head_inv

theorem head_refEq {a : Admin} (h : adminHead a = "REF.EQ") : a = .plain .refEq := by
  revert h
  admin_head_inv

theorem head_refI31 {a : Admin} (h : adminHead a = "REF.I31") : a = .plain .refI31 := by
  revert h
  admin_head_inv

theorem head_i31Get {a : Admin} (h : adminHead a = "I31.GET") : ∃ sx, a = .plain (.i31Get sx) := by
  revert h
  admin_head_inv

theorem head_externConvertAny {a : Admin} (h : adminHead a = "EXTERN.CONVERT_ANY") :
    a = .plain .externConvertAny := by
  revert h
  admin_head_inv

theorem head_anyConvertExtern {a : Admin} (h : adminHead a = "ANY.CONVERT_EXTERN") :
    a = .plain .anyConvertExtern := by
  revert h
  admin_head_inv

theorem head_refI31Num {a : Admin} (h : adminHead a = "REF.I31_NUM") : ∃ b, a = .ref (.i31 b) := by
  revert h
  admin_head_inv

theorem head_refExtern {a : Admin} (h : adminHead a = "REF.EXTERN") :
    ∃ r, a = .ref (.extern r) := by
  revert h
  admin_head_inv

theorem head_structSet {a : Admin} (h : adminHead a = "STRUCT.SET") :
    ∃ x i, a = .plain (.structSet x i) := by
  revert h
  admin_head_inv

theorem head_arraySet {a : Admin} (h : adminHead a = "ARRAY.SET") : ∃ x, a = .plain (.arraySet x) := by
  revert h
  admin_head_inv

theorem head_arrayNew {a : Admin} (h : adminHead a = "ARRAY.NEW") : ∃ x, a = .plain (.arrayNew x) := by
  revert h
  admin_head_inv

theorem head_refArray {a : Admin} (h : adminHead a = "REF.ARRAY_ADDR") :
    ∃ n, a = .ref (.array n) := by
  revert h
  admin_head_inv

/-- The heads of the IL type `ref`'s cases. -/
def refHeads : List MixopS :=
  ["REF.I31_NUM", "REF.NULL_ADDR", "REF.STRUCT_ADDR", "REF.ARRAY_ADDR", "REF.FUNC_ADDR",
    "REF.EXN_ADDR", "REF.HOST_ADDR", "REF.EXTERN"]

/-- An administrative instruction with a reference head is a reference. -/
theorem head_ref {a : Admin} (h : adminHead a ∈ refHeads) : ∃ r : Ref, a = .ref r := by
  revert h
  cases a with
  | plain i => cases i <;> simp [adminHead, instrHead, refHeads]
  | ref r => intro _; exact ⟨r, rfl⟩
  | _ => simp [adminHead, refHeads]

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem refCases_heads :
    (IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d268 0 0).map
      (fun c : TypCase => match c with | .mk o _ _ _ => o) = refHeads := rfl

/-- A typed `ref` is a `case` with one of `ref`'s heads. -/
theorem head_of_typed_ref {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "ref" []) v) : ∃ op w, v = .case op w ∧ op ∈ refHeads := by
  have hl : localTyp? ρ "ref" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [Typing.findTyp_ref] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    have hmem := List.mem_map_of_mem (f := fun c : TypCase => match c with | .mk o _ _ _ => o) hm
    rw [refCases_heads] at hmem
    exact ⟨op, w, rfl, hmem⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- **An administrative instruction whose image is a typed `ref` is a reference.** -/
theorem ref_of_typed {ρ : VarEnv} (hρ : ValsOnly ρ) {a : Admin}
    (h : HasTyp (simEnv B) ρ (.varT "ref" []) (adminToV a)) : ∃ r : Ref, a = .ref r := by
  obtain ⟨op, w, hw, hop⟩ := head_of_typed_ref hρ h
  exact head_ref ((adminToV_case hw) ▸ hop)

/-! ## Inverting a firing rule -/

/-- The image of a three-instruction sequence. -/
theorem adminsToV_eq_triple {is : List Admin} {v₁ v₂ v₃ : Value}
    (h : adminsToV is = [v₁, v₂, v₃]) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ adminToV a₁ = v₁ ∧ adminToV a₂ = v₂ ∧ adminToV a₃ = v₃ := by
  match is, h with
  | [a₁, a₂, a₃], h =>
      simp only [adminsToV, List.cons.injEq] at h
      exact ⟨a₁, a₂, a₃, rfl, h.1, h.2.1, h.2.2.1⟩
  | [], h => simp [adminsToV] at h
  | [_], h => simp [adminsToV] at h
  | [_, _], h => simp [adminsToV] at h
  | _ :: _ :: _ :: _ :: _, h => simp [adminsToV] at h

/-- The premises of a firing `Step_pure` rule, in its scope. -/
abbrev PremsAt (env : Env) (k : Nat) (v : Value) (ρ : VarEnv) (prems : List Prem) : Prop :=
  ∀ pr ∈ prems, PremW env (DDerives env (otherwise env)) (otherwise env "Step_pure" [] k v) ρ pr

/-- **A firing two-instruction `Step_pure` rule, inverted**: the code is two instructions whose
images are the left-hand side's elements, in the rule's scope. -/
theorem fires_two {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {e₁ e₂ rh : Exp}
    {prems : List Prem} {is : List Admin} {w : Value}
    (h : HasRuleAt env "Step_pure" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.listE [e₁, e₂], rh]) prems))
    (hf : Fires env "Step_pure" k (.tuple [.list (adminsToV is), w])) :
    ∃ σ a₁ a₂, is = [a₁, a₂] ∧ QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e₁ (adminToV a₁) ∧
      EvalExp env (VarEnv.empty.bindVals σ) e₂ (adminToV a₂) ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      PremsAt env k (.tuple [.list (adminsToV is), w]) (VarEnv.empty.bindVals σ) prems := by
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq h hf
  have hl := RefsGC.lhs_of_concl he
  have hr := RefsGC.rhs_of_concl he
  obtain ⟨u₁, u₂, h₁, h₂, hu⟩ := State.evalExp_listE_two_inv hl
  obtain ⟨a₁, a₂, rfl, ha₁, ha₂⟩ := adminsToV_eq_pair (Value.list.inj hu)
  exact ⟨σ, a₁, a₂, rfl, hq, ha₁ ▸ h₁, ha₂ ▸ h₂, hr, hp⟩

/-- **A firing three-instruction `Step_pure` rule, inverted.** -/
theorem fires_three {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {e₁ e₂ e₃ rh : Exp}
    {prems : List Prem} {is : List Admin} {w : Value}
    (h : HasRuleAt env "Step_pure" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.listE [e₁, e₂, e₃], rh]) prems))
    (hf : Fires env "Step_pure" k (.tuple [.list (adminsToV is), w])) :
    ∃ σ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e₁ (adminToV a₁) ∧
      EvalExp env (VarEnv.empty.bindVals σ) e₂ (adminToV a₂) ∧
      EvalExp env (VarEnv.empty.bindVals σ) e₃ (adminToV a₃) ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      PremsAt env k (.tuple [.list (adminsToV is), w]) (VarEnv.empty.bindVals σ) prems := by
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq h hf
  have hl := RefsGC.lhs_of_concl he
  have hr := RefsGC.rhs_of_concl he
  obtain ⟨u₁, u₂, u₃, h₁, h₂, h₃, hu⟩ := State.evalExp_listE_three_inv hl
  obtain ⟨a₁, a₂, a₃, rfl, ha₁, ha₂, ha₃⟩ := adminsToV_eq_triple (Value.list.inj hu)
  exact ⟨σ, a₁, a₂, a₃, rfl, hq, ha₁ ▸ h₁, ha₂ ▸ h₂, ha₃ ▸ h₃, hr, hp⟩

/-- A `case` element of a left-hand side gives the instruction's head. -/
theorem head_of_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE op e) (adminToV a)) : adminHead a = op := by
  obtain ⟨u, -, hu⟩ := evalExp_caseE_iff.1 h
  exact (adminToV_case hu).symm

/-- A `case` element of a left-hand side, with its payload. -/
theorem payload_of_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE op e) (adminToV a)) :
    ∃ u, EvalExp env ρ e u ∧ adminToV a = .case op u := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  exact ⟨u, hu, he⟩

/-- A `ref`-typed variable of the left-hand side is a reference. -/
theorem ref_of_var {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {a : Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "ref" []) ∈ qs)
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.subE (.varE x) (.varT "ref" []) (.varT "instr" [])) (adminToV a)) :
    ∃ r : Ref, a = .ref r ∧ (VarEnv.empty.bindVals σ).findVal? x = some (refToValue r) := by
  obtain ⟨R, fR, tR⟩ := hq x _ hm
  have e : adminToV a = R := EvalExp.unique (evalExp_subE_iff.1 h) (evalExp_var fR)
  obtain ⟨r, rfl⟩ := ref_of_typed (valsOnly_bindVals σ) (e ▸ tR)
  rw [← e] at fR
  exact ⟨r, rfl, fR⟩



/-- A `CONST I32 e` element of a left-hand side is an `i32` constant, `e` its payload. -/
theorem const32_of_lhs {env : Env} {ρ : VarEnv} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), e])) (adminToV a)) :
    ∃ c : BitVec 32, a = constI32 c ∧ EvalExp env ρ e (Silmaril.SpecTec.Equiv.Execution.pctV c.toNat) := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := State.evalExp_tup2_inv hu
  have e₁ : u₁ = Silmaril.SpecTec.Equiv.Execution.caseNilV "I32" := by
    obtain ⟨z, hz, rfl⟩ := evalExp_caseE_iff.1 hu₁
    obtain ⟨zs, hzs, rfl⟩ := evalExp_tupE_iff.1 hz
    rw [Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hzs]
    rfl
  subst e₁
  obtain ⟨c, rfl⟩ := (Typing.ctrlDecode_simEnv ⟨fun _ _ => none⟩).constI32 a u₂ he
  have he' : Value.case "CONST" (.tuple [Silmaril.SpecTec.Equiv.Execution.caseNilV "I32",
      Silmaril.SpecTec.Equiv.Execution.pctV c.toNat]) =
      .case "CONST" (.tuple [Silmaril.SpecTec.Equiv.Execution.caseNilV "I32", u₂]) := he
  have e₂ : u₂ = Silmaril.SpecTec.Equiv.Execution.pctV c.toNat := by
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
    exact he'.symm
  subst e₂
  exact ⟨c, rfl, hu₂⟩

/-! ## Code lists, element by element -/

/-- The empty code list. -/
theorem evalExps_admins_nil {env : Env} {ρ : VarEnv} {is : List Admin}
    (h : EvalExps env ρ [] (adminsToV is)) : is = [] := by
  have e := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 h
  cases is with
  | nil => rfl
  | cons a l => simp [adminsToV] at e

/-- A non-empty code list. -/
theorem evalExps_admins_cons {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp} {is : List Admin}
    (h : EvalExps env ρ (e :: es) (adminsToV is)) :
    ∃ a is', is = a :: is' ∧ EvalExp env ρ e (adminToV a) ∧ EvalExps env ρ es (adminsToV is') := by
  obtain ⟨w, ws, hw, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  cases is with
  | nil => simp [adminsToV] at he
  | cons a l =>
      simp only [adminsToV, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨a, l, rfl, hw, hws⟩


/-- A one-instruction code list. -/
theorem codes_one {env : Env} {ρ : VarEnv} {e₁ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁] (adminsToV is)) : ∃ a₁, is = [a₁] ∧ EvalExp env ρ e₁ (adminToV a₁) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := evalExps_admins_cons h
  obtain rfl := evalExps_admins_nil h
  exact ⟨a₁, rfl, h₁⟩

/-- A two-instruction code list. -/
theorem codes_two {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂] (adminsToV is)) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧ EvalExp env ρ e₂ (adminToV a₂) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := evalExps_admins_cons h
  obtain ⟨a₂, is, rfl, h₂, h⟩ := evalExps_admins_cons h
  obtain rfl := evalExps_admins_nil h
  exact ⟨a₁, a₂, rfl, h₁, h₂⟩

/-- A three-instruction code list. -/
theorem codes_three {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂, e₃] (adminsToV is)) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) ∧ EvalExp env ρ e₃ (adminToV a₃) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := evalExps_admins_cons h
  obtain ⟨a₂, a₃, rfl, h₂, h₃⟩ := codes_two h
  exact ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩

/-- A four-instruction code list. -/
theorem codes_four {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂, e₃, e₄] (adminsToV is)) :
    ∃ a₁ a₂ a₃ a₄, is = [a₁, a₂, a₃, a₄] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) ∧ EvalExp env ρ e₃ (adminToV a₃) ∧
      EvalExp env ρ e₄ (adminToV a₄) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := evalExps_admins_cons h
  obtain ⟨a₂, a₃, a₄, rfl, h₂, h₃, h₄⟩ := codes_three h
  exact ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩

/-- An instruction `op x` of the left-hand side: `x`'s value is the image's payload. -/
theorem payload_var {env : Env} {ρ : VarEnv} {op : MixopS} {x : IL.Id} {a : Admin}
    (h : EvalExp env ρ (.caseE op (.varE x)) (adminToV a)) :
    ∃ u, ρ.findVal? x = some u ∧ adminToV a = .case op u := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  exact ⟨u, evalExp_varE_iff.1 hu, he⟩

/-- An index instruction `op x` of the left-hand side, `op` one of the instructions whose image
is `.case op (% x)`: `x` is bound to the `%`-wrapped index. -/
theorem idx_of_var {env : Env} {ρ : VarEnv} {op : MixopS} {a : Admin} {k : Nat}
    (h : EvalExp env ρ (.caseE op (.varE "x")) (adminToV a))
    (ha : adminToV a = .case op (.case "%" (.tuple [.num (.natN k)]))) :
    ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])) := by
  obtain ⟨u, fu, he⟩ := payload_var h
  have e : u = .case "%" (.tuple [.num (.natN k)]) := (Value.case.inj (he.symm.trans ha)).2
  exact e ▸ fu

/-- An instruction `op y` of the left-hand side whose image is `.case op u`: `y` is bound to
`u`. -/
theorem idx_of_var' {env : Env} {ρ : VarEnv} {op : MixopS} {y : IL.Id} {a : Admin} {u : Value}
    (h : EvalExp env ρ (.caseE op (.varE y)) (adminToV a)) (ha : adminToV a = .case op u) :
    ρ.findVal? y = some u := by
  obtain ⟨u', fu, he⟩ := payload_var h
  have e : u' = u := (Value.case.inj (he.symm.trans ha)).2
  exact e ▸ fu

/-- A right-hand side `e; ε`. -/
theorem rhs_nil {env : Env} {ρ : VarEnv} {e : Exp} {w : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [e, .listE []])) w) :
    ∃ W, EvalExp env ρ e W ∧ w = .case "%;%" (.tuple [W, .list []]) := by
  obtain ⟨W, hW, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨W₁, W₂, hW₁, hW₂, rfl⟩ := State.evalExp_tup2_inv hW
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hW₂
  obtain rfl := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hvs
  exact ⟨W₁, hW₁, rfl⟩

/-- The body of a one-clause updater `$u(z, …) = z'; f'`, at a call: both components. -/
theorem body_pair {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {W : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [e₁, e₂])) W) :
    ∃ W₁ W₂, EvalExp env ρ e₁ W₁ ∧ EvalExp env ρ e₂ W₂ ∧ W = .case "%;%" (.tuple [W₁, W₂]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨W₁, W₂, h₁, h₂, rfl⟩ := State.evalExp_tup2_inv hu
  exact ⟨W₁, W₂, h₁, h₂, rfl⟩

/-- **A firing `Step` rule `z; instr* ~> …`, inverted**: the state is `z`'s value, the code
evaluates element by element. -/
theorem fires_step {H : Type} {hn : H → String} {env : Env} {k : Nat} {nm : IL.Id}
    {qs : List Param} {es : List Exp} {rh : Exp} {prems : List Prem} {c : Config H} {w : Value}
    (h : HasRuleAt env "Step" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires env "Step" k (.tuple [configV hn c, w])) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps env (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env))
        (otherwise env "Step" [] k (.tuple [configV hn c, w])) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq h hf
  have hl := RefsGC.lhs_of_concl he
  have hr := RefsGC.rhs_of_concl he
  obtain ⟨hz, hc⟩ := RefsGC.cfgz_inv (z := stateV hn c.store c.frame) (l := adminsToV c.code) hl
  exact ⟨σ, hq, evalExp_varE_iff.1 hz, RefsGC.elems_of_list hc, hr, hp⟩

/-- A `val`-typed variable of the left-hand side is a value. -/
theorem val_of_var {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {a : Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "val" []) ∈ qs)
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.subE (.varE x) (.varT "val" []) (.varT "instr" [])) (adminToV a)) :
    ∃ v : Val, a = v.toAdmin ∧ (VarEnv.empty.bindVals σ).findVal? x = some (valV v) := by
  obtain ⟨R, fR, tR⟩ := hq x _ hm
  have e : adminToV a = R := EvalExp.unique (evalExp_subE_iff.1 h) (evalExp_var fR)
  obtain ⟨v, rfl⟩ := (Typing.stateDecode_simEnv B).val a _ (valsOnly_bindVals σ) (e ▸ tR)
  exact ⟨v, rfl, by rw [← RefsGC.adminToV_toAdmin, e]; exact fR⟩

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
