module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumCvt
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureNumericV2

/-!
# The live numeric rules of `Step_pure`, backwards, at arbitrary code

`unop-val` (20), `binop-val` (22), `testop` (24), `relop` (25) and `cvtop-val` (26) of wasm-2.0
`Step_pure`, at the image of any V2 code, under builtins `B` that interpret the integer (`IntB`)
and float (`FloatB P`) primitives. The rule's shared `nt` forces the constant and the operator to
the same number type (`nt_eq`), so ill-typed pairs never fire.

`unop-val` is proved at **every** integer operator (`applies_unop_int20`), including `EXTEND n`
with `n` at least the width, which V2 validation rejects but which is IL-typed. `cvtop-val` needs
the conversion to be one V2 defines (`CvtOp.toShared … isSome`): the 2.0 script's `$cvtop__`
has generic clauses (`EXTEND` and `WRAP` at any pair of integer types, `PROMOTE`/`DEMOTE` at any
pair of float types), so at other pairs it can produce a value where V2 only traps
(`WholeCvtEdge`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB)

variable {B : Builtins}

/-! ## Shared number types -/

/-- The payload of a `case` element of a left-hand side, component by component. -/
theorem tup_of_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {es : List Exp} {a : Admin}
    {us : List Value} (h : EvalExp env ρ (.caseE op (.tupE es)) (adminToV a))
    (ha : adminToV a = .case op (.tuple us)) : EvalExps env ρ es us := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  have e : u = .tuple us := (Value.case.inj (he.symm.trans ha)).2
  subst e
  exact Sim.RefsGC.elems_of_tup hu

/-- The first component of a payload `(x, …)` is `x`'s value. -/
theorem var_fst {env : Env} {ρ : VarEnv} {x : IL.Id} {es : List Exp} {u : Value}
    {us : List Value} (h : EvalExps env ρ (.varE x :: es) (u :: us)) : ρ.findVal? x = some u := by
  obtain ⟨w, ws, hw, -, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  obtain ⟨rfl, -⟩ := List.cons.inj he
  exact evalExp_varE_iff.1 hw

/-- The second component of a payload `(_, x, …)` is `x`'s value. -/
theorem var_snd {env : Env} {ρ : VarEnv} {e : Exp} {x : IL.Id} {es : List Exp} {u₀ u : Value}
    {us : List Value} (h : EvalExps env ρ (e :: .varE x :: es) (u₀ :: u :: us)) :
    ρ.findVal? x = some u := by
  obtain ⟨w, ws, -, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  obtain ⟨-, rfl⟩ := List.cons.inj he
  exact var_fst hws

/-- Two elements whose payloads start with the same variable share that component. -/
theorem nt_eq {env : Env} {ρ : VarEnv} {op₁ op₂ : MixopS} {e₁ e₂ : Exp} {a₁ a₂ : Admin}
    {n₁ n₂ u₁ u₂ : Value}
    (h₁ : EvalExp env ρ (.caseE op₁ (.tupE [.varE "nt", e₁])) (adminToV a₁))
    (ha₁ : adminToV a₁ = .case op₁ (.tuple [n₁, u₁]))
    (h₂ : EvalExp env ρ (.caseE op₂ (.tupE [.varE "nt", e₂])) (adminToV a₂))
    (ha₂ : adminToV a₂ = .case op₂ (.tuple [n₂, u₂])) : n₁ = n₂ :=
  Option.some.inj ((var_fst (tup_of_caseE h₁ ha₁)).symm.trans (var_fst (tup_of_caseE h₂ ha₂)))

/-- `numTypeV` is injective. -/
theorem numTypeV_inj {t t' : NumType} (h : numTypeV t = numTypeV t') : t = t' := by
  rcases t with ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases t' with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    first | rfl | simp [numTypeV, caseNilV] at h

/-- A `CONST` image is a number. -/
theorem num_of_const {a : Admin} (h : adminHead20 a = "CONST") :
    ∃ (t : NumType) (x : BitVec t.width), a = (Val.num ⟨t, x⟩).toAdmin := by
  rcases head20_const h with ⟨t, x, rfl⟩ | ⟨t, x, rfl⟩
  · exact ⟨.int t, x, rfl⟩
  · exact ⟨.float t, x, rfl⟩

/-- The image of a number. -/
theorem adminToV_numAdmin (t : NumType) (x : BitVec t.width) :
    adminToV (Val.num ⟨t, x⟩).toAdmin = .case "CONST" (.tuple [numTypeV t, numV ⟨t, x⟩]) := by
  rcases t with ⟨_ | _⟩ | ⟨_ | _⟩ <;> rfl

/-! ## The rules -/

variable {P : Profile}

/-- `Step_pure/unop-val` at any code, at every operator. -/
theorem bwdPure_unop (hI : IntB B) (hF : FloatB P B) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 20 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨σ, -, hes⟩ := fires_list20 (Pure.hasRuleAt_unopVal B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  have hB := firesB_pure hf
  obtain ⟨t, x, rfl⟩ := num_of_const (head20_of_caseE h₁)
  have hn : ∀ n₂ u₂, adminToV a₂ = .case "UNOP" (.tuple [n₂, u₂]) → numTypeV t = n₂ :=
    fun _ _ h => nt_eq h₁ (adminToV_numAdmin t x) h₂ h
  rcases head20_unop (head20_of_caseE h₂) with ⟨t', op, rfl⟩ | ⟨t', op, rfl⟩
  · obtain rfl := numTypeV_inj (hn _ _ rfl)
    obtain ⟨c, v, hw, happ, hm⟩ := Pure.unopVal_inv B hB
    have hv := Applies.unique happ (Pure.applies_unop_int20 hI hF t' op x)
    subst hv
    have hc := List.mem_singleton.1 (Pure.memValue_list_iff.1 hm)
    subst hc
    exact pureBwd_of (code' := [.plain (.intConst t' (Numerics.intUnOp t' op x))]) hw (.intUnOp rfl)
  · obtain rfl := numTypeV_inj (hn _ _ rfl)
    obtain ⟨z, hz, hw⟩ := (Pure.floatUnOp_iff B (Pure.numAgree_simEnv20 hI hF)
      (Pure.numTyped_simEnv20 B)).1 hB
    exact pureBwd_of hw (.floatUnOp hz)

/-- The three elements of a two-operand numeric left-hand side, read back. -/
theorem num2_lhs {i : Nat} {nm : IL.Id} {qs : List Param} {o₁ o₂ e₃ rh : Exp} {op : MixopS}
    {prems : List Prem} {code : List Admin} {w : List Value}
    (h : Silmaril.SpecTec.Equiv.Validation.HasRuleAt (simEnv20 B) "Step_pure" "%~>%" i
      (.ruleD nm qs "%~>%" (.tupE [.listE [.caseE "CONST" (.tupE [.varE "nt", o₁]),
        .caseE "CONST" (.tupE [.varE "nt", o₂]), .caseE op (.tupE [.varE "nt", e₃])], rh]) prems))
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    ∃ (t : NumType) (x y : BitVec t.width) (a : Admin),
      code = [(Val.num ⟨t, x⟩).toAdmin, (Val.num ⟨t, y⟩).toAdmin, a] ∧ adminHead20 a = op ∧
      ∀ u₁ u₂, adminToV a = .case op (.tuple [u₁, u₂]) → u₁ = numTypeV t := by
  obtain ⟨σ, -, hes⟩ := fires_list20 h hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨t, x, rfl⟩ := num_of_const (head20_of_caseE h₁)
  obtain ⟨t₂, y, rfl⟩ := num_of_const (head20_of_caseE h₂)
  obtain rfl := numTypeV_inj (nt_eq h₂ (adminToV_numAdmin t₂ y) h₁ (adminToV_numAdmin t x))
  exact ⟨t₂, x, y, a₃, rfl, head20_of_caseE h₃,
    fun u₁ u₂ hu => (nt_eq h₁ (adminToV_numAdmin t₂ x) h₃ hu).symm⟩

/-- `Step_pure/binop-val` at any code. -/
theorem bwdPure_binop (hI : IntB B) (hF : FloatB P B) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 22 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨t, x, y, a, rfl, ha, hn⟩ := num2_lhs (Pure.hasRuleAt_binopVal B) hf
  have hB := firesB_pure hf
  have A := Pure.numAgree_simEnv20 hI hF
  have T := Pure.numTyped_simEnv20 B
  rcases head20_binop ha with ⟨t', op, rfl⟩ | ⟨t', op, rfl⟩
  · obtain rfl := numTypeV_inj (hn _ _ rfl)
    obtain ⟨z, hz, hw⟩ := (Pure.intBinOp_iff B A T).1 hB
    exact pureBwd_of hw (.intBinOp hz)
  · obtain rfl := numTypeV_inj (hn _ _ rfl)
    obtain ⟨z, hz, hw⟩ := (Pure.floatBinOp_iff B A T).1 hB
    exact pureBwd_of hw (.floatBinOp hz)

/-- `Step_pure/relop` at any code. -/
theorem bwdPure_relop (hI : IntB B) (hF : FloatB P B) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 25 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨t, x, y, a, rfl, ha, hn⟩ := num2_lhs (Pure.hasRuleAt_relop B) hf
  have hB := firesB_pure hf
  have A := Pure.numAgree_simEnv20 hI hF
  have T := Pure.numTyped_simEnv20 B
  rcases head20_relop ha with ⟨t', op, rfl⟩ | ⟨t', op, rfl⟩
  · obtain rfl := numTypeV_inj (hn _ _ rfl)
    exact pureBwd_of ((Pure.intRelOp_iff B A T).1 hB) .intRelOp
  · obtain rfl := numTypeV_inj (hn _ _ rfl)
    exact pureBwd_of ((Pure.floatRelOp_iff B A T).1 hB) .floatRelOp

/-- `Step_pure/testop` at any code. -/
theorem bwdPure_testop (hI : IntB B) (hF : FloatB P B) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 24 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨σ, -, hes⟩ := fires_list20 (Pure.hasRuleAt_testop B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨t, x, rfl⟩ := num_of_const (head20_of_caseE h₁)
  obtain ⟨t', op, rfl⟩ := head20_testop (head20_of_caseE h₂)
  obtain rfl := numTypeV_inj (nt_eq h₁ (adminToV_numAdmin t x) h₂ rfl)
  exact pureBwd_of ((Pure.testOp_iff B (Pure.numAgree_simEnv20 hI hF)
    (Pure.numTyped_simEnv20 B)).1 (firesB_pure hf)) .testOp

/-- `Step_pure/cvtop-val` at any code whose conversion V2 defines. -/
theorem bwdPure_cvtop (hF : FloatB P B) {code : List Admin} {w : List Value}
    (hok : ∀ t₁ t₂ op, .plain (.cvtOp t₁ t₂ op) ∈ code → (V2.CvtOp.toShared t₁ t₂ op).isSome)
    (hf : Fires (simEnv20 B) "Step_pure" 26 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨σ, -, hes⟩ := fires_list20 (Pure.hasRuleAt_cvtopVal B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨t, x, rfl⟩ := num_of_const (head20_of_caseE h₁)
  obtain ⟨t₁, t₂, op, rfl⟩ := head20_cvtop (head20_of_caseE h₂)
  have e : numTypeV t = numTypeV t₂ := Option.some.inj
    ((var_fst (tup_of_caseE h₁ (adminToV_numAdmin t x))).symm.trans
      (var_snd (tup_of_caseE h₂ rfl)))
  obtain rfl := numTypeV_inj e
  obtain ⟨z, hz, hw⟩ := (Pure.cvtOp_iff B (Pure.cvtAgree_simEnv20 hF) (Pure.numTyped_simEnv20 B)
    (Pure.cvtTyped_simEnv20 B) (hok _ _ _ (by simp))).1 (firesB_pure hf)
  exact pureBwd_of hw (.cvtOp hz)

end Silmaril.Wasm.SpecTec.Sim20.Whole
