module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Env

/-!
# Integer numerics: the dispatchers denote Core's operators

`$unop_`, `$binop_`, `$testop_` and `$relop_` at an integer type, in `simEnv B` with `IntB B`,
denote exactly what Core's `intUnOp`, `intBinOp`, `intTestOp` and `intRelOp` compute. The
dispatch is the script's own: every clause for another opcode is skipped on its opcode pattern,
and the clause for the opcode is evaluated as written; only the primitives come from `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV NumEnv)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d132 Original.d143 Original.d503 Original.d504
  Original.d505 Original.d506)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

theorem ntV_i32 : ntV .i32 = .case "I32" (.tuple []) := rfl
theorem ntV_i64 : ntV .i64 = .case "I64" (.tuple []) := rfl

variable {B : Builtins}

/-! ## `$size` and `$sizenn` at an integer type -/

set_option maxRecDepth 100000 in
/-- `$size(Inn)` is the width. -/
theorem callDef_size_int (t : Silmaril.Wasm.IntType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "size" = none) (ha : EvalArgs (simEnv B) ρ args [.val (ntV t)]) :
    CallDef (simEnv B) ρ "size" args (natV t.width) := by
  refine callDef_of_tryClauses hρ (findDef_size B) ha ?_
  cases t with
  | i32 =>
      exact tryClauses_hit (ρ₀ := VarEnv.empty)
        (matchArgs_cons (matchArg_expA
          (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
        premsHold_nil evalExp_num
  | i64 =>
      refine tryClauses_skip_match (matchArgs_cons_undef
        (matchArg_expA_undef (matchExp_caseE_undef (by decide)))) ?_
      exact tryClauses_hit (ρ₀ := VarEnv.empty)
        (matchArgs_cons (matchArg_expA
          (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
        premsHold_nil evalExp_num

set_option maxRecDepth 100000 in
/-- `$sizenn(Inn)` is the width, through `$size`. -/
theorem callDef_sizenn_int (t : Silmaril.Wasm.IntType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "sizenn" = none) (ha : EvalArgs (simEnv B) ρ args [.val (ntV t)]) :
    CallDef (simEnv B) ρ "sizenn" args (natV t.width) := by
  refine callDef_of_tryClauses hρ (findDef_sizenn B) ha ?_
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" (ntV t))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    premsHold_nil
    (evalExp_callE_iff.2 (callDef_size_int t rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))

/-- `$sizenn(Inn)` written as the dispatcher clauses write it, `Inn` bound to `ntV t`. -/
theorem evalExp_sizennInn (t : Silmaril.Wasm.IntType) {ρ : VarEnv} {t₁ t₂ : Typ}
    (hρ : ρ.findDef? "sizenn" = none) (hInn : ρ.findVal? "Inn" = some (ntV t)) :
    EvalExp (simEnv B) ρ (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)])
      (natV t.width) :=
  evalExp_callE_iff.2 (callDef_sizenn_int t hρ
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hInn)) Equiv.evalArgs_nil))


/-! ## Walking a dispatcher -/

set_option maxRecDepth 100000 in
theorem findTyp_Inn : (simEnv B).findTyp? "Inn" = some ([], [.instD [] []
    (.variantT [.mk "I32" (.tupT []) [] [], .mk "I64" (.tupT []) [] []])]) := rfl

set_option maxRecDepth 100000 in
/-- An integer type passes the `Inn` pattern's subtype test (`Sem.argSubOk`). -/
theorem argSubOk_innPat_ntV (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv B) VarEnv.empty (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))
      (ntV t) = true := by
  cases t <;> rfl

/-- The `Inn` pattern of every integer dispatcher clause matches any value in its subtype and
binds it. -/
theorem matchArg_InnPat {env : Env} {ρ : VarEnv} {t₁ t₂ : Typ} {v : Value}
    (hx : ρ.findVal? "Inn" = none) (hs : argSubOk env ρ (.subE (.varE "Inn") t₁ t₂) v = true) :
    MatchArg env ρ (.expA (.subE (.varE "Inn") t₁ t₂)) (.val v) (ρ.bindVal "Inn" v) :=
  matchArg_expA (Equiv.Validation.matchExp_sub_iff.2
    ((Equiv.Execution.matchExp_freshVar_iff hx).2 rfl)) hs

/-- A dispatcher clause for another opcode is skipped: its `Inn` pattern fails its subtype test,
or matches and its opcode pattern definitely fails. -/
theorem skipOp {env : Env} {t₁ t₂ : Typ} {op op' : MixopS} {inner : Exp} {pats : List Arg}
    {nt p : Value} {ws : List ArgV} (hop : op ≠ op') :
    MatchArgsUndef env VarEnv.empty
      (.expA (.subE (.varE "Inn") t₁ t₂) :: .expA (.caseE op' inner) :: pats)
      (.val nt :: .val (.case op p) :: ws) := by
  cases hs : argSubOk env VarEnv.empty (.subE (.varE "Inn") t₁ t₂) nt with
  | false => exact matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub hs)
  | true =>
      exact matchArgs_cons_undef_tail (matchArg_InnPat (by simp) hs)
        (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hop)))

/-! ### Scopes, matches and arguments of the clause shapes -/

/-- The scope a one-operand clause binds (`Inn`, `i`). -/
def scope1 (nt c : Value) : VarEnv := (VarEnv.empty.bindVal "Inn" nt).bindVal "i" c

/-- The scope a two-operand clause with a nullary opcode binds (`Inn`, `i_1`, `i_2`). -/
def scope2 (nt c₁ c₂ : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Inn" nt).bindVal "i_1" c₁).bindVal "i_2" c₂

/-- The scope a two-operand clause with an `sx` opcode binds (`Inn`, `sx`, `i_1`, `i_2`). -/
def scope2s (nt s c₁ c₂ : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "Inn" nt).bindVal "sx" s).bindVal "i_1" c₁).bindVal "i_2" c₂

/-- A one-operand clause with a nullary opcode matches. -/
theorem matchArgs_nullary1 {env : Env} {t₁ t₂ : Typ} {op : MixopS} {nt c : Value}
    (hs : argSubOk env VarEnv.empty (.subE (.varE "Inn") t₁ t₂) nt = true := by
      exact argSubOk_innPat_ntV _) :
    MatchArgs env VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.tupE [])), .expA (.varE "i")]
      [.val nt, .val (.case op (.tuple [])), .val c] (scope1 nt c) :=
  matchArgs_cons (matchArg_InnPat (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))

/-- A two-operand clause with a nullary opcode `op` matches. -/
theorem matchArgs_nullary2 {env : Env} {t₁ t₂ : Typ} {op : MixopS} {nt c₁ c₂ : Value}
    (hs : argSubOk env VarEnv.empty (.subE (.varE "Inn") t₁ t₂) nt = true := by
      exact argSubOk_innPat_ntV _) :
    MatchArgs env VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val nt, .val (.case op (.tuple [])), .val c₁, .val c₂] (scope2 nt c₁ c₂) :=
  matchArgs_cons (matchArg_InnPat (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-- A two-operand clause whose opcode carries an `sx` matches. -/
theorem matchArgs_sx2 {env : Env} {t₁ t₂ : Typ} {op : MixopS} {nt s c₁ c₂ : Value}
    (hs : argSubOk env VarEnv.empty (.subE (.varE "Inn") t₁ t₂) nt = true := by
      exact argSubOk_innPat_ntV _) :
    MatchArgs env VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.varE "sx")), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val nt, .val (.case op s), .val c₁, .val c₂] (scope2s nt s c₁ c₂) :=
  matchArgs_cons (matchArg_InnPat (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE (by simp))))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-- `$sizenn(Inn), i` in a one-operand scope. -/
theorem evalArgs_prim1 (t : Silmaril.Wasm.IntType) (x : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv B) (scope1 (ntV t) (bvV x))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "i")]
      [.val (natV t.width), .val (bvV x)] :=
  Equiv.evalArgs_cons (evalExp_sizennInn t rfl (by simp [scope1]))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope1])) Equiv.evalArgs_nil)

/-- `$sizenn(Inn), i_1, i_2` in a two-operand scope. -/
theorem evalArgs_prim2 (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv B) (scope2 (ntV t) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV t.width), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizennInn t rfl (by simp [scope2]))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2]))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2])) Equiv.evalArgs_nil))

/-- `$sizenn(Inn), sx, i_1, i_2` in a two-operand `sx` scope. -/
theorem evalArgs_prim2s (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv B) (scope2s (ntV t) (Equiv.sxV s) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "sx"),
        .expA (.varE "i_1"), .expA (.varE "i_2")]
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizennInn t rfl (by simp [scope2s]))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s]))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s]))
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s])) Equiv.evalArgs_nil)))

/-! ### Clause bodies -/

/-- A body `[$prim(…)]`: the one-element list of the call. -/
theorem evalExp_list1Call {env : Env} {ρ : VarEnv} {x : IL.Id} {xs : List Arg} {r : Value}
    (h : CallDef env ρ x xs r) : EvalExp env ρ (.listE [.callE x xs]) (.list [r]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_callE_iff.2 h) evalExps_nil, rfl⟩

/-- A body `$prim(…)` lifted from an option to a list. -/
theorem evalExp_liftCall {env : Env} {ρ : VarEnv} {x : IL.Id} {xs : List Arg}
    {o : Option Value} (h : CallDef env ρ x xs (.opt o)) :
    EvalExp env ρ (.liftE (.callE x xs)) (.list o.toList) :=
  evalExp_liftE_iff.2 ⟨o, evalExp_callE_iff.2 h, rfl⟩

/-- A primitive with no clause, answered by `B` through `IntB`. -/
theorem callDef_prim (hB : IntB B) {x : IL.Id} (hx : NoClauses (simEnv B) x) {ρ : VarEnv}
    {args : List Arg} {ws : List ArgV} {v : Value} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv B) ρ args ws) (hc : intCall x ws = some v) :
    CallDef (simEnv B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ hc)

/-- Every `IntegerN` bit pattern is read back by `asBits?`. -/
theorem asPctNat?_bvV {N : Nat} (x : BitVec N) : asPctNat? (bvV x) = some x.toNat := rfl

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
