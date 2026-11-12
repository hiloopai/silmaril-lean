module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumLookup
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumDiv

/-!
# The wasm-2.0 dispatchers at integer types

`$unop_`, `$binop_`, `$testop_`, `$relop_` of the wasm-2.0 script (`Original.d182`, `d202`,
`d204`, `d217`) at an integer type, opcode by opcode, in `simEnv20 B` with `IntB B` (and
`FloatB P B` for `EXTEND`, whose 2.0 clause calls the builtins `$extend__`/`$wrap__`, not 3.0's
`$iextend_`). The clauses for other opcodes, and for `Fnn`, are skipped on their patterns; the
clause for the opcode is evaluated as written, with `Equiv.NumEnvCore.callDef_*` and `DivEnv`
(`Sim20/NumDiv.lean`) for the shared definitions and `B` for the primitives. They denote
`IntegerN.iunop_`, `ibinop_`, `itestop_`, `irelop_` (`applies_unop_int20` …).

Two clause shapes are 2.0's own: `EXTEND N'` binds a bare `nat`, and `DIV`/`REM` return
`$list_(num_(Inn), $idiv_(…))` where 3.0 lifts the option.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV optUNV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB intCall NoClauses evalExp_list1Call)
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Skipping clauses -/

/-- A `X <: numtype` pattern with `X` fresh matches a value in its subtype and binds it. -/
theorem matchArg_subVar20 {env : Env} {ρ : VarEnv} {X : IL.Id} {t₁ t₂ : Typ} {v : Value}
    (hx : ρ.findVal? X = none) (hs : argSubOk env ρ (.subE (.varE X) t₁ t₂) v = true) :
    MatchArg env ρ (.expA (.subE (.varE X) t₁ t₂)) (.val v) (ρ.bindVal X v) :=
  matchArg_expA (Equiv.Validation.matchExp_sub_iff.2
    ((Equiv.Execution.matchExp_freshVar_iff hx).2 rfl)) hs

/-- A dispatcher clause is skipped: its number-kind pattern fails its subtype test, or passes it
and its opcode pattern definitely fails. -/
theorem skipK20 {env : Env} {X : IL.Id} {t₁ t₂ : Typ} {o o' : MixopS} {inner : Exp}
    {pats : List Arg} {nt p : Value} {ws : List ArgV}
    (h : argSubOk env VarEnv.empty (.subE (.varE X) t₁ t₂) nt = false ∨
      (argSubOk env VarEnv.empty (.subE (.varE X) t₁ t₂) nt = true ∧ o ≠ o')) :
    MatchArgsUndef env VarEnv.empty
      (.expA (.subE (.varE X) t₁ t₂) :: .expA (.caseE o' inner) :: pats)
      (.val nt :: .val (.case o p) :: ws) := by
  rcases h with hs | ⟨hs, hne⟩
  · exact matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub hs)
  · exact matchArgs_cons_undef_tail (matchArg_subVar20 (by simp) hs)
      (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hne)))

set_option maxRecDepth 100000 in
theorem argSubOk_inn_int20 (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv20 B) VarEnv.empty
      (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])) (numTypeV (.int t)) = true := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_fnn_int20 (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv20 B) VarEnv.empty
      (.subE (.varE "Fnn") (.varT "Fnn" []) (.varT "numtype" [])) (numTypeV (.int t)) = false := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_inn_float20 (t : Silmaril.Wasm.FloatType) :
    argSubOk (simEnv20 B) VarEnv.empty
      (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])) (numTypeV (.float t)) =
      false := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_fnn_float20 (t : Silmaril.Wasm.FloatType) :
    argSubOk (simEnv20 B) VarEnv.empty
      (.subE (.varE "Fnn") (.varT "Fnn" []) (.varT "numtype" [])) (numTypeV (.float t)) = true := by
  cases t <;> rfl

/-- Skip every clause before the one for the opcode. -/
macro "skip20" : tactic => `(tactic| repeat (refine tryClauses_skip_match (skipK20 (by
    first
    | exact .inl (argSubOk_fnn_int20 _)
    | exact .inl (argSubOk_inn_float20 _)
    | exact .inr ⟨argSubOk_inn_int20 _, by decide⟩
    | exact .inr ⟨argSubOk_fnn_float20 _, by decide⟩)) ?_))

/-! ## Scopes and matches of the integer clause shapes -/

/-- The scope of a one-operand clause (`Inn`, `iN`). -/
def scope1' (nt c : Value) : VarEnv := (VarEnv.empty.bindVal "Inn" nt).bindVal "iN" c

/-- The scope of a two-operand clause with a nullary opcode (`Inn`, `iN_1`, `iN_2`). -/
def scope2' (nt c₁ c₂ : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Inn" nt).bindVal "iN_1" c₁).bindVal "iN_2" c₂

/-- The scope of a two-operand clause with an `sx` opcode (`Inn`, `sx`, `iN_1`, `iN_2`). -/
def scope2s' (nt s c₁ c₂ : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "Inn" nt).bindVal "sx" s).bindVal "iN_1" c₁).bindVal "iN_2" c₂

theorem matchArgs_un20 {t : Silmaril.Wasm.IntType} {t₁ t₂ : Typ} {op : MixopS} {c : Value}
    (hs : argSubOk (simEnv20 B) VarEnv.empty (.subE (.varE "Inn") t₁ t₂) (numTypeV (.int t)) =
      true) :
    MatchArgs (simEnv20 B) VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.tupE [])), .expA (.varE "iN")]
      [.val (numTypeV (.int t)), .val (.case op (.tuple [])), .val c]
      (scope1' (numTypeV (.int t)) c) :=
  matchArgs_cons (matchArg_subVar20 (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))

theorem matchArgs_bin20 {t : Silmaril.Wasm.IntType} {t₁ t₂ : Typ} {op : MixopS} {c₁ c₂ : Value}
    (hs : argSubOk (simEnv20 B) VarEnv.empty (.subE (.varE "Inn") t₁ t₂) (numTypeV (.int t)) =
      true) :
    MatchArgs (simEnv20 B) VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.tupE [])), .expA (.varE "iN_1"),
        .expA (.varE "iN_2")]
      [.val (numTypeV (.int t)), .val (.case op (.tuple [])), .val c₁, .val c₂]
      (scope2' (numTypeV (.int t)) c₁ c₂) :=
  matchArgs_cons (matchArg_subVar20 (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

theorem matchArgs_sx20 {t : Silmaril.Wasm.IntType} {t₁ t₂ : Typ} {op : MixopS}
    {s c₁ c₂ : Value}
    (hs : argSubOk (simEnv20 B) VarEnv.empty (.subE (.varE "Inn") t₁ t₂) (numTypeV (.int t)) =
      true) :
    MatchArgs (simEnv20 B) VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.varE "sx")), .expA (.varE "iN_1"),
        .expA (.varE "iN_2")]
      [.val (numTypeV (.int t)), .val (.case op s), .val c₁, .val c₂]
      (scope2s' (numTypeV (.int t)) s c₁ c₂) :=
  matchArgs_cons (matchArg_subVar20 (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE (by simp))))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

theorem evalArgs_un20 (t : Silmaril.Wasm.IntType) (x : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv20 B) (scope1' (numTypeV (.int t)) (bvV x))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "iN")]
      [.val (natV t.width), .val (bvV x)] :=
  Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scope1']))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope1'])) Equiv.evalArgs_nil)

theorem evalArgs_bin20 (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv20 B) (scope2' (numTypeV (.int t)) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "iN_1"),
        .expA (.varE "iN_2")]
      [.val (natV t.width), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scope2']))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2']))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2'])) Equiv.evalArgs_nil))

theorem evalArgs_sx20 (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv20 B) (scope2s' (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "sx"),
        .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scope2s']))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s']))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s']))
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s'])) Equiv.evalArgs_nil)))

/-! ## `$list_` -/

/-- `ε` definitely fails to match a non-empty option. -/
theorem matchExp_optNone_undef {env : Env} {ρ : VarEnv} {w : Value} :
    MatchExpUndef env ρ (.optE none) (.opt (some w)) :=
  ⟨1, by simp [matchExp, Res.assert]⟩

/-- `$list_(X, o)` is the list of the option's elements (`Original.d8`). -/
theorem callDef_list20 {ρ : VarEnv} {args : List Arg} {T : Typ} {o : Option Value}
    (hρ : ρ.findDef? "list_" = none) (ha : EvalArgs (simEnv20 B) ρ args [.typ T, .val (.opt o)]) :
    CallDef (simEnv20 B) ρ "list_" args (.list o.toList) := by
  refine callDef_of_tryClauses hρ (findDef_list20 B) ha ?_
  cases o with
  | none =>
      exact tryClauses_hit (matchArgs_cons (Sim.Round5.FwdRef.matchArg_typVar rfl (memTyp_X20 B))
        (matchArgs_cons (matchArg_expA Sim.Aggregates.matchExp_optNone) matchArgs_nil))
        premsHold_nil (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  | some w =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (Sim.Round5.FwdRef.matchArg_typVar rfl (memTyp_X20 B))
        (matchArgs_cons_undef (matchArg_expA_undef matchExp_optNone_undef))) ?_
      exact tryClauses_hit (matchArgs_cons (Sim.Round5.FwdRef.matchArg_typVar rfl (memTyp_X20 B))
        (matchArgs_cons (matchArg_expA (Equiv.Validation.matchExp_optSome_iff.2
          ⟨w, rfl, matchExp_varE rfl⟩)) matchArgs_nil))
        premsHold_nil (evalExp_listE_iff.2 ⟨[w],
          evalExps_cons (evalExp_varE_iff.2 rfl) evalExps_nil, rfl⟩)

/-! ## The dispatchers -/

/-- `iN_2` re-read as a shift count `%(iN_2!%.0)`. -/
theorem evalExp_shiftCount20 {ρ : VarEnv} {N : Nat} {y : BitVec N}
    (h : ρ.findVal? "iN_2" = some (bvV y)) :
    EvalExp (simEnv20 B) ρ (.caseE "%" (.tupE [.projE (.uncaseE (.varE "iN_2") "%") 0])) (bvV y) :=
  Equiv.evalExp_case_tup_one (Equiv.evalExp_uNV_payload h)

theorem evalArgs_shl20 (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv20 B) (scope2' (numTypeV (.int t)) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "iN_1"),
        .expA (.caseE "%" (.tupE [.projE (.uncaseE (.varE "iN_2") "%") 0]))]
      [.val (natV t.width), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scope2']))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2']))
      (Equiv.evalArgs_cons (evalExp_shiftCount20 (by simp [scope2'])) Equiv.evalArgs_nil))

theorem evalArgs_shr20 (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv20 B) (scope2s' (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "sx"),
        .expA (.varE "iN_1"), .expA (.caseE "%" (.tupE [.projE (.uncaseE (.varE "iN_2") "%") 0]))]
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scope2s']))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s']))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s']))
        (Equiv.evalArgs_cons (evalExp_shiftCount20 (by simp [scope2s'])) Equiv.evalArgs_nil)))

set_option maxRecDepth 100000 in
/-- The `$idiv_`/`$irem_` lemmas hold in `simEnv20 B`. -/
theorem divEnv_simEnv20 (hB : IntB B) : DivEnv (simEnv20 B) :=
  ⟨numEnvCore_simEnv20 B, hB, ⟨_, _, rfl⟩⟩

/-- The `Inn` argument pattern of the 2.0 integer clauses. -/
abbrev innPat20 : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])

/-- A two-operand clause `[$f($sizenn(Inn), iN_1, iN_2)]` for the opcode `o` fires. -/
theorem hitBin2 {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {t : Silmaril.Wasm.IntType} {x y : BitVec t.width} {v : Value}
    (hc : CallDef (simEnv20 B) (scope2' (numTypeV (.int t)) (bvV x) (bvV y)) f args v) :
    TryClauses (simEnv20 B) (.defD q
      [.expA innPat20, .expA (.caseE o (.tupE [])), .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      (.listE [.callE f args]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (.tuple [])), .val (bvV x), .val (bvV y)]
      (.list [v]) :=
  tryClauses_hit (matchArgs_bin20 (argSubOk_inn_int20 t)) premsHold_nil (evalExp_list1Call hc)

/-- A two-operand clause `[$f($sizenn(Inn), sx, iN_1, iN_2)]` for the opcode `o` fires. -/
theorem hitBin2s {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {t : Silmaril.Wasm.IntType} {s : Silmaril.Wasm.Signedness} {x y : BitVec t.width} {v : Value}
    (hc : CallDef (simEnv20 B) (scope2s' (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y)) f args
      v) :
    TryClauses (simEnv20 B) (.defD q
      [.expA innPat20, .expA (.caseE o (.varE "sx")), .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      (.listE [.callE f args]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (Equiv.sxV s)), .val (bvV x), .val (bvV y)]
      (.list [v]) :=
  tryClauses_hit (matchArgs_sx20 (argSubOk_inn_int20 t)) premsHold_nil (evalExp_list1Call hc)

/-- The `DIV`/`REM` clause `$list_(num_(Inn), $f($sizenn(Inn), sx, iN_1, iN_2))` fires. -/
theorem hitDivRem {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {T : Typ} {t : Silmaril.Wasm.IntType} {s : Silmaril.Wasm.Signedness} {x y : BitVec t.width}
    {r : Option (BitVec t.width)}
    (hc : CallDef (simEnv20 B) (scope2s' (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y)) f args
      (optUNV r)) :
    TryClauses (simEnv20 B) (.defD q
      [.expA innPat20, .expA (.caseE o (.varE "sx")), .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      (.callE "list_" [.typA T, .expA (.callE f args)]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (Equiv.sxV s)), .val (bvV x), .val (bvV y)]
      (.list (r.toList.map bvV)) := by
  rw [← Sim.IntNumeric.optUNV_toList]
  exact tryClauses_hit (matchArgs_sx20 (argSubOk_inn_int20 t)) premsHold_nil
    (evalExp_callE_iff.2 (callDef_list20 rfl (Sim.Round5.FwdRef.evalArgs_typA
      (Equiv.evalArgs_cons (evalExp_callE_iff.2 hc) Equiv.evalArgs_nil))))

set_option maxRecDepth 100000 in
/-- **`$binop_` at an integer type is `IntegerN.ibinop_`**, as a list (empty on a trap). -/
theorem applies_binop_int20 (hB : IntB B) (t : Silmaril.Wasm.IntType)
    (op : Silmaril.Wasm.IntBinOp) (x y : BitVec t.width) :
    Applies (simEnv20 B) "binop_" [.val (numTypeV (.int t)), .val (intBinOpV op), .val (bvV x),
      .val (bvV y)] (.list ((ibinop_ t.width op x y).toList.map bvV)) := by
  refine ⟨_, _, _, findDef_binop20 B, Or.inl ?_⟩
  have hN : Equiv.NumEnvCore (simEnv20 B) := numEnvCore_simEnv20 B
  have hD : DivEnv (simEnv20 B) := divEnv_simEnv20 hB
  cases op <;> skip20
  · exact hitBin2 (hN.callDef_iadd rfl (evalArgs_bin20 t x y))
  · exact hitBin2 (hN.callDef_isub rfl (evalArgs_bin20 t x y))
  · exact hitBin2 (hN.callDef_imul rfl (evalArgs_bin20 t x y))
  · exact hitDivRem (hD.callDef_idiv t _ x y rfl (evalArgs_sx20 t _ x y))
  · exact hitDivRem (hD.callDef_irem t _ x y rfl (evalArgs_sx20 t _ x y))
  · exact hitBin2 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_bin20 t x y)
      (Sim.IntNumeric.intCall_iand _ x y))
  · exact hitBin2 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_bin20 t x y)
      (Sim.IntNumeric.intCall_ior _ x y))
  · exact hitBin2 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_bin20 t x y)
      (Sim.IntNumeric.intCall_ixor _ x y))
  · exact hitBin2 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_shl20 t x y)
      (Sim.IntNumeric.intCall_ishl _ x y))
  · exact hitBin2s (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_shr20 t _ x y)
      (Sim.IntNumeric.intCall_ishr _ _ x y))
  · exact hitBin2 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_bin20 t x y)
      (Sim.IntNumeric.intCall_irotl _ x y))
  · exact hitBin2 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_bin20 t x y)
      (Sim.IntNumeric.intCall_irotr _ x y))

/-- A one-operand clause `[$f($sizenn(Inn), iN)]` for the opcode `o` fires. -/
theorem hitUn1 {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {t : Silmaril.Wasm.IntType} {x : BitVec t.width} {v : Value}
    (hc : CallDef (simEnv20 B) (scope1' (numTypeV (.int t)) (bvV x)) f args v) :
    TryClauses (simEnv20 B) (.defD q
      [.expA innPat20, .expA (.caseE o (.tupE [])), .expA (.varE "iN")]
      (.listE [.callE f args]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (.tuple [])), .val (bvV x)] (.list [v]) :=
  tryClauses_hit (matchArgs_un20 (argSubOk_inn_int20 t)) premsHold_nil (evalExp_list1Call hc)

/-- The scope of the 2.0 `EXTEND` clause (`Inn`, `N'`, `iN`). -/
def scopeExt' (nt k c : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Inn" nt).bindVal "N'" k).bindVal "iN" c

/-- The 2.0 `EXTEND N'` clause matches, binding `N'` to the bare width. -/
theorem matchArgs_ext20 (t : Silmaril.Wasm.IntType) (p : Silmaril.Wasm.PackSize)
    (x : BitVec t.width) :
    MatchArgs (simEnv20 B) VarEnv.empty
      [.expA innPat20, .expA (.caseE "EXTEND" (.varE "N'")), .expA (.varE "iN")]
      [.val (numTypeV (.int t)), .val (intUnOpV (.extend p)), .val (bvV x)]
      (scopeExt' (numTypeV (.int t)) (natV p.width) (bvV x)) :=
  matchArgs_cons (matchArg_subVar20 (by simp) (argSubOk_inn_int20 t))
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE (by simp))))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))

set_option maxRecDepth 100000 in
/-- `$wrap__($sizenn(Inn), N', iN)` is the low `N'` bits. -/
theorem evalExp_wrap20 {P : Profile} (hF : Sim.Floats.FloatB P B) (t : Silmaril.Wasm.IntType)
    (p : Silmaril.Wasm.PackSize) (x : BitVec t.width) :
    EvalExp (simEnv20 B) (scopeExt' (numTypeV (.int t)) (natV p.width) (bvV x))
      (.callE "wrap__" [.expA (.callE "sizenn" [.expA innPat20]), .expA (.varE "N'"),
        .expA (.varE "iN")]) (bvV (x.setWidth p.width)) :=
  evalExp_callE_iff.2 (callDef_floatPrim20 hF ⟨_, _, rfl⟩ rfl
    (Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scopeExt']))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scopeExt']))
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scopeExt']; rfl)) Equiv.evalArgs_nil)))
    (Sim.Floats.floatCall_wrap P t.width p.width x))

set_option maxRecDepth 100000 in
/-- `$extend__(N', $sizenn(Inn), S, $wrap__(…))` is the sign extension of the low bits. -/
theorem callDef_ext20 {P : Profile} (hF : Sim.Floats.FloatB P B) (t : Silmaril.Wasm.IntType)
    (p : Silmaril.Wasm.PackSize) (x : BitVec t.width) :
    CallDef (simEnv20 B) (scopeExt' (numTypeV (.int t)) (natV p.width) (bvV x)) "extend__"
      [.expA (.varE "N'"), .expA (.callE "sizenn" [.expA innPat20]), .expA (.caseE "S" (.tupE [])),
        .expA (.callE "wrap__" [.expA (.callE "sizenn" [.expA innPat20]), .expA (.varE "N'"),
          .expA (.varE "iN")])]
      (bvV ((x.setWidth p.width).signExtend t.width)) :=
  callDef_floatPrim20 hF ⟨_, _, rfl⟩ rfl
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scopeExt']))
      (Equiv.evalArgs_cons (evalExp_sizenn20 (.int t) rfl (by simp [scopeExt']))
        (Equiv.evalArgs_cons (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil,
          rfl⟩, rfl⟩) (Equiv.evalArgs_cons (evalExp_wrap20 hF t p x) Equiv.evalArgs_nil))))
    (Sim.Floats.floatCall_extend P p.width t.width .signed (x.setWidth p.width))

set_option maxRecDepth 100000 in
/-- **`$unop_` at an integer type is Core's `intUnOp`**, at every operator. `EXTEND N'` goes
through the builtins `$wrap__` and `$extend__` (2.0 has no `$iextend_`). -/
theorem applies_unop_int20 {P : Profile} (hB : IntB B) (hF : Sim.Floats.FloatB P B)
    (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntUnOp) (x : BitVec t.width) :
    Applies (simEnv20 B) "unop_" [.val (numTypeV (.int t)), .val (intUnOpV op), .val (bvV x)]
      (.list [bvV (intUnOp t op x)]) := by
  refine ⟨_, _, _, findDef_unop20 B, Or.inl ?_⟩
  cases op <;> skip20
  · exact hitUn1 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_un20 t x)
      (Sim.IntNumeric.intCall_iclz _ x))
  · exact hitUn1 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_un20 t x)
      (Sim.IntNumeric.intCall_ictz _ x))
  · exact hitUn1 (callDef_prim20 hB ⟨_, _, rfl⟩ rfl (evalArgs_un20 t x)
      (Sim.IntNumeric.intCall_ipopcnt _ x))
  · exact tryClauses_hit (matchArgs_ext20 t _ x) premsHold_nil
      (evalExp_list1Call (callDef_ext20 hF t _ x))

set_option maxRecDepth 100000 in
/-- **`$testop_` at an integer type is Core's `intTestOp`.** -/
theorem applies_testop_int20 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntTestOp)
    (x : BitVec t.width) :
    Applies (simEnv20 B) "testop_" [.val (numTypeV (.int t)), .val (intTestOpV op), .val (bvV x)]
      (bvV (intTestOp t op x)) := by
  refine ⟨_, _, _, findDef_testop20 B, Or.inl ?_⟩
  rw [← itestop_agree]
  cases op
  exact tryClauses_hit (matchArgs_un20 (argSubOk_inn_int20 t)) premsHold_nil
    (evalExp_callE_iff.2 ((numEnvCore_simEnv20 B).callDef_ieqz rfl (evalArgs_un20 t x)))

set_option maxRecDepth 100000 in
/-- **`$relop_` at an integer type is Core's `intRelOp`.** -/
theorem applies_relop_int20 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntRelOp)
    (x y : BitVec t.width) :
    Applies (simEnv20 B) "relop_" [.val (numTypeV (.int t)), .val (intRelOpV op), .val (bvV x),
      .val (bvV y)] (bvV (intRelOp t op x y)) := by
  refine ⟨_, _, _, findDef_relop20 B, Or.inl ?_⟩
  have hs := argSubOk_inn_int20 (B := B) t
  rw [← irelop_agree]
  have hw : 0 < t.width := by cases t <;> decide
  cases op with
  | eq => exact tryClauses_hit (matchArgs_bin20 hs) premsHold_nil (evalExp_callE_iff.2
      ((numEnvCore_simEnv20 B).callDef_ieq rfl (evalArgs_bin20 t x y)))
  | ne => skip20; exact tryClauses_hit (matchArgs_bin20 hs) premsHold_nil (evalExp_callE_iff.2
      ((numEnvCore_simEnv20 B).callDef_ine rfl (evalArgs_bin20 t x y)))
  | lt s => skip20; exact tryClauses_hit (matchArgs_sx20 hs) premsHold_nil (evalExp_callE_iff.2
      ((numEnvCore_simEnv20 B).callDef_ilt rfl (evalArgs_sx20 t s x y) hw))
  | gt s => skip20; exact tryClauses_hit (matchArgs_sx20 hs) premsHold_nil (evalExp_callE_iff.2
      ((numEnvCore_simEnv20 B).callDef_igt rfl (evalArgs_sx20 t s x y) hw))
  | le s => skip20; exact tryClauses_hit (matchArgs_sx20 hs) premsHold_nil (evalExp_callE_iff.2
      ((numEnvCore_simEnv20 B).callDef_ile rfl (evalArgs_sx20 t s x y) hw))
  | ge s => skip20; exact tryClauses_hit (matchArgs_sx20 hs) premsHold_nil (evalExp_callE_iff.2
      ((numEnvCore_simEnv20 B).callDef_ige rfl (evalArgs_sx20 t s x y) hw))

end Silmaril.Wasm.SpecTec.Sim20.Pure
