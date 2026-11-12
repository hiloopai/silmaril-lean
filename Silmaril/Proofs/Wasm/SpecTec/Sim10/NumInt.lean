module

public import Silmaril.Raw.Wasm.SpecTec.Sim10.NumDiv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumAgree
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemTrap

/-!
# The wasm-1.0 dispatchers at integer and float types

`$unop_`, `$binop_`, `$testop_` and `$relop_` of the wasm-1.0 script (`Original.d101`, `d121`,
`d123`, `d136`), opcode by opcode, in `simEnv10 B`. They have 2.0's clause shapes with two
differences: the kind patterns are `Inn <: valtype`/`Fnn <: valtype` (2.0: `numtype`), and the
width is `$size(Inn)` (2.0: `$sizenn`). wasm-1.0 has no `EXTEND` among its `unop_`, and its bit
operations (`$iand_` … `$ipopcnt_`) are `hint(builtin)` where 2.0 defines them; `IntB B`
answers them (`Sim.IntNumeric.intCall`).

* `numEnv10_simEnv10`: the 16 shared integer definitions wasm-1.0 has (`Sim10.NumEnv10`), each a
  kernel `rfl`; with `IntB B` this is a `DivEnv10`, so the copied `$idiv_`/`$irem_` lemmas apply.
* `applies_unop_int10`, `applies_binop_int10`, `applies_testop_int10`, `applies_relop_int10`: at
  an integer type each dispatcher is Core's (`IntegerN`) operator.
* `applies_unop_float10`, `applies_binop_float10`, `applies_relop_float10`: at a float type each
  is the list of every result the profile allows, under `Floats.FloatB P B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV optUNV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB intCall NoClauses defOf evalExp_list1Call)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB floatCall unRes binRes)
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV intBinOpV floatUnOpV floatBinOpV intTestOpV intRelOpV
  floatRelOpV)
open Silmaril.Wasm.SpecTec.Sim20.Pure (skipK20 matchArg_subVar20 matchExp_optNone_undef)
open Silmaril.Wasm.SpecTec.Scripts.Wasm10 (Original.d9 Original.d101 Original.d121 Original.d123
  Original.d136)
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Lookups -/

set_option maxRecDepth 100000 in
/-- **The 16 shared integer definitions are wasm-1.0's.** -/
theorem numEnv10_simEnv10 (B : Builtins) : NumEnv10 (simEnv10 B) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- With `IntB B`, `simEnv10 B` is a `DivEnv10`. -/
theorem divEnv10_simEnv10 (hB : IntB B) : DivEnv10 (simEnv10 B) :=
  ⟨numEnv10_simEnv10 B, hB, ⟨_, _, rfl⟩⟩

set_option maxRecDepth 100000 in
theorem findDef_list10 (B : Builtins) : (simEnv10 B).findDef? "list_" = defOf Original.d9 := rfl

set_option maxRecDepth 100000 in
theorem findDef_unop10 (B : Builtins) : (simEnv10 B).findDef? "unop_" = defOf Original.d101 :=
  rfl

set_option maxRecDepth 100000 in
theorem findDef_binop10 (B : Builtins) : (simEnv10 B).findDef? "binop_" = defOf Original.d121 :=
  rfl

set_option maxRecDepth 100000 in
theorem findDef_testop10 (B : Builtins) :
    (simEnv10 B).findDef? "testop_" = defOf Original.d123 := rfl

set_option maxRecDepth 100000 in
theorem findDef_relop10 (B : Builtins) : (simEnv10 B).findDef? "relop_" = defOf Original.d136 :=
  rfl

set_option maxRecDepth 100000 in
/-- `X` is not a type of the 1.0 script, so `$list_`'s type parameter binds. -/
theorem memTyp_X10 (B : Builtins) : (simEnv10 B).memTyp "X" = false := rfl

/-! ## Kind patterns -/

/-- The 1.0 `Inn` pattern. -/
abbrev innPat10' : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "valtype" [])

/-- The 1.0 `Fnn` pattern. -/
abbrev fnnPat10 : Exp := .subE (.varE "Fnn") (.varT "Fnn" []) (.varT "valtype" [])

set_option maxRecDepth 100000 in
theorem argSubOk_inn_int10 (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv10 B) VarEnv.empty innPat10' (numTypeV (.int t)) = true := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_fnn_int10 (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv10 B) VarEnv.empty fnnPat10 (numTypeV (.int t)) = false := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_inn_float10 (t : Silmaril.Wasm.FloatType) :
    argSubOk (simEnv10 B) VarEnv.empty innPat10' (numTypeV (.float t)) = false := by
  cases t <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_fnn_float10 (t : Silmaril.Wasm.FloatType) :
    argSubOk (simEnv10 B) VarEnv.empty fnnPat10 (numTypeV (.float t)) = true := by
  cases t <;> rfl

/-- Skip every 1.0 dispatcher clause before the one for the opcode. -/
macro "skip10" : tactic => `(tactic| repeat (refine tryClauses_skip_match (skipK20 (by
    first
    | exact .inl (argSubOk_fnn_int10 _)
    | exact .inl (argSubOk_inn_float10 _)
    | exact .inr ⟨argSubOk_inn_int10 _, by decide⟩
    | exact .inr ⟨argSubOk_fnn_float10 _, by decide⟩)) ?_))

/-! ## `$size`, primitives, `$list_` -/

/-- `$size(X)` as the dispatcher clauses write it, `X` bound to the number type. -/
theorem evalExp_sizeK10 (t : Silmaril.Wasm.NumType) {ρ : VarEnv} {X : IL.Id} {t₁ t₂ : Typ}
    (hρ : ρ.findDef? "size" = none) (hX : ρ.findVal? X = some (numTypeV t)) :
    EvalExp (simEnv10 B) ρ (.callE "size" [.expA (.subE (.varE X) t₁ t₂)]) (natV t.width) :=
  evalExp_size10 t hρ (evalExp_subE_iff.2 (evalExp_varE_iff.2 hX))

/-- A primitive with no clause, answered by `B` through `IntB`. -/
theorem callDef_prim10 (hB : IntB B) {x : IL.Id} (hx : NoClauses (simEnv10 B) x) {ρ : VarEnv}
    {args : List Arg} {ws : List ArgV} {v : Value} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv10 B) ρ args ws) (hc : intCall x ws = some v) :
    CallDef (simEnv10 B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ hc)

/-- A primitive with no clause, answered by `B` through `FloatB`. -/
theorem callDef_floatPrim10 {P : Profile} (hB : FloatB P B) {x : IL.Id}
    (hx : NoClauses (simEnv10 B) x) {ρ : VarEnv} {args : List Arg} {ws : List ArgV} {v : Value}
    (hρ : ρ.findDef? x = none) (ha : EvalArgs (simEnv10 B) ρ args ws)
    (hc : floatCall P x ws = some v) : CallDef (simEnv10 B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ hc)

/-- `$list_(X, o)` is the list of the option's elements (`Original.d9`). -/
theorem callDef_list10 {ρ : VarEnv} {args : List Arg} {T : Typ} {o : Option Value}
    (hρ : ρ.findDef? "list_" = none) (ha : EvalArgs (simEnv10 B) ρ args [.typ T, .val (.opt o)]) :
    CallDef (simEnv10 B) ρ "list_" args (.list o.toList) := by
  refine callDef_of_tryClauses hρ (findDef_list10 B) ha ?_
  cases o with
  | none =>
      exact tryClauses_hit (matchArgs_cons (Sim.Round5.FwdRef.matchArg_typVar rfl (memTyp_X10 B))
        (matchArgs_cons (matchArg_expA Sim.Aggregates.matchExp_optNone) matchArgs_nil))
        premsHold_nil (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  | some w =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (Sim.Round5.FwdRef.matchArg_typVar rfl (memTyp_X10 B))
        (matchArgs_cons_undef (matchArg_expA_undef matchExp_optNone_undef))) ?_
      exact tryClauses_hit (matchArgs_cons (Sim.Round5.FwdRef.matchArg_typVar rfl (memTyp_X10 B))
        (matchArgs_cons (matchArg_expA (Equiv.Validation.matchExp_optSome_iff.2
          ⟨w, rfl, matchExp_varE rfl⟩)) matchArgs_nil))
        premsHold_nil (evalExp_listE_iff.2 ⟨[w],
          evalExps_cons (evalExp_varE_iff.2 rfl) evalExps_nil, rfl⟩)

/-! ## Scopes and matches -/

/-- The scope of a one-operand clause (`K`, `x`). -/
abbrev sc1 (K x : IL.Id) (nt c : Value) : VarEnv := (VarEnv.empty.bindVal K nt).bindVal x c

/-- The scope of a two-operand clause with a nullary opcode (`K`, `x_1`, `x_2`). -/
abbrev sc2 (K x₁ x₂ : IL.Id) (nt c₁ c₂ : Value) : VarEnv :=
  ((VarEnv.empty.bindVal K nt).bindVal x₁ c₁).bindVal x₂ c₂

/-- The scope of a two-operand clause with an `sx` opcode (`Inn`, `sx`, `iN_1`, `iN_2`). -/
abbrev sc2s (nt s c₁ c₂ : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "Inn" nt).bindVal "sx" s).bindVal "iN_1" c₁).bindVal "iN_2" c₂

theorem matchArgs_un10 {K x : IL.Id} {t₁ t₂ : Typ} {op : MixopS} {nt c : Value}
    (hK : K ≠ x) (hK' : K ≠ "_")
    (hs : argSubOk (simEnv10 B) VarEnv.empty (.subE (.varE K) t₁ t₂) nt = true) :
    MatchArgs (simEnv10 B) VarEnv.empty
      [.expA (.subE (.varE K) t₁ t₂), .expA (.caseE op (.tupE [])), .expA (.varE x)]
      [.val nt, .val (.case op (.tuple [])), .val c] (sc1 K x nt c) :=
  matchArgs_cons (matchArg_subVar20 (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp [hK, hK']))) matchArgs_nil))

theorem matchArgs_bin10 {K x₁ x₂ : IL.Id} {t₁ t₂ : Typ} {op : MixopS} {nt c₁ c₂ : Value}
    (h₁ : K ≠ x₁) (h₂ : K ≠ x₂) (h₁₂ : x₁ ≠ x₂) (hK' : K ≠ "_") (hx₁ : x₁ ≠ "_")
    (hs : argSubOk (simEnv10 B) VarEnv.empty (.subE (.varE K) t₁ t₂) nt = true) :
    MatchArgs (simEnv10 B) VarEnv.empty
      [.expA (.subE (.varE K) t₁ t₂), .expA (.caseE op (.tupE [])), .expA (.varE x₁),
        .expA (.varE x₂)]
      [.val nt, .val (.case op (.tuple [])), .val c₁, .val c₂] (sc2 K x₁ x₂ nt c₁ c₂) :=
  matchArgs_cons (matchArg_subVar20 (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp [h₁, hK'])))
        (matchArgs_cons (matchArg_expA (matchExp_varE
          (by simp [h₂, h₁₂, hK', hx₁])))
          matchArgs_nil)))

theorem matchArgs_sx10 {t₁ t₂ : Typ} {op : MixopS} {nt s c₁ c₂ : Value}
    (hs : argSubOk (simEnv10 B) VarEnv.empty (.subE (.varE "Inn") t₁ t₂) nt = true) :
    MatchArgs (simEnv10 B) VarEnv.empty
      [.expA (.subE (.varE "Inn") t₁ t₂), .expA (.caseE op (.varE "sx")), .expA (.varE "iN_1"),
        .expA (.varE "iN_2")]
      [.val nt, .val (.case op s), .val c₁, .val c₂] (sc2s nt s c₁ c₂) :=
  matchArgs_cons (matchArg_subVar20 (by simp) hs)
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE (by simp))))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-- `[$size(K), x]`, evaluated. -/
theorem evalArgs_un10 (t : Silmaril.Wasm.NumType) {K x : IL.Id} (hK : K ≠ x) (hK' : K ≠ "_")
    (hx' : x ≠ "_") {c : Value} {t₁ t₂ : Typ} :
    EvalArgs (simEnv10 B) (sc1 K x (numTypeV t) c)
      [.expA (.callE "size" [.expA (.subE (.varE K) t₁ t₂)]), .expA (.varE x)]
      [.val (natV t.width), .val c] :=
  Equiv.evalArgs_cons (evalExp_sizeK10 t rfl (by simp [Ne.symm hK, hK', hx']))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [hx'])) Equiv.evalArgs_nil)

/-- `[$size(K), x_1, x_2]`, evaluated. -/
theorem evalArgs_bin10 (t : Silmaril.Wasm.NumType) {K x₁ x₂ : IL.Id} (h₁ : K ≠ x₁)
    (h₂ : K ≠ x₂) (h₁₂ : x₁ ≠ x₂) (hK' : K ≠ "_") (hx₁ : x₁ ≠ "_") (hx₂ : x₂ ≠ "_")
    {c₁ c₂ : Value} {t₁ t₂ : Typ} :
    EvalArgs (simEnv10 B) (sc2 K x₁ x₂ (numTypeV t) c₁ c₂)
      [.expA (.callE "size" [.expA (.subE (.varE K) t₁ t₂)]), .expA (.varE x₁), .expA (.varE x₂)]
      [.val (natV t.width), .val c₁, .val c₂] :=
  Equiv.evalArgs_cons
    (evalExp_sizeK10 t rfl (by simp [Ne.symm h₁, Ne.symm h₂, hK', hx₁, hx₂]))
    (Equiv.evalArgs_cons
      (evalExp_varE_iff.2 (by simp [Ne.symm h₁₂, hx₁, hx₂]))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [hx₂])) Equiv.evalArgs_nil))

/-- `[$size(Inn), sx, iN_1, iN_2]`, evaluated. -/
theorem evalArgs_sx10 (t : Silmaril.Wasm.IntType) {s c₁ c₂ : Value} {t₁ t₂ : Typ} :
    EvalArgs (simEnv10 B) (sc2s (numTypeV (.int t)) s c₁ c₂)
      [.expA (.callE "size" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "sx"),
        .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      [.val (natV t.width), .val s, .val c₁, .val c₂] :=
  Equiv.evalArgs_cons (evalExp_sizeK10 (.int t) rfl (by simp))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))

/-- `[$size(Inn), iN_1, %(iN_2!%.0)]`, the shift arguments, evaluated. -/
theorem evalArgs_shl10 (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv10 B) (sc2 "Inn" "iN_1" "iN_2" (numTypeV (.int t)) (bvV x) (bvV y))
      [.expA (.callE "size" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "iN_1"),
        .expA (.caseE "%" (.tupE [.projE (.uncaseE (.varE "iN_2") "%") 0]))]
      [.val (natV t.width), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizeK10 (.int t) rfl (by simp))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (Equiv.evalArgs_cons (Equiv.evalExp_case_tup_one (Equiv.evalExp_uNV_payload (by simp)))
        Equiv.evalArgs_nil))

/-- `[$size(Inn), sx, iN_1, %(iN_2!%.0)]`, evaluated. -/
theorem evalArgs_shr10 (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv10 B) (sc2s (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y))
      [.expA (.callE "size" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "sx"),
        .expA (.varE "iN_1"), .expA (.caseE "%" (.tupE [.projE (.uncaseE (.varE "iN_2") "%") 0]))]
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizeK10 (.int t) rfl (by simp))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (Equiv.evalArgs_cons (Equiv.evalExp_case_tup_one (Equiv.evalExp_uNV_payload (by simp)))
          Equiv.evalArgs_nil)))

/-! ## Hitting the clause for the opcode -/

theorem hitUn10 {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {t : Silmaril.Wasm.IntType} {x : BitVec t.width} {v : Value}
    (hc : CallDef (simEnv10 B) (sc1 "Inn" "iN" (numTypeV (.int t)) (bvV x)) f args v) :
    TryClauses (simEnv10 B) (.defD q
      [.expA innPat10', .expA (.caseE o (.tupE [])), .expA (.varE "iN")]
      (.listE [.callE f args]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (.tuple [])), .val (bvV x)] (.list [v]) :=
  tryClauses_hit (matchArgs_un10 (by decide) (by decide) (argSubOk_inn_int10 t)) premsHold_nil
    (evalExp_list1Call hc)

theorem hitBin10 {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {t : Silmaril.Wasm.IntType} {x y : BitVec t.width} {v : Value}
    (hc : CallDef (simEnv10 B) (sc2 "Inn" "iN_1" "iN_2" (numTypeV (.int t)) (bvV x) (bvV y)) f
      args v) :
    TryClauses (simEnv10 B) (.defD q
      [.expA innPat10', .expA (.caseE o (.tupE [])), .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      (.listE [.callE f args]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (.tuple [])), .val (bvV x), .val (bvV y)]
      (.list [v]) :=
  tryClauses_hit (matchArgs_bin10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (argSubOk_inn_int10 t))
    premsHold_nil (evalExp_list1Call hc)

theorem hitBin10s {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id} {args : List Arg}
    {t : Silmaril.Wasm.IntType} {s : Silmaril.Wasm.Signedness} {x y : BitVec t.width} {v : Value}
    (hc : CallDef (simEnv10 B) (sc2s (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y)) f args v) :
    TryClauses (simEnv10 B) (.defD q
      [.expA innPat10', .expA (.caseE o (.varE "sx")), .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      (.listE [.callE f args]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (Equiv.sxV s)), .val (bvV x), .val (bvV y)]
      (.list [v]) :=
  tryClauses_hit (matchArgs_sx10 (argSubOk_inn_int10 t)) premsHold_nil (evalExp_list1Call hc)

theorem hitDivRem10 {q : List Param} {cs : List Clause} {o : MixopS} {f : IL.Id}
    {args : List Arg} {T : Typ} {t : Silmaril.Wasm.IntType} {s : Silmaril.Wasm.Signedness}
    {x y : BitVec t.width} {r : Option (BitVec t.width)}
    (hc : CallDef (simEnv10 B) (sc2s (numTypeV (.int t)) (Equiv.sxV s) (bvV x) (bvV y)) f args
      (optUNV r)) :
    TryClauses (simEnv10 B) (.defD q
      [.expA innPat10', .expA (.caseE o (.varE "sx")), .expA (.varE "iN_1"), .expA (.varE "iN_2")]
      (.callE "list_" [.typA T, .expA (.callE f args)]) [] :: cs)
      [.val (numTypeV (.int t)), .val (.case o (Equiv.sxV s)), .val (bvV x), .val (bvV y)]
      (.list (r.toList.map bvV)) := by
  rw [← Sim.IntNumeric.optUNV_toList]
  exact tryClauses_hit (matchArgs_sx10 (argSubOk_inn_int10 t)) premsHold_nil
    (evalExp_callE_iff.2 (callDef_list10 rfl (Sim.Round5.FwdRef.evalArgs_typA
      (Equiv.evalArgs_cons (evalExp_callE_iff.2 hc) Equiv.evalArgs_nil))))

/-! ## The integer dispatchers -/

set_option maxRecDepth 100000 in
/-- **`$binop_` at an integer type is `IntegerN.ibinop_`**, as a list (empty on a trap). -/
theorem applies_binop_int10 (hB : IntB B) (t : Silmaril.Wasm.IntType)
    (op : Silmaril.Wasm.IntBinOp) (x y : BitVec t.width) :
    Applies (simEnv10 B) "binop_" [.val (numTypeV (.int t)), .val (intBinOpV op), .val (bvV x),
      .val (bvV y)] (.list ((ibinop_ t.width op x y).toList.map bvV)) := by
  refine ⟨_, _, _, findDef_binop10 B, Or.inl ?_⟩
  have hN : NumEnv10 (simEnv10 B) := numEnv10_simEnv10 B
  have hD : DivEnv10 (simEnv10 B) := divEnv10_simEnv10 hB
  have ha := evalArgs_bin10 (B := B) (.int t) (K := "Inn") (x₁ := "iN_1") (x₂ := "iN_2")
    (c₁ := bvV x) (c₂ := bvV y) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (t₁ := .varT "Inn" []) (t₂ := .varT "valtype" [])
  cases op <;> skip10
  · exact hitBin10 (hN.callDef_iadd rfl ha)
  · exact hitBin10 (hN.callDef_isub rfl ha)
  · exact hitBin10 (hN.callDef_imul rfl ha)
  · exact hitDivRem10 (hD.callDef_idiv t _ x y rfl (evalArgs_sx10 t))
  · exact hitDivRem10 (hD.callDef_irem t _ x y rfl (evalArgs_sx10 t))
  · exact hitBin10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_iand _ x y))
  · exact hitBin10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_ior _ x y))
  · exact hitBin10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_ixor _ x y))
  · exact hitBin10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl (evalArgs_shl10 t x y)
      (Sim.IntNumeric.intCall_ishl _ x y))
  · exact hitBin10s (callDef_prim10 hB ⟨_, _, rfl⟩ rfl (evalArgs_shr10 t _ x y)
      (Sim.IntNumeric.intCall_ishr _ _ x y))
  · exact hitBin10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_irotl _ x y))
  · exact hitBin10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_irotr _ x y))

set_option maxRecDepth 100000 in
/-- **`$unop_` at an integer type is Core's `intUnOp`**, at the three 1.0 operators. -/
theorem applies_unop_int10 (hB : IntB B) (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.V1.IntUnOp)
    (x : BitVec t.width) :
    Applies (simEnv10 B) "unop_" [.val (numTypeV (.int t)), .val (intUnOpV op), .val (bvV x)]
      (.list [bvV (intUnOp t op.toCore x)]) := by
  refine ⟨_, _, _, findDef_unop10 B, Or.inl ?_⟩
  have ha := evalArgs_un10 (B := B) (.int t) (K := "Inn") (x := "iN") (c := bvV x) (by decide)
    (by decide) (by decide)
    (t₁ := .varT "Inn" []) (t₂ := .varT "valtype" [])
  cases op <;> skip10
  · exact hitUn10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_iclz _ x))
  · exact hitUn10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_ictz _ x))
  · exact hitUn10 (callDef_prim10 hB ⟨_, _, rfl⟩ rfl ha (Sim.IntNumeric.intCall_ipopcnt _ x))

set_option maxRecDepth 100000 in
/-- **`$testop_` at an integer type is Core's `intTestOp`.** -/
theorem applies_testop_int10 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntTestOp)
    (x : BitVec t.width) :
    Applies (simEnv10 B) "testop_" [.val (numTypeV (.int t)), .val (intTestOpV op), .val (bvV x)]
      (bvV (intTestOp t op x)) := by
  refine ⟨_, _, _, findDef_testop10 B, Or.inl ?_⟩
  rw [← itestop_agree]
  cases op
  exact tryClauses_hit (matchArgs_un10 (by decide) (by decide) (argSubOk_inn_int10 t)) premsHold_nil
    (evalExp_callE_iff.2 ((numEnv10_simEnv10 B).callDef_ieqz rfl
      (evalArgs_un10 (.int t) (by decide) (by decide) (by decide))))

set_option maxRecDepth 100000 in
/-- **`$relop_` at an integer type is Core's `intRelOp`.** -/
theorem applies_relop_int10 (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntRelOp)
    (x y : BitVec t.width) :
    Applies (simEnv10 B) "relop_" [.val (numTypeV (.int t)), .val (intRelOpV op), .val (bvV x),
      .val (bvV y)] (bvV (intRelOp t op x y)) := by
  refine ⟨_, _, _, findDef_relop10 B, Or.inl ?_⟩
  have hs : argSubOk (simEnv10 B) VarEnv.empty innPat10' (numTypeV (.int t)) = true :=
    argSubOk_inn_int10 t
  have hN : NumEnv10 (simEnv10 B) := numEnv10_simEnv10 B
  have hm := matchArgs_bin10 (B := B) (K := "Inn") (x₁ := "iN_1") (x₂ := "iN_2") (op := "EQ")
    (c₁ := bvV x) (c₂ := bvV y) (by decide) (by decide) (by decide) (by decide) (by decide) hs
  have ha := evalArgs_bin10 (B := B) (.int t) (K := "Inn") (x₁ := "iN_1") (x₂ := "iN_2")
    (c₁ := bvV x) (c₂ := bvV y) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (t₁ := .varT "Inn" []) (t₂ := .varT "valtype" [])
  rw [← irelop_agree]
  have hw : 0 < t.width := by cases t <;> decide
  cases op with
  | eq => exact tryClauses_hit hm premsHold_nil (evalExp_callE_iff.2 (hN.callDef_ieq rfl ha))
  | ne =>
      skip10
      exact tryClauses_hit (matchArgs_bin10 (K := "Inn") (x₁ := "iN_1") (x₂ := "iN_2")
        (by decide) (by decide) (by decide) (by decide) (by decide) hs)
        premsHold_nil (evalExp_callE_iff.2 (hN.callDef_ine rfl ha))
  | lt s =>
      skip10
      exact tryClauses_hit (matchArgs_sx10 hs) premsHold_nil
        (evalExp_callE_iff.2 (hN.callDef_ilt rfl (evalArgs_sx10 t) hw))
  | gt s =>
      skip10
      exact tryClauses_hit (matchArgs_sx10 hs) premsHold_nil
        (evalExp_callE_iff.2 (hN.callDef_igt rfl (evalArgs_sx10 t) hw))
  | le s =>
      skip10
      exact tryClauses_hit (matchArgs_sx10 hs) premsHold_nil
        (evalExp_callE_iff.2 (hN.callDef_ile rfl (evalArgs_sx10 t) hw))
  | ge s =>
      skip10
      exact tryClauses_hit (matchArgs_sx10 hs) premsHold_nil
        (evalExp_callE_iff.2 (hN.callDef_ige rfl (evalArgs_sx10 t) hw))

/-! ## The float dispatchers -/

/-- The one-operand `Fnn` clause for the opcode `o` fires and calls its primitive. -/
theorem hitFUn10 {P : Profile} (hB : FloatB P B) {x : IL.Id} (hx : NoClauses (simEnv10 B) x)
    {o : MixopS} {q : List Param} {cs : List Clause} {t : Silmaril.Wasm.FloatType} {a v : Value}
    (hc : floatCall P x [.val (natV t.width), .val a] = some v) :
    TryClauses (simEnv10 B) (.defD q [.expA fnnPat10, .expA (.caseE o (.tupE [])),
        .expA (.varE "fN")]
      (.callE x [.expA (.callE "size" [.expA fnnPat10]), .expA (.varE "fN")]) [] :: cs)
      [.val (numTypeV (.float t)), .val (.case o (.tuple [])), .val a] v :=
  tryClauses_hit (matchArgs_un10 (by decide) (by decide) (argSubOk_fnn_float10 t)) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim10 hB hx rfl
      (evalArgs_un10 (.float t) (by decide) (by decide) (by decide)) hc))

/-- The two-operand `Fnn` clause for the opcode `o` fires and calls its primitive. -/
theorem hitFBin10 {P : Profile} (hB : FloatB P B) {x : IL.Id} (hx : NoClauses (simEnv10 B) x)
    {o : MixopS} {q : List Param} {cs : List Clause} {t : Silmaril.Wasm.FloatType} {a b v : Value}
    (hc : floatCall P x [.val (natV t.width), .val a, .val b] = some v) :
    TryClauses (simEnv10 B) (.defD q
      [.expA fnnPat10, .expA (.caseE o (.tupE [])), .expA (.varE "fN_1"), .expA (.varE "fN_2")]
      (.callE x [.expA (.callE "size" [.expA fnnPat10]), .expA (.varE "fN_1"),
        .expA (.varE "fN_2")]) [] :: cs)
      [.val (numTypeV (.float t)), .val (.case o (.tuple [])), .val a, .val b] v :=
  tryClauses_hit (matchArgs_bin10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (argSubOk_fnn_float10 t))
    premsHold_nil (evalExp_callE_iff.2 (callDef_floatPrim10 hB hx rfl
      (evalArgs_bin10 (.float t) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)) hc))

set_option maxRecDepth 100000 in
/-- **`$unop_(Fnn, op, fN)`** is the list of every result the profile allows. -/
theorem applies_unop_float10 {P : Profile} (hB : FloatB P B) (t : Silmaril.Wasm.FloatType)
    (op : Silmaril.Wasm.FloatUnOp) (x : BitVec t.width) :
    Applies (simEnv10 B) "unop_" [.val (numTypeV (.float t)), .val (floatUnOpV op),
      .val (Sim.floatV t x)] (unRes P t op x) := by
  refine ⟨_, _, _, findDef_unop10 B, Or.inl ?_⟩
  have hc := Sim.Floats.floatCall_un P t op x
  cases op <;> (skip10; exact hitFUn10 hB ⟨_, _, rfl⟩ hc)

set_option maxRecDepth 100000 in
/-- **`$binop_(Fnn, op, fN_1, fN_2)`** is the list of every result the profile allows. -/
theorem applies_binop_float10 {P : Profile} (hB : FloatB P B) (t : Silmaril.Wasm.FloatType)
    (op : Silmaril.Wasm.FloatBinOp) (x y : BitVec t.width) :
    Applies (simEnv10 B) "binop_" [.val (numTypeV (.float t)), .val (floatBinOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (binRes P t op x y) := by
  refine ⟨_, _, _, findDef_binop10 B, Or.inl ?_⟩
  have hc := Sim.Floats.floatCall_bin P t op x y
  cases op <;> (skip10; exact hitFBin10 hB ⟨_, _, rfl⟩ hc)

set_option maxRecDepth 100000 in
/-- **`$relop_(Fnn, op, fN_1, fN_2)`** is Core's comparison. -/
theorem applies_relop_float10 {P : Profile} (hB : FloatB P B) (t : Silmaril.Wasm.FloatType)
    (op : Silmaril.Wasm.FloatRelOp) (x y : BitVec t.width) :
    Applies (simEnv10 B) "relop_" [.val (numTypeV (.float t)), .val (floatRelOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (Sim.Vec.i32NV (floatRelOp t op x y)) := by
  refine ⟨_, _, _, findDef_relop10 B, Or.inl ?_⟩
  have hc := Sim.Floats.floatCall_rel P t op x y
  cases op <;> (skip10; exact hitFBin10 hB ⟨_, _, rfl⟩ hc)

end Silmaril.Wasm.SpecTec.Sim10.Whole
