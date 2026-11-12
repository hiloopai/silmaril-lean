module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumEnv
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.NumericsCore
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Ops
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Dispatch
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.Concatn

/-!
# The wasm-2.0 numerics: lookups and the shared clause machinery

What the 2.0 dispatchers `$unop_`, `$binop_`, `$testop_`, `$relop_` (`Original.d182`, `d202`,
`d204`, `d217`) need from `simEnv20 B`, each a kernel `rfl` against the generated script:

* `numEnvCore_simEnv20`: the 24 definitions of `Equiv.NumEnvCore` (`Equiv/NumericsCore.lean`
  restates the `Equiv.callDef_*` lemmas over them as `Equiv.NumEnvCore.callDef_*`), so the
  shared integer library applies to the 2.0 script as it stands;
* `$size` (`d82`, over `valtype`, five clauses) and `$sizenn` (`d88`, which reaches `$size`
  through `nt <: valtype`), evaluated at every number type (`callDef_size20`,
  `callDef_sizenn20`);
* `$list_` (`d8`), the option-to-list conversion 2.0's `DIV`/`REM` clauses call where 3.0 writes
  a lift;
* the clause-less (`hint(builtin)`) primitives, answered by `B` through `IntB`
  (`callDef_prim20`) or `Floats.FloatB` (`callDef_floatPrim20`).

The variable names of 2.0's clauses differ from 3.0's (`iN`, `iN_1`, `iN_2`, `fN`, `fN_1`, `fN_2`
for `i`, `i_1`, `i_2`, `f`, `f_1`, `f_2`), so the scopes and matches are restated here with the
2.0 names (`scope1'`, `scope2'`, `scope2s'`, `fscope1'`, `fscope2'`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB intCall NoClauses defOf matchArg_InnPat)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d8 Original.d82 Original.d88 Original.d182
  Original.d202 Original.d204 Original.d217)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable (B : Builtins)

set_option maxRecDepth 100000 in
/-- **The 24 shared definitions of the integer library are wasm-2.0's**, so every
`Equiv.callDef_*` lemma except `callDef_iextend` applies to `simEnv20 B`. -/
theorem numEnvCore_simEnv20 : Equiv.NumEnvCore (simEnv20 B) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_size20 : (simEnv20 B).findDef? "size" = defOf Original.d82 := rfl

set_option maxRecDepth 100000 in
theorem findDef_sizenn20 : (simEnv20 B).findDef? "sizenn" = defOf Original.d88 := rfl

set_option maxRecDepth 100000 in
theorem findDef_list20 : (simEnv20 B).findDef? "list_" = defOf Original.d8 := rfl

set_option maxRecDepth 100000 in
theorem findDef_unop20 : (simEnv20 B).findDef? "unop_" = defOf Original.d182 := rfl

set_option maxRecDepth 100000 in
theorem findDef_binop20 : (simEnv20 B).findDef? "binop_" = defOf Original.d202 := rfl

set_option maxRecDepth 100000 in
theorem findDef_testop20 : (simEnv20 B).findDef? "testop_" = defOf Original.d204 := rfl

set_option maxRecDepth 100000 in
theorem findDef_relop20 : (simEnv20 B).findDef? "relop_" = defOf Original.d217 := rfl

set_option maxRecDepth 100000 in
/-- `X` is not a type of the 2.0 script, so `$list_`'s type parameter binds. -/
theorem memTyp_X20 : (simEnv20 B).memTyp "X" = false := rfl

variable {B}

/-! ## `$size`, `$sizenn` -/

set_option maxRecDepth 100000 in
/-- `$size(nt)` is the width, at every number type. -/
theorem callDef_size20 (t : Silmaril.Wasm.NumType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "size" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (numTypeV t)]) :
    CallDef (simEnv20 B) ρ "size" args (natV t.width) := by
  refine callDef_of_tryClauses hρ (findDef_size20 B) ha ?_
  rcases t with (_ | _) | (_ | _) <;>
  · repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) ?_)
    exact tryClauses_hit (ρ₀ := VarEnv.empty)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
      premsHold_nil evalExp_num

/-- `$sizenn(nt)` is the width, through `$size(nt <: valtype)`. -/
theorem callDef_sizenn20 (t : Silmaril.Wasm.NumType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "sizenn" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (numTypeV t)]) :
    CallDef (simEnv20 B) ρ "sizenn" args (natV t.width) := by
  refine callDef_of_tryClauses hρ (findDef_sizenn20 B) ha ?_
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" (numTypeV t))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_size20 t rfl
      (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp)))
        Equiv.evalArgs_nil)))

/-- `$sizenn(X)` as the dispatcher clauses write it, `X` bound to the number type. -/
theorem evalExp_sizenn20 (t : Silmaril.Wasm.NumType) {ρ : VarEnv} {X : IL.Id} {t₁ t₂ : Typ}
    (hρ : ρ.findDef? "sizenn" = none) (hX : ρ.findVal? X = some (numTypeV t)) :
    EvalExp (simEnv20 B) ρ (.callE "sizenn" [.expA (.subE (.varE X) t₁ t₂)]) (natV t.width) :=
  evalExp_callE_iff.2 (callDef_sizenn20 t hρ
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hX)) Equiv.evalArgs_nil))

/-! ## The `Inn` pattern -/

set_option maxRecDepth 100000 in
/-- An integer type passes the 2.0 `Inn` pattern's subtype test. -/
theorem argSubOk_innPat20 (t : Silmaril.Wasm.IntType) :
    argSubOk (simEnv20 B) VarEnv.empty
      (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])) (numTypeV (.int t)) = true := by
  cases t <;> rfl

/-! ## Primitives -/

/-- A primitive with no clause, answered by `B` through `IntB`. -/
theorem callDef_prim20 (hB : IntB B) {x : IL.Id} (hx : NoClauses (simEnv20 B) x) {ρ : VarEnv}
    {args : List Arg} {ws : List ArgV} {v : Value} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv20 B) ρ args ws) (hc : intCall x ws = some v) :
    CallDef (simEnv20 B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ hc)

/-- A primitive with no clause, answered by `B` through `FloatB`. -/
theorem callDef_floatPrim20 {P : Silmaril.Wasm.Numerics.Profile} (hB : Sim.Floats.FloatB P B)
    {x : IL.Id} (hx : NoClauses (simEnv20 B) x) {ρ : VarEnv} {args : List Arg} {ws : List ArgV}
    {v : Value} (hρ : ρ.findDef? x = none) (ha : EvalArgs (simEnv20 B) ρ args ws)
    (hc : Sim.Floats.floatCall P x ws = some v) : CallDef (simEnv20 B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ hc)

end Silmaril.Wasm.SpecTec.Sim20.Pure
