module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadVal
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# Round 7, memory SIMD: `uN(N)` and `vec_(V128)` bound their numerals

The quantifier `c : vec_(V128)` of `Step_read/vload-num-val` (rule 43) is bound only by the
premise `$vbytes_(V128, c) = …`, and `withVBytes` reads only the low 128 bits of `c`. Inverting
the rule therefore needs the range of `c`, which its type gives:

* `uN_inv_lt`: a typed `uN(N)` value is a numeral `%(n)` with `n < 2 ^ N`, at every width `N`
  (round 5's `ConfigOk.lt_of_hasTyp_uN32` is the bound at `N = 32`); the case's premise
  `i <= 2^N - 1` is evaluated to `false` beyond the bound.
* `iN_inv_lt`: the same for `iN(N)`, an alias of `uN(N)`.
* `vec_inv`: a typed `vec_(V128)` value is a numeral below `2 ^ 128`, through
  `vN($vsizenn(V128))` and `uN(128)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d22)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- The scope in which `uN(N)`'s premise is checked for the numeral `n`. -/
noncomputable def uNScopeN (N n : Nat) : VarEnv :=
  caseScope (VarEnv.empty.bindVal "N" (.num (.natN N)))
    (.tupT [.mk "i" (.numT .natT)]) (.tuple [.num (.natN n)])

theorem uNScopeN_N (N n : Nat) : (uNScopeN N n).findVal? "N" = some (Equiv.natV N) := by
  simp [uNScopeN, caseScope, typBinds, Equiv.natV]

theorem uNScopeN_i (N n : Nat) : (uNScopeN N n).findVal? "i" = some (.num (.natN n)) := by
  simp [uNScopeN, caseScope, typBinds]

/-- **`uN(N)`'s premise is false beyond the bound.** -/
theorem evalExp_uNPremN_false {N n : Nat} (hn : 2 ^ N ≤ n) :
    EvalExp (simEnv B) (uNScopeN N n) ConfigOk.uNPrem (.bool false) := by
  have hpow : EvalExp (simEnv B) (uNScopeN N n)
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (Equiv.natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (uNScopeN_N N n)
  have hsub : EvalExp (simEnv B) (uNScopeN N n) (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  have hge : EvalExp (simEnv B) (uNScopeN N n)
      (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0))) (.bool true) :=
    evalExp_cmpNum (evalExp_var (uNScopeN_i N n)) evalExp_num (by simp [Num.cmp])
  have hcmp : Num.cmp .leOp (.natN n) (.natN ((((2 ^ N : Nat) : Int) - 1).toNat)) =
      some false := by
    simp only [Num.cmp, Option.some.injEq, decide_eq_false_iff_not]
    have := Nat.one_le_two_pow (n := N)
    omega
  exact IntNumeric.evalExp_and hge (evalExp_cmpNum (evalExp_var (uNScopeN_i N n)) hk hcmp)

/-- **A one-instance type family, inverted**: a value of `x(e)`, where `x`'s single instance has
the pattern `p` and `e` evaluates to `u`, is a value of the instance's definition with `p := u`. -/
theorem hasTypDef_of_oneInst {x p : IL.Id} {ps : List Param} {qs : List Param} {dt : DefTyp}
    {ρ : VarEnv} {e : Exp} {u v : Value}
    (htd : (simEnv B).findTyp? x = some (ps, [.instD qs [.expA (.varE p)] dt]))
    (he : EvalExp (simEnv B) ρ e u) (h : HasTyp (simEnv B) ρ (.varT x [.expA e]) v) :
    HasTypDef (simEnv B) (VarEnv.empty.bindVal p u) dt v := by
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  have etd : td = (ps, [.instD qs [.expA (.varE p)] dt]) := Option.some.inj (htd'.symm.trans htd)
  obtain ⟨u', hu', hws⟩ := evalArgs_expA_iff.1 hargs
  have eu : u' = u := EvalExp.unique hu' he
  subst etd hws eu
  exact IntNumeric.hasTypInsts_head_inv
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) hi

/-- **The one case of `uN(N)`, inverted**: a numeral `%(n)` with its premise checked at `N`. -/
theorem uN_case_inv {N : Nat} {v : Value}
    (hd : HasTypDef (simEnv B) (VarEnv.empty.bindVal "N" (.num (.natN N)))
      (.variantT (IntNumeric.instCases Original.d22 0)) v) :
    ∃ n, v = pctV n ∧ PremsOk (simEnv B) (uNScopeN N n) [.ifPr ConfigOk.uNPrem] := by
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
  rw [ConfigOk.uNCases] at hc
  by_cases hop : op = "%"
  · subst hop
    obtain ⟨ht, hp⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    obtain ⟨vs, rfl, hvs⟩ := hasTyp_tupT_iff.1 ht
    obtain ⟨y, ys, rfl, hy, hys⟩ := hasTypTup_cons_iff.1 hvs
    obtain rfl := hasTypTup_nil_iff.1 hys
    obtain ⟨m, rfl, hm⟩ := hasTyp_numT_iff.1 hy
    cases m with
    | natN n => exact ⟨n, rfl, hp⟩
    | _ => simp [Num.toTyp, Num.subTyp] at hm
  · exact absurd ((hasTypCase_cons_miss_iff (Ne.symm hop)).1 hc) not_hasTypCase_nil

/-- **Inversion of `uN(N)`**: a typed value is a numeral `%(n)` below `2 ^ N`, for the width `N`
the argument evaluates to. -/
theorem uN_inv_lt {ρ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv B) ρ e (.num (.natN N)))
    (h : HasTyp (simEnv B) ρ (.varT "uN" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_uN (B := B)
  obtain ⟨n, hv, hp⟩ := uN_case_inv (hasTypDef_of_oneInst htd he h)
  have htrue : EvalExp (simEnv B) (uNScopeN N n) ConfigOk.uNPrem (.bool true) :=
    ConfigOk.evalExp_of_premsOk_if hp
  refine ⟨n, hv, Nat.lt_of_not_le fun hn => ?_⟩
  cases htrue.unique (evalExp_uNPremN_false hn)

/-- **Inversion of `iN(N)`**, through `uN(N)`: a typed value is a numeral below `2 ^ N`. -/
theorem iN_inv_lt {ρ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv B) ρ e (.num (.natN N)))
    (h : HasTyp (simEnv B) ρ (.varT "iN" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_iN (B := B)
  exact uN_inv_lt (evalExp_var (by simp))
    (hasTypDef_aliasT_iff.1 (hasTypDef_of_oneInst htd he h))

/-- **Inversion of `vec_(V128)`**: a typed value is a numeral `%(n)` below `2 ^ 128`, through
`vN($vsizenn(V128))` and `uN(128)`. -/
theorem vec_inv {ρ : VarEnv} {e : Exp} {v : Value}
    (he : EvalExp (simEnv B) ρ e (caseNilV "V128"))
    (h : HasTyp (simEnv B) ρ (.varT "vec_" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ 128 := by
  obtain ⟨ps, qs, htd⟩ := Typing.findTyp_vec (B := B)
  obtain ⟨ps', qs', htd₂⟩ := Typing.findTyp_vN (B := B)
  have hvN := hasTypDef_aliasT_iff.1 (hasTypDef_of_oneInst htd he h)
  have h128 : EvalExp (simEnv B) (VarEnv.empty.bindVal "Vnn" (caseNilV "V128"))
      (.callE "vsizenn" [.expA (.varE "Vnn")]) (Equiv.natV 128) :=
    evalExp_callE_iff.2 (Typing.callDef_vsizenn rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil))
  have huN := hasTypDef_aliasT_iff.1 (hasTypDef_of_oneInst htd₂ h128 hvN)
  exact uN_inv_lt (evalExp_var (by simp [Equiv.natV])) huN

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
