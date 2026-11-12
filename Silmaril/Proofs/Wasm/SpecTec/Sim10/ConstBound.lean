module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble7
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeConstBound

/-!
# A typed wasm-1.0 `CONST I32 (% k)` has `k < 2 ^ 32`

`Step_read/memory.size` of 1.0 puts the page count `n` into `CONST I32 (% n)`, and V1's result is
`i32.const (BitVec.ofNat 32 n)`. The two agree only below `2 ^ 32`. As for 2.0
(`Sim20.Whole.lt_of_typed_constI32`), the bound comes from the IL typing of the result, which the
backward obligation provides: a typed 1.0 `admininstr` `CONST I32 (% k)` has `k < 2 ^ 32`
(`lt_of_typed_constI32_10`).

The inversion runs through the 1.0 definitions, each found by kernel `rfl`: `admininstr`'s case
`CONST (valtype, val_(valtype))` (`constCase_of_mem10`), `val_(Inn)` (an alias of
`iN($size(Inn))`, `val_i32_inv10`), `iN(N)` (an alias of `uN(N)`) and `uN(N)`, whose premise
`i <= 2^N - 1` is false beyond the bound. 1.0's `uN` has 2.0's one case and premise
(`uNCases10`), so `Sim20.Whole.evalExp_uNPrem20_false`'s argument carries over at `simEnv10`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)
open Silmaril.Wasm.SpecTec.Sim20.Whole (uNScope20 uNScope20_N uNScope20_i caseHead)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `uN(N)` and `iN(N)` in 1.0 -/

set_option maxRecDepth 100000 in
/-- 1.0's `uN` has the one case of 2.0's. -/
theorem uNCases10 : ∃ ps qs, (simEnv10 B).findTyp? "uN" = some (ps, [.instD qs [.expA (.varE "N")]
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr Sim.ConfigOk.uNPrem]])]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_iN10 : ∃ ps qs, (simEnv10 B).findTyp? "iN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.aliasT (.varT "uN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

/-- **`uN(N)`'s premise is false beyond the bound**, at `simEnv10`. -/
theorem evalExp_uNPrem10_false {N n : Nat} (hn : 2 ^ N ≤ n) :
    EvalExp (simEnv10 B) (uNScope20 N n) Sim.ConfigOk.uNPrem (.bool false) := by
  have hpow : EvalExp (simEnv10 B) (uNScope20 N n)
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (Equiv.natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (uNScope20_N N n)
  have hsub : EvalExp (simEnv10 B) (uNScope20 N n) (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  have hge : EvalExp (simEnv10 B) (uNScope20 N n)
      (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0))) (.bool true) :=
    evalExp_cmpNum (evalExp_var (uNScope20_i N n)) evalExp_num (by simp [Num.cmp])
  have hcmp : Num.cmp .leOp (.natN n) (.natN ((((2 ^ N : Nat) : Int) - 1).toNat)) =
      some false := by
    simp only [Num.cmp, Option.some.injEq, decide_eq_false_iff_not]
    have := Nat.one_le_two_pow (n := N)
    omega
  exact Sim.IntNumeric.evalExp_and hge (evalExp_cmpNum (evalExp_var (uNScope20_i N n)) hk hcmp)

/-- **A one-instance type family of `simEnv10 B`, inverted.** -/
theorem hasTypDef_of_oneInst10 {x p : IL.Id} {ps qs : List Param} {dt : DefTyp} {ρ : VarEnv}
    {e : Exp} {u v : Value}
    (htd : (simEnv10 B).findTyp? x = some (ps, [.instD qs [.expA (.varE p)] dt]))
    (he : EvalExp (simEnv10 B) ρ e u) (h : HasTyp (simEnv10 B) ρ (.varT x [.expA e]) v) :
    HasTypDef (simEnv10 B) (VarEnv.empty.bindVal p u) dt v := by
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  have etd : td = (ps, [.instD qs [.expA (.varE p)] dt]) := Option.some.inj (htd'.symm.trans htd)
  obtain ⟨u', hu', hws⟩ := evalArgs_expA_iff.1 hargs
  have eu : u' = u := EvalExp.unique hu' he
  subst etd hws eu
  exact Sim.IntNumeric.hasTypInsts_head_inv
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) hi

/-- **The one case of 1.0's `uN(N)`, inverted.** -/
theorem uN_case_inv10 {N : Nat} {v : Value}
    (hd : HasTypDef (simEnv10 B) (VarEnv.empty.bindVal "N" (.num (.natN N)))
      (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr Sim.ConfigOk.uNPrem]]) v) :
    ∃ n, v = pctV n ∧ PremsOk (simEnv10 B) (uNScope20 N n) [.ifPr Sim.ConfigOk.uNPrem] := by
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
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

/-- **Inversion of 1.0's `uN(N)`**: a typed value is a numeral below `2 ^ N`. -/
theorem uN_inv_lt10 {ρ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv10 B) ρ e (.num (.natN N)))
    (h : HasTyp (simEnv10 B) ρ (.varT "uN" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := uNCases10 (B := B)
  obtain ⟨n, hv, hp⟩ := uN_case_inv10 (hasTypDef_of_oneInst10 htd he h)
  have htrue : EvalExp (simEnv10 B) (uNScope20 N n) Sim.ConfigOk.uNPrem (.bool true) :=
    Sim.ConfigOk.evalExp_of_premsOk_if hp
  refine ⟨n, hv, Nat.lt_of_not_le fun hn => ?_⟩
  cases htrue.unique (evalExp_uNPrem10_false hn)

/-- **Inversion of 1.0's `iN(N)`**, through `uN(N)`. -/
theorem iN_inv_lt10 {ρ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv10 B) ρ e (.num (.natN N)))
    (h : HasTyp (simEnv10 B) ρ (.varT "iN" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := findTyp_iN10 (B := B)
  exact uN_inv_lt10 (evalExp_var (by simp))
    (hasTypDef_aliasT_iff.1 (hasTypDef_of_oneInst10 htd he h))

/-! ## `val_(I32)` -/

/-- `Inn <: valtype`, the pattern of `val_`'s first instance. -/
abbrev innPat10 : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "valtype" [])

set_option maxRecDepth 100000 in
theorem findTyp_val10' : ∃ ps qs rest, (simEnv10 B).findTyp? "val_" = some (ps,
    .instD qs [.expA innPat10] (.aliasT (.varT "iN" [.expA (.callE "size" [.expA innPat10])])) ::
      rest) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem argSubOk_inn_i32_10 :
    argSubOk (simEnv10 B) VarEnv.empty innPat10 (valTypeV (.int .i32)) = true := rfl

/-- **Inversion of 1.0's `val_(I32)`**, through `iN($size(I32))`. -/
theorem val_i32_inv10 {ρ : VarEnv} {e : Exp} {v : Value}
    (he : EvalExp (simEnv10 B) ρ e (caseNilV "I32"))
    (h : HasTyp (simEnv10 B) ρ (.varT "val_" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ 32 := by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_val10' (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  have etd := Option.some.inj (htd'.symm.trans htd)
  subst etd
  obtain ⟨u', hu', rfl⟩ := evalArgs_expA_iff.1 hargs
  have eu : u' = valTypeV (.int .i32) := EvalExp.unique hu' he
  subst eu
  have hd := Sim.IntNumeric.hasTypInsts_head_inv (matchArgs_cons
    (Sim20.Pure.matchArg_subVar20 (by simp) argSubOk_inn_i32_10) matchArgs_nil) hi
  exact iN_inv_lt10 (evalExp_size10 (.int .i32) rfl
    (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp)))) (hasTypDef_aliasT_iff.1 hd)

/-! ## `admininstr`'s `CONST` -/

/-- wasm-1.0's `admininstr` cases. -/
noncomputable def admininstrCases10 : List TypCase :=
  match Silmaril.Wasm.SpecTec.Scripts.Wasm10.Original.d170 with
  | .recD (.typD _ _ [.instD _ _ (.variantT cs)] :: _) => cs
  | _ => []

set_option maxRecDepth 8000000 in
/-- wasm-1.0's `admininstr`, as `simEnv10 B` finds it. -/
theorem findTyp_admininstr10 : (simEnv10 B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT admininstrCases10)]) := rfl

/-- `admininstr`'s case `CONST (valtype, val_(valtype))`. -/
def constCase10 : TypCase :=
  .mk "CONST" (.tupT [.mk "valtype" (.varT "valtype" []),
    .mk "_" (.varT "val_" [.expA (.varE "valtype")])]) [] []

set_option maxRecDepth 8000000 in
/-- `CONST` is the head of exactly one case of 1.0's `admininstr`. -/
theorem constCases10 :
    admininstrCases10.filter (fun c => caseHead c == "CONST") = [constCase10] := by
  rfl

/-- The case of `admininstr` named `CONST`. -/
theorem constCase_of_mem10 {t : Typ} {qs : List Param} {prems : List Prem}
    (h : TypCase.mk "CONST" t qs prems ∈ admininstrCases10) :
    TypCase.mk "CONST" t qs prems = constCase10 := by
  have hm : TypCase.mk "CONST" t qs prems ∈
      admininstrCases10.filter (fun c => caseHead c == "CONST") :=
    List.mem_filter.2 ⟨h, by simp [caseHead]⟩
  rw [constCases10] at hm
  exact List.mem_singleton.1 hm

/-- **The case `CONST` of `admininstr`, inverted**: the payload is typed `val_(valtype)` with
`valtype` bound to the first component. -/
theorem val_of_constCase10 {σ : VarEnv} {k : Nat}
    (hc : HasTypCase (simEnv10 B) σ admininstrCases10 "CONST" (.tuple [caseNilV "I32", pctV k])) :
    ∃ ρ' : VarEnv, ρ'.findVal? "valtype" = some (caseNilV "I32") ∧
      HasTyp (simEnv10 B) ρ' (.varT "val_" [.expA (.varE "valtype")]) (pctV k) := by
  obtain ⟨t, qs, prems, hm, ht, -⟩ := hasTypCase_mem hc
  have e : TypCase.mk "CONST" t qs prems = constCase10 := constCase_of_mem10 hm
  have et : t = .tupT [.mk "valtype" (.varT "valtype" []),
      .mk "_" (.varT "val_" [.expA (.varE "valtype")])] := by
    simp only [constCase10, TypCase.mk.injEq, true_and] at e
    exact e.1
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (et ▸ ht)
  have evs : vs = [caseNilV "I32", pctV k] := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 (evs ▸ htup)
  obtain ⟨ey, eys⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨ey', -⟩ := List.cons.inj (eys.trans hys')
  refine ⟨σ.bindVal "valtype" y, by simp [← ey], ?_⟩
  rw [ey']
  exact hy'

/-- **A typed 1.0 `admininstr` `CONST I32 (% k)` has `k < 2 ^ 32`.** -/
theorem lt_of_hasTyp_constI32_10 {ρ : VarEnv} (hρ : ValsOnly ρ) {k : Nat}
    (h : HasTyp (simEnv10 B) ρ (.varT "admininstr" [])
      (.case "CONST" (.tuple [caseNilV "I32", pctV k]))) : k < 2 ^ 32 := by
  have hl : localTyp? ρ "admininstr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  have etd : td = ([], [.instD [] [] (.variantT admininstrCases10)]) :=
    (Option.some.inj (findTyp_admininstr10.symm.trans htd)).symm
  rcases hasTypInsts_cons_inv (etd ▸ hi) with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    have eow : op = "CONST" ∧ w = .tuple [caseNilV "I32", pctV k] := by
      simpa only [Value.case.injEq] using he.symm
    obtain ⟨ρ', fvt, hval⟩ := val_of_constCase10 (eow.1 ▸ eow.2 ▸ hc)
    obtain ⟨n, hn, hlt⟩ := val_i32_inv10 (evalExp_var fvt) hval
    have e' : k = n := by simpa [pctV] using hn
    exact e' ▸ hlt
  · exact absurd hrest not_hasTypInsts_nil

/-- **Every `CONST I32 (% k)` of a typed 1.0 `admininstr*` has `k < 2 ^ 32`.** -/
theorem lt_of_typed_constI32_10 {l : List Value} (h : TypedSome (simEnv10 B) adminsT (.list l))
    {k : Nat} (hm : Value.case "CONST" (.tuple [caseNilV "I32", pctV k]) ∈ l) : k < 2 ^ 32 := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 ht
  obtain rfl := (Value.list.inj hvs).symm
  exact lt_of_hasTyp_constI32_10 hρ (hasTypList_iff.1 hl _ hm)

end Silmaril.Wasm.SpecTec.Sim10.Whole
