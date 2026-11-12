module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestTable
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Bounds

/-!
# A typed wasm-2.0 `CONST I32 (% k)` has `k < 2 ^ 32`

Several `Step_read` rules of the wasm-2.0 script put a natural computed from the state into an
`i32` constant: `table.size` and `memory.size` (the count), and the `-succ`, `-le` and `-gt` rules
of `table.fill/copy/init` and `memory.fill/copy/init` (`i + 1`, `n - 1`, `j + n - 1`). V2's result
is `BitVec.ofNat 32 _`, so the two agree only below `2 ^ 32`. V2's stores do not bound the length
of a table, but the backward obligations of `Task.wholeStepBwdW` give the typing of the result
`instr*`, and an IL-typed `CONST I32 (% k)` has `k < 2 ^ 32` (`lt_of_typed_constI32`).

The inversion runs through the 2.0 definitions, each found by kernel `rfl`:
`instr`'s case `CONST (numtype, num_(numtype))` (`constCase_of_mem`), `num_(Inn)` (an alias of
`iN($sizenn(Inn))`, `num_i32_inv`), `iN(N)` (an alias of `uN(N)`, `iN_inv_lt20`) and `uN(N)`,
whose premise `i <= 2^N - 1` is evaluated to `false` beyond the bound (`uN_inv_lt20`). The `uN`
steps are round 7's `MemSimd.uN_inv_lt`, ported from `simEnv B` to `simEnv20 B` (2.0's `uN` is
byte-identical to 3.0's, `uNCases20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.V2.Execution (constI32)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `uN(N)` and `iN(N)` -/

set_option maxRecDepth 100000 in
/-- 2.0's `uN` has the one case of 3.0's. -/
theorem uNCases20 : Sim.IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d17 0 =
    [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr Sim.ConfigOk.uNPrem]] := rfl

/-- The scope in which `uN(N)`'s premise is checked for the numeral `n`. -/
noncomputable def uNScope20 (N n : Nat) : VarEnv :=
  caseScope (VarEnv.empty.bindVal "N" (.num (.natN N)))
    (.tupT [.mk "i" (.numT .natT)]) (.tuple [.num (.natN n)])

theorem uNScope20_N (N n : Nat) : (uNScope20 N n).findVal? "N" = some (Equiv.natV N) := by
  simp [uNScope20, caseScope, typBinds, Equiv.natV]

theorem uNScope20_i (N n : Nat) : (uNScope20 N n).findVal? "i" = some (.num (.natN n)) := by
  simp [uNScope20, caseScope, typBinds]

/-- **`uN(N)`'s premise is false beyond the bound.** -/
theorem evalExp_uNPrem20_false {N n : Nat} (hn : 2 ^ N ≤ n) :
    EvalExp (simEnv20 B) (uNScope20 N n) Sim.ConfigOk.uNPrem (.bool false) := by
  have hpow : EvalExp (simEnv20 B) (uNScope20 N n)
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (Equiv.natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (uNScope20_N N n)
  have hsub : EvalExp (simEnv20 B) (uNScope20 N n) (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  have hge : EvalExp (simEnv20 B) (uNScope20 N n)
      (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0))) (.bool true) :=
    evalExp_cmpNum (evalExp_var (uNScope20_i N n)) evalExp_num (by simp [Num.cmp])
  have hcmp : Num.cmp .leOp (.natN n) (.natN ((((2 ^ N : Nat) : Int) - 1).toNat)) =
      some false := by
    simp only [Num.cmp, Option.some.injEq, decide_eq_false_iff_not]
    have := Nat.one_le_two_pow (n := N)
    omega
  exact Sim.IntNumeric.evalExp_and hge (evalExp_cmpNum (evalExp_var (uNScope20_i N n)) hk hcmp)

/-- **A one-instance type family of `simEnv20 B`, inverted.** -/
theorem hasTypDef_of_oneInst20 {x p : IL.Id} {ps qs : List Param} {dt : DefTyp} {ρ : VarEnv}
    {e : Exp} {u v : Value}
    (htd : (simEnv20 B).findTyp? x = some (ps, [.instD qs [.expA (.varE p)] dt]))
    (he : EvalExp (simEnv20 B) ρ e u) (h : HasTyp (simEnv20 B) ρ (.varT x [.expA e]) v) :
    HasTypDef (simEnv20 B) (VarEnv.empty.bindVal p u) dt v := by
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  have etd : td = (ps, [.instD qs [.expA (.varE p)] dt]) := Option.some.inj (htd'.symm.trans htd)
  obtain ⟨u', hu', hws⟩ := evalArgs_expA_iff.1 hargs
  have eu : u' = u := EvalExp.unique hu' he
  subst etd hws eu
  exact Sim.IntNumeric.hasTypInsts_head_inv
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) hi

/-- **The one case of 2.0's `uN(N)`, inverted.** -/
theorem uN_case_inv20 {N : Nat} {v : Value}
    (hd : HasTypDef (simEnv20 B) (VarEnv.empty.bindVal "N" (.num (.natN N)))
      (.variantT (Sim.IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d17 0)) v) :
    ∃ n, v = pctV n ∧ PremsOk (simEnv20 B) (uNScope20 N n) [.ifPr Sim.ConfigOk.uNPrem] := by
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
  rw [uNCases20] at hc
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

/-- **Inversion of 2.0's `uN(N)`**: a typed value is a numeral below `2 ^ N`. -/
theorem uN_inv_lt20 {ρ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv20 B) ρ e (.num (.natN N)))
    (h : HasTyp (simEnv20 B) ρ (.varT "uN" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := Pure.findTyp_uN20 (B := B)
  obtain ⟨n, hv, hp⟩ := uN_case_inv20 (hasTypDef_of_oneInst20 htd he h)
  have htrue : EvalExp (simEnv20 B) (uNScope20 N n) Sim.ConfigOk.uNPrem (.bool true) :=
    Sim.ConfigOk.evalExp_of_premsOk_if hp
  refine ⟨n, hv, Nat.lt_of_not_le fun hn => ?_⟩
  cases htrue.unique (evalExp_uNPrem20_false hn)

/-- **Inversion of 2.0's `iN(N)`**, through `uN(N)`. -/
theorem iN_inv_lt20 {ρ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv20 B) ρ e (.num (.natN N)))
    (h : HasTyp (simEnv20 B) ρ (.varT "iN" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := Pure.findTyp_iN20 (B := B)
  exact uN_inv_lt20 (evalExp_var (by simp))
    (hasTypDef_aliasT_iff.1 (hasTypDef_of_oneInst20 htd he h))

/-- **Inversion of 2.0's `num_(I32)`**, through `iN($sizenn(I32))`. -/
theorem num_i32_inv {ρ : VarEnv} {e : Exp} {v : Value}
    (he : EvalExp (simEnv20 B) ρ e (caseNilV "I32"))
    (h : HasTyp (simEnv20 B) ρ (.varT "num_" [.expA e]) v) : ∃ n, v = pctV n ∧ n < 2 ^ 32 := by
  obtain ⟨ps, qs, qs', htd⟩ := Pure.findTyp_num20 (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  have etd := Option.some.inj (htd'.symm.trans htd)
  subst etd
  obtain ⟨u', hu', rfl⟩ := evalArgs_expA_iff.1 hargs
  have eu : u' = numTypeV (.int .i32) := EvalExp.unique hu' he
  subst eu
  have hd := Sim.IntNumeric.hasTypInsts_head_inv (matchArgs_cons
    (Pure.matchArg_subVar20 (by simp) (Pure.argSubOk_inn_int20 .i32)) matchArgs_nil) hi
  exact iN_inv_lt20 (Pure.evalExp_sizenn20 (.int .i32) rfl (by simp)) (hasTypDef_aliasT_iff.1 hd)

/-! ## `instr`'s `CONST` -/

/-- `instr`'s case `CONST (numtype, num_(numtype))`. -/
def constCase20 : TypCase :=
  .mk "CONST" (.tupT [.mk "numtype" (.varT "numtype" []),
    .mk "_" (.varT "num_" [.expA (.varE "numtype")])]) [] []

set_option maxRecDepth 8000000 in
/-- `CONST` is the head of exactly one case of 2.0's `instr`. -/
theorem constCases20 : instrCases20.filter (fun c => caseHead c == "CONST") = [constCase20] := by
  rfl

/-- The case of `instr` named `CONST`. -/
theorem constCase_of_mem {t : Typ} {qs : List Param} {prems : List Prem}
    (h : TypCase.mk "CONST" t qs prems ∈ instrCases20) : TypCase.mk "CONST" t qs prems = constCase20 := by
  have hm : TypCase.mk "CONST" t qs prems ∈ instrCases20.filter (fun c => caseHead c == "CONST") :=
    List.mem_filter.2 ⟨h, by simp [caseHead]⟩
  rw [constCases20] at hm
  exact List.mem_singleton.1 hm

/-- **The case `CONST` of `instr`, inverted**: the payload is typed `num_(numtype)` with
`numtype` bound to the first component. -/
theorem num_of_constCase {σ : VarEnv} {k : Nat}
    (hc : HasTypCase (simEnv20 B) σ instrCases20 "CONST" (.tuple [caseNilV "I32", pctV k])) :
    ∃ ρ' : VarEnv, ρ'.findVal? "numtype" = some (caseNilV "I32") ∧
      HasTyp (simEnv20 B) ρ' (.varT "num_" [.expA (.varE "numtype")]) (pctV k) := by
  obtain ⟨t, qs, prems, hm, ht, -⟩ := hasTypCase_mem hc
  have e : TypCase.mk "CONST" t qs prems = constCase20 := constCase_of_mem hm
  have et : t = .tupT [.mk "numtype" (.varT "numtype" []),
      .mk "_" (.varT "num_" [.expA (.varE "numtype")])] := by
    simp only [constCase20, TypCase.mk.injEq, true_and] at e
    exact e.1
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (et ▸ ht)
  have evs : vs = [caseNilV "I32", pctV k] := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 (evs ▸ htup)
  obtain ⟨ey, eys⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨ey', -⟩ := List.cons.inj (eys.trans hys')
  refine ⟨σ.bindVal "numtype" y, by simp [← ey], ?_⟩
  rw [ey']
  exact hy'

/-- **A typed 2.0 `instr` `CONST I32 (% k)` has `k < 2 ^ 32`.** -/
theorem lt_of_hasTyp_constI32 {ρ : VarEnv} (hρ : ValsOnly ρ) {k : Nat}
    (h : HasTyp (simEnv20 B) ρ (.varT "instr" [])
      (.case "CONST" (.tuple [caseNilV "I32", pctV k]))) : k < 2 ^ 32 := by
  have hl : localTyp? ρ "instr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  have etd : td = ([], [.instD [] [] (.variantT instrCases20)]) :=
    (Option.some.inj ((findTyp_instr20 B).symm.trans htd)).symm
  rcases hasTypInsts_cons_inv (etd ▸ hi) with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    have eow : op = "CONST" ∧ w = .tuple [caseNilV "I32", pctV k] := by
      simpa only [Value.case.injEq] using he.symm
    obtain ⟨ρ', fnt, hnum⟩ := num_of_constCase (eow.1 ▸ eow.2 ▸ hc)
    obtain ⟨n, hn, hlt⟩ := num_i32_inv (evalExp_var fnt) hnum
    have e' : k = n := by simpa [pctV] using hn
    exact e' ▸ hlt
  · exact absurd hrest not_hasTypInsts_nil

/-- **Every `CONST I32 (% k)` of a typed 2.0 `instr*` has `k < 2 ^ 32`.** -/
theorem lt_of_typed_constI32 {l : List Value} (h : TypedSome (simEnv20 B) instrsT20 (.list l))
    {k : Nat} (hm : Value.case "CONST" (.tuple [caseNilV "I32", pctV k]) ∈ l) : k < 2 ^ 32 := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 ht
  obtain rfl := (Value.list.inj hvs).symm
  exact lt_of_hasTyp_constI32 hρ (hasTypList_iff.1 hl _ hm)

/-- The image of `i32.const (BitVec.ofNat 32 k)` below the bound. -/
theorem adminToV_constI32_ofNat {k : Nat} (hk : k < 2 ^ 32) :
    adminToV (constI32 (BitVec.ofNat 32 k)) = .case "CONST" (.tuple [caseNilV "I32", pctV k]) := by
  rw [adminToV_constI32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

end Silmaril.Wasm.SpecTec.Sim20.Whole
