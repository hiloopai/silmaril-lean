module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestSize

/-!
# `table.fill` backwards: reading the `otherwise` premise back

`Step_read` 12–14 of the wasm-2.0 script are `table.fill-trap` (`i + n > |$table(z, x).REFS|`, to
`TRAP`), `table.fill-zero` (`otherwise`, `n = 0`, to `ε`) and `table.fill-succ` (`otherwise`, one
element per step). Rule 12 is dead (its `TRAP` is not an `instr`), but its body is what the
`otherwise` premises of 13 and 14 deny.

* `otherwise_absurd`: rule `k`'s `otherwise` refutes every body of an earlier rule `j` at the same
  left-hand side, whatever its right-hand side.
* `body_ifRule`: the body of a one-`if` rule, from its quantifiers, conclusion and premise; with
  them, a firing `-zero` or `-succ` rule gives the bound `i + n ≤ |$table(z, x).REFS|`
  (`fill_bound`): otherwise the `-trap` body holds at `TRAP`.
* `-succ`'s right-hand side has `CONST I32 (% $(n - 1))`, an `int` subtraction converted back to
  `nat`, which has no value at `n = 0` (`pred_inv`); so `n ≠ 0`. The new constants `i + 1` and
  `n - 1` are below `2 ^ 32` by the typing of the result (`lt_of_typed_constI32`).

This discharges `Step_read` 13 and 14 (`bwdRead_tableFillZero`, `bwdRead_tableFillSucc`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW RuleBody DDerives otherwise otherwiseAt noElse
  evalExp_tup2 evalExp_case evalExp_list1)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Generic: the `otherwise` premise, read back -/

/-- **Rule `k`'s `otherwise` refutes the body of an earlier rule `j` at the same left-hand side.** -/
theorem otherwise_absurd {env : Env} {x : IL.Id} {k j : Nat} {r : Rule} {a b b' : Value}
    (hR : HasRuleAt env x "%~>%" j r) (hj : j < k) (h : otherwise env x [] k (.tuple [a, b]))
    (hb : RuleBody env (DDerives env noElse) (otherwiseAt env x [] j (.tuple [a, b'])) [] []
      "%~>%" r (.tuple [a, b'])) : False := by
  obtain ⟨ps, t, rules, hrel, rfl, hr⟩ := hR
  have h' : otherwiseAt env x [] k (.tuple [a, b]) := h
  rw [otherwiseAt] at h'
  exact h' j hj [] "%~>%" t rules r hrel hr _ ⟨a, b, b', rfl, rfl⟩ hb

/-- **The body of a rule with one `if` premise.** -/
theorem body_ifRule {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {nm : IL.Id}
    {qs : List Param} {c e : Exp} {σ : List (IL.Id × Value)} {v : Value}
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (hc : EvalExp env (VarEnv.empty.bindVals σ) c v)
    (hp : EvalExp env (VarEnv.empty.bindVals σ) e (.bool true)) :
    RuleBody env D els [] [] "%~>%" (.ruleD nm qs "%~>%" c [.ifPr e]) v := by
  refine ⟨rfl, VarEnv.empty, σ, rfl, hq, hc, fun pr hpr => ?_⟩
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr hp

/-- **A firing configuration rule, inverted, with its left-hand side kept.** -/
theorem firesCfg_lhs20 {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {c : Config H} {w : Value}
    (h : HasRuleAt (simEnv20 B) x "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires (simEnv20 B) x k (.tuple [configV hn c, w])) :
    ∃ σ, QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs ∧
      EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
        (.caseE "%;%" (.tupE [.varE "z", .listE es])) (configV hn c) ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW (simEnv20 B) (DDerives (simEnv20 B) (otherwise (simEnv20 B)))
        (otherwise (simEnv20 B) x [] k (.tuple [configV hn c, w])) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := Sim.State.Fires.rule_eq h hf
  obtain ⟨σ', -, fz, hes, hr, -⟩ := firesCfg_full20 h hf
  have hl := Sim.RefsGC.lhs_of_concl he
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  exact ⟨σ, hq, hl, evalExp_varE_iff.1 hZ, Sim.RefsGC.elems_of_list hL,
    Sim.RefsGC.rhs_of_concl he, hp⟩

/-- An `otherwise` premise holds: its reading holds. -/
theorem else_of_prem {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {ρ : VarEnv}
    (h : PremW env D els ρ .elsePr) : els := by
  cases h with
  | elsePr h => exact h

/-- `TRAP` as a one-element right-hand side. -/
abbrev trapRhs : Exp := .listE [.caseE "TRAP" (.tupE [])]

/-- `[TRAP]`, evaluated. -/
theorem evalExp_trapRhs {env : Env} {ρ : VarEnv} :
    EvalExp env ρ trapRhs (.list [caseNilV "TRAP"]) :=
  evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))

/-- `e₁ + e₂` on naturals. -/
theorem evalExp_addNat20 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {p q : Nat}
    (h₁ : EvalExp env ρ e₁ (.num (.natN p))) (h₂ : EvalExp env ρ e₂ (.num (.natN q))) :
    EvalExp env ρ (.binE .addOp (.numT .natT) e₁ e₂) (.num (.natN (p + q))) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨rfl, _, h₂, by simp [binValues, Num.bin, Res.ofOption]⟩⟩

theorem cmpValues_gtOp_nat20 {p q : Nat} (h : q < p) :
    cmpValues .gtOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true) := by
  simp [cmpValues, Num.cmp, Res.ofOption, h]

/-! ## `$(n - 1)` -/

/-- `$(n - 1)`: `int` subtraction, converted back to `nat`. -/
abbrev predE : Exp :=
  .cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
    (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT

/-- **`$(n - 1)` has a value only at `n ≥ 1`.** -/
theorem pred_inv {env : Env} {ρ : VarEnv} {k : Nat} {v : Value}
    (fn : ρ.findVal? "n" = some (.num (.natN k))) (h : EvalExp env ρ predE v) :
    1 ≤ k ∧ v = .num (.natN (k - 1)) := by
  obtain ⟨m, m', hm, hcv, rfl⟩ := evalExp_cvtE_iff.1 h
  obtain ⟨u₁, hu₁, hs | ⟨-, u₂, hu₂, hb⟩⟩ := evalExp_binE_iff.1 hm
  · simp [boolShort] at hs
  have e₁ : u₁ = .num (.intN k) :=
    EvalExp.unique hu₁ (Equiv.evalExp_toInt (evalExp_var fn))
  have e₂ : u₂ = .num (.intN 1) := EvalExp.unique hu₂ Equiv.evalExp_oneInt
  rw [e₁, e₂] at hb
  have em : m = .intN ((k : Int) - 1) := by
    simpa [binValues, Num.bin, Res.ofOption] using hb.symm
  subst em
  by_cases hk : 1 ≤ k
  · refine ⟨hk, ?_⟩
    have : ((k : Int) - 1).toNat = k - 1 := by omega
    simp only [Num.cvt, show (0 : Int) ≤ (k : Int) - 1 by omega, ↓reduceIte, this,
      Option.some.injEq] at hcv
    rw [← hcv]
  · have hc : ¬ (0 : Int) ≤ (k : Int) - 1 := by omega
    simp only [Num.cvt, hc, ↓reduceIte, reduceCtorEq] at hcv

/-- `$(n - 1)` at `n ≥ 1`. -/
theorem evalExp_pred {env : Env} {ρ : VarEnv} {k : Nat} (hk : 1 ≤ k)
    (fn : ρ.findVal? "n" = some (.num (.natN k))) :
    EvalExp env ρ predE (.num (.natN (k - 1))) := by
  have hsub : EvalExp env ρ (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((k : Int) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt (evalExp_var fn)) Equiv.evalExp_oneInt rfl
  have h := Equiv.evalExp_toNat (j := (k : Int) - 1) (by omega) hsub
  have e : ((k : Int) - 1).toNat = k - 1 := by omega
  rw [e] at h
  exact h

/-- `CONST I32 (% e)`. -/
abbrev constPE (e : Exp) : Exp :=
  .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [e])])

/-- `CONST I32 (% e)`, evaluated. -/
theorem evalExp_constPE {env : Env} {ρ : VarEnv} {e : Exp} {k : Nat}
    (h : EvalExp env ρ e (.num (.natN k))) :
    EvalExp env ρ (constPE e) (.case "CONST" (.tuple [caseNilV "I32", pctV k])) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons h evalExps_nil, rfl⟩)))

/-- The payload of an evaluated `CONST I32 (% e)`. -/
theorem constPE_inv {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (constPE e) v) : ∃ u, EvalExp env ρ e u := by
  obtain ⟨u, hu, -⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, -, hw₂, -, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨u', hu', -⟩ := evalExp_caseE_iff.1 hw₂
  obtain ⟨vs', hvs', -⟩ := evalExp_tupE_iff.1 hu'
  obtain ⟨w₃, -, hw₃, -, -⟩ := evalExps_cons_iff.1 hvs'
  exact ⟨w₃, hw₃⟩

/-! ## Bit-vector arithmetic below the bound -/

theorem toNat_add_one {i : BitVec 32} (h : i.toNat + 1 < 2 ^ 32) : (i + 1).toNat = i.toNat + 1 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using h)]
  rfl

theorem toNat_sub_one {n : BitVec 32} (h : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have hn : 1 ≤ n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
    · exact h0
  rw [BitVec.toNat_sub]
  have hlt := n.isLt
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1]
  omega

theorem ne_zero_of_toNat {n : BitVec 32} (h : 1 ≤ n.toNat) : n ≠ 0 := by
  rintro rfl
  simp at h

/-! ## `table.fill`, verbatim -/

/-- `(val : val <: admininstr)`. -/
abbrev valE : Exp := .subE (.varE "val") (.varT "val" []) (.varT "admininstr" [])

/-- The quantifiers of the three `table.fill` rules. -/
abbrev fillQs : List Param :=
  [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
    .expP "val" (.varT "val" []), .expP "n" (.varT "n" []), .expP "x" (.varT "idx" [])]

/-- The code of the three `table.fill` rules. -/
abbrev tableFillEs : List Exp := [constIE, valE, constNE, .caseE "TABLE.FILL" (.varE "x")]

/-- Their left-hand side. -/
abbrev tableFillLhs : Exp := .caseE "%;%" (.tupE [.varE "z", .listE tableFillEs])

/-- `Step_read/table.fill-trap`, rule 12 (verbatim). -/
def tableFillTrapRule : Rule :=
  .ruleD "table.fill-trap" fillQs "%~>%" (.tupE [tableFillLhs, trapRhs])
    [.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) iPay (.varE "n")) tableLenE)]

/-- `Step_read/table.fill-zero`, rule 13 (verbatim). -/
def tableFillZeroRule : Rule :=
  .ruleD "table.fill-zero" fillQs "%~>%" (.tupE [tableFillLhs, .listE []])
    [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))]

/-- The right-hand side of `table.fill-succ`. -/
abbrev tableFillSuccRhs : List Exp :=
  [constIE, valE, .caseE "TABLE.SET" (.varE "x"),
    constPE (.binE .addOp (.numT .natT) iPay (.numE (.natN 1))), valE, constPE predE,
    .caseE "TABLE.FILL" (.varE "x")]

/-- `Step_read/table.fill-succ`, rule 14 (verbatim). -/
def tableFillSuccRule : Rule :=
  .ruleD "table.fill-succ" fillQs "%~>%" (.tupE [tableFillLhs, .listE tableFillSuccRhs]) [.elsePr]

theorem hasRuleAt_tableFillTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 12 tableFillTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableFillZero : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 13 tableFillZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableFillSucc : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 14 tableFillSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head20_tableFill {a : Admin} (h : adminHead20 a = "TABLE.FILL") :
    ∃ x, a = .plain (.tableFill x) := by
  revert h; admin_head_inv20

/-- The operands of a `table.fill` left-hand side, read back. -/
structure FillLhs (σ : List (IL.Id × Value)) (code : List Admin) : Prop where
  ops : ∃ (i n : BitVec 32) (v : Val) (x : TableIdx),
    code = [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)] ∧
    (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) ∧
    (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v) ∧
    (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)) ∧
    (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x)

theorem fillLhs_of {σ : List (IL.Id × Value)} {code : List Admin}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) fillQs)
    (hes : EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) tableFillEs (adminsToV code)) :
    FillLhs σ code := by
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes20_four hes
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨v, rfl⟩ := val20_of_var hq (by simp) h₂
  obtain ⟨n, rfl, fn⟩ := constN_of_lhs h₃
  obtain ⟨x, rfl⟩ := head20_tableFill (head20_of_caseE h₄)
  exact ⟨i, n, v, x, rfl, fi, val_of_subE h₂, fn, idx_of_caseE (X := idxV x) h₄ rfl⟩

/-- **A firing `-zero` or `-succ` rule of `table.fill` gives the bound**: otherwise rule 12's body
holds at `TRAP`. -/
theorem fill_bound {k : Nat} (hk : 12 < k) {σ : List (IL.Id × Value)} {c : Config H} {w : Value}
    {i n : BitVec 32} {x : TableIdx} {a : Nat} {ti : TableInst}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) fillQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableFillLhs (configV hn c))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (ha : c.frame.module.tables[x.toNat]? = some a) (ht : c.store.tables[a]? = some ti)
    (ho : otherwise (simEnv20 B) "Step_read" [] k (.tuple [configV hn c, w])) :
    i.toNat + n.toNat ≤ ti.refs.length := by
  refine Nat.le_of_not_lt fun hlt => otherwise_absurd hasRuleAt_tableFillTrap hk ho
    (b' := .list [caseNilV "TRAP"]) (body_ifRule hq (evalExp_tup2 hl evalExp_trapRhs) ?_)
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn),
    evalExp_tableLen20 rfl fz fx ha ht, cmpValues_gtOp_nat20 hlt⟩

/-! ## The two rules backwards -/

/-- **`Step_read/table.fill-zero` backwards**, at a `GoodW` configuration. -/
theorem bwdRead_tableFillZero {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 13 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableFillZero hf
  obtain ⟨i, n, v, x, rfl, fi, -, fn, fx⟩ := (fillLhs_of hq hes).ops
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableFill x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have ho := else_of_prem (hp _ (List.mem_cons_self ..))
  have hb := fill_bound (by decide) hq hl fz fi fn fx ha ht ho
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ :=
    evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have hn0 : n.toNat = 0 := by
    have e : v₁ = v₂ := cmpValues_eq_true_iff.1 hcmp
    rw [EvalExp.unique e₁ (evalExp_var fn), EvalExp.unique e₂ (evalExp_numE_iff.2 rfl)] at e
    simpa using e
  have en : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn0)
  subst en
  have ew : w = [] := Value.list.inj (EvalExp.unique hr Pure.evalExp_list0)
  refine ⟨[], ew, .tableFillZero (ti := ti) (by
    simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, ha, ht]) ?_⟩
  simpa using hb

/-- The image of `table.fill-succ`'s V2 right-hand side. -/
theorem adminsToV_tableFillSucc (i n : BitVec 32) (v : Val) (x : TableIdx) (hi : i.toNat + 1 < 2 ^ 32)
    (hn : n ≠ 0) :
    adminsToV [constI32 i, v.toAdmin, .plain (.tableSet x), constI32 (i + 1), v.toAdmin,
        constI32 (n - 1), .plain (.tableFill x)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), valV v, .case "TABLE.SET" (idxV x),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]), valV v,
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]), .case "TABLE.FILL" (idxV x)] := by
  simp only [adminsToV, adminToV_constI32, Pure.adminToV_toAdmin, toNat_add_one hi,
    toNat_sub_one hn]
  rfl

/-- **`Step_read/table.fill-succ` backwards**, at a `GoodW` configuration with a typed result. -/
theorem bwdRead_tableFillSucc {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 14 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableFillSucc hf
  obtain ⟨i, n, v, x, rfl, fi, fv, fn, fx⟩ := (fillLhs_of hq hes).ops
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableFill x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have ho := else_of_prem (hp _ (List.mem_singleton_self _))
  have hb := fill_bound (by decide) hq hl fz fi fn fx ha ht ho
  have hes' := Sim.RefsGC.elems_of_list hr
  have h6 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hes'
    obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
    obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
    obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
    obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
    obtain ⟨u, -, hu, -, -⟩ := evalExps_cons_iff.1 hws
    exact constPE_inv hu
  obtain ⟨u, hu⟩ := h6
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hn : n ≠ 0 := ne_zero_of_toNat hn1
  have hv : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) valE (valV v) :=
    evalExp_subE_iff.2 (evalExp_var fv)
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), valV v,
      .case "TABLE.SET" (idxV x), .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
      valV v, .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "TABLE.FILL" (idxV x)] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        (evalExp_var fi))) (evalExps_cons hv (evalExps_cons (evalExp_case (evalExp_var fx))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons hv (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)))))), rfl⟩))
  have hi1 : i.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  refine ⟨_, ew.trans (adminsToV_tableFillSucc i n v x hi1 hn).symm, .tableFillSucc (ti := ti) (by
    simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, ha, ht]) hb hn⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
