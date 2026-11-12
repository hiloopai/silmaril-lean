module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestMemInit

/-!
# `table.copy-gt` and `memory.copy-gt` backwards: `otherwise` against an `otherwise` rule

`table.copy-gt` (`Step_read` 18) has the single premise `otherwise`. Reading `i < j` back from it
means refuting the body of `table.copy-le` (17) when `j ≤ i`, and that body carries `-le`'s own
`otherwise` premise. So `otherwise` is constructed for rule 17 at the same left-hand side
(`otherwise17`): rules 0–14 name a constructor the code lacks (the tag table `readTags20`, through
`RefsGC.otherwiseAt_of_table`), and the bodies of 15 (`-trap`) and 16 (`-zero`) are refuted by
reading their scopes back (`bodyCfg_inv`): the bounds hold and `n ≠ 0`. The same for
`memory.copy-gt` (43) against 40–42.

This discharges `Step_read` 18 and 43 (`bwdRead_tableCopyGt`, `bwdRead_memoryCopyGt`), the last of
the live `Step_read` rules: `wholeStepBwdW_of_rest9` leaves only `Step` rules (`BwdRestW9`).
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
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW RuleBody DDerives otherwise otherwiseAt noElse
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn TagsIn otherwiseAt_of_table tags_of_take relRules
  ruleTags)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Generic -/

/-- **The body of a configuration rule, inverted**: the scope binds `z` to the state, the code
evaluates element by element, the right-hand side evaluates, and the premises hold. -/
theorem bodyCfg_inv {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {nm : IL.Id}
    {qs : List Param} {es : List Exp} {rh : Exp} {prems : List Prem} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv20 B) D els [] [] "%~>%"
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems)
      (.tuple [configV hn c, w])) :
    ∃ σ, QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW (simEnv20 B) D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := hb
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hl := Sim.RefsGC.lhs_of_concl he
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  exact ⟨σ, hq, evalExp_varE_iff.1 hZ, Sim.RefsGC.elems_of_list hL, Sim.RefsGC.rhs_of_concl he, hp⟩

/-- `e₁ ∨ e₂` has no value `true` when both are `false`. -/
theorem not_or_true {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h₁ : EvalExp env ρ e₁ (.bool false)) (h₂ : EvalExp env ρ e₂ (.bool false))
    (h : EvalExp env ρ (.binE .orOp .boolT e₁ e₂) (.bool true)) : False := by
  obtain ⟨v₁, hv₁, hs | ⟨-, v₂, hv₂, hb⟩⟩ := evalExp_binE_iff.1 h
  · rw [EvalExp.unique hv₁ h₁] at hs
    simp [boolShort] at hs
  · rw [EvalExp.unique hv₁ h₁, EvalExp.unique hv₂ h₂] at hb
    simp [binValues, boolBin, Res.ofOption] at hb

/-- The rule at a known index. -/
theorem rule_of_hasRuleAt {env : Env} {x : IL.Id} {k : Nat} {r r' : Rule} {t : Typ}
    {rules : List Rule} (hrel : env.findRel? x = some ([], "%~>%", t, rules))
    (hR : HasRuleAt env x "%~>%" k r) (hr : rules[k]? = some r') : r' = r := by
  obtain ⟨_, _, rules', hrel', -, hk⟩ := hR
  have e : rules' = rules := by
    rw [hrel] at hrel'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    exact hrel'.2.2.2.symm
  rw [e] at hk
  exact Option.some.inj (hr.symm.trans hk)

/-- Two pairs with the same left-hand side. -/
theorem sameLhs_inv {a b w' : Value} (h : Sim.SameLhs (.tuple [a, b]) w') :
    ∃ c, w' = .tuple [a, c] := by
  obtain ⟨a', b', c', h₁, rfl⟩ := h
  have e : a' = a := by
    simp only [Value.tuple.injEq, List.cons.injEq] at h₁
    exact h₁.1.symm
  exact ⟨c', by rw [e]⟩

/-- The premises `[otherwise, if e]`. -/
theorem prems_else_if {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {ρ : VarEnv}
    {e : Exp} (ho : els) (he : EvalExp env ρ e (.bool true)) :
    ∀ pr ∈ [Prem.elsePr, .ifPr e], PremW env D els ρ pr := by
  intro pr hpr
  rcases List.mem_pair.1 hpr with rfl | rfl
  · exact .elsePr ho
  · exact .ifPr he

/-- `constI32` is injective. -/
theorem constI32_inj {a b : BitVec 32} (h : constI32 a = constI32 b) : a = b := by
  cases h
  rfl

/-- `$(v.%.0 + n - 1)`. -/
abbrev sumPredE (p : Exp) : Exp :=
  .cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT .natT) p (.varE "n")) .natT .intT)
    (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT

/-- `$(p + n - 1)` at `n ≥ 1`. -/
theorem evalExp_sumPred {env : Env} {ρ : VarEnv} {p : Exp} {a k : Nat} (hk : 1 ≤ k)
    (hp : EvalExp env ρ p (.num (.natN a))) (fn : ρ.findVal? "n" = some (.num (.natN k))) :
    EvalExp env ρ (sumPredE p) (.num (.natN (a + k - 1))) := by
  have hsub : EvalExp env ρ (.binE .subOp (.numT .intT)
      (.cvtE (.binE .addOp (.numT .natT) p (.varE "n")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN (((a + k : Nat) : Int) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt (evalExp_addNat20 hp (evalExp_var fn)))
      Equiv.evalExp_oneInt rfl
  have h := Equiv.evalExp_toNat (j := ((a + k : Nat) : Int) - 1) (by omega) hsub
  have e : (((a + k : Nat) : Int) - 1).toNat = a + k - 1 := by omega
  rw [e] at h
  exact h

/-- `(a + n - 1).toNat` below the bound. -/
theorem toNat_add_sub_one {a n : BitVec 32} (hn : 1 ≤ n.toNat) (h : a.toNat + n.toNat - 1 < 2 ^ 32) :
    (a + n - 1).toNat = a.toNat + n.toNat - 1 := by
  have ha := a.isLt
  have hn' := n.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_add]
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1]
  omega

/-! ## `table.copy-gt` -/

/-- `Step_read/table.copy-gt`, rule 18 (verbatim). -/
def tableCopyGtRule : Rule :=
  .ruleD "table.copy-gt" copyQs "%~>%" (.tupE [tableCopyLhs, .listE [constPE (sumPredE jPay),
    constPE (sumPredE iPay), .caseE "TABLE.GET" (.varE "y"), .caseE "TABLE.SET" (.varE "x"),
    constJE, constIE, constPE predE, tableCopyE]]) [.elsePr]

theorem hasRuleAt_tableCopyGt : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 18 tableCopyGtRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The scope of a `table.copy` rule body at `c`, read back. -/
structure CopyScope (σ : List (IL.Id × Value)) (j i n : BitVec 32) (x y : TableIdx) : Prop where
  fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat)
  fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat)
  fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat))
  fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x)
  fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y)

/-- A `table.copy` left-hand side at a known code binds the code's operands. -/
theorem copyScope_of {σ : List (IL.Id × Value)} {j i n : BitVec 32} {x y : TableIdx}
    (hes : EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) [constJE, constIE, constNE, tableCopyE]
      (adminsToV [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)])) :
    CopyScope σ j i n x y := by
  obtain ⟨j', i', n', a₄, hc, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x', y', rfl, fx, fy⟩ := copyIdx_of_lhs h₄
  have hc' : constI32 j = constI32 j' ∧ constI32 i = constI32 i' ∧ constI32 n = constI32 n' ∧
      (Admin.plain (.tableCopy x y) : Admin) = .plain (.tableCopy x' y') := by
    simpa only [List.cons.injEq, and_true] using hc
  obtain ⟨hj, hi, hn, hxy⟩ := hc'
  cases hxy
  rw [constI32_inj hj, constI32_inj hi, constI32_inj hn]
  exact ⟨fj, fi, fn, fx, fy⟩

/-- The tags of `table.copy`'s code. -/
theorem lhsIn_tableCopy (s : Store H) (f : Frame) (j i n : BitVec 32) (x y : TableIdx) :
    LhsIn ["CONST", "TABLE.COPY"]
      (configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩) := by
  refine Or.inr ⟨_, _, rfl, ?_⟩
  intro u hu op w hw
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
  · rw [← adminToV_case20 hw]
    simp [adminHead20, instrHead20]

/-- The `table.copy-trap` body is refuted where both bounds hold. -/
theorem not_trapBody_copy {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {j i n : BitVec 32} {x y : TableIdx} {ax ay : Nat} {tx ty : TableInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (c' : Value) :
    ¬ RuleBody (simEnv20 B) D els [] [] "%~>%" tableCopyTrapRule
      (.tuple [configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩,
        c']) := by
  intro hbody
  obtain ⟨σ, -, fz, hes, -, hp⟩ := bodyCfg_inv hbody
  have S := copyScope_of hes
  have h₁ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) iPay (.varE "n")) tableLenYE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_iPay S.fi) (evalExp_var S.fn))
      (evalExp_tableLenVar20 (B := B) rfl fz S.fy hay hty)
    rwa [show decide (ty.refs.length < i.toNat + n.toNat) = false by simp; omega] at h
  have h₂ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) jPay (.varE "n")) tableLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_jPay S.fj) (evalExp_var S.fn))
      (evalExp_tableLen20 (B := B) rfl fz S.fx hax htx)
    rwa [show decide (tx.refs.length < j.toNat + n.toNat) = false by simp; omega] at h
  exact not_or_true h₁ h₂ (Pure.ifPrem (hp _ (List.mem_singleton_self _)))

/-- The `table.copy-zero` body is refuted at `n ≠ 0`. -/
theorem not_zeroBody_copy {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {j i n : BitVec 32} {x y : TableIdx} (hn0 : n ≠ 0) (c' : Value) :
    ¬ RuleBody (simEnv20 B) D els [] [] "%~>%" tableCopyZeroRule
      (.tuple [configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩,
        c']) := by
  intro hbody
  obtain ⟨σ, -, -, hes, -, hp⟩ := bodyCfg_inv hbody
  exact hn0 (zero_of_prem (copyScope_of hes).fn
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))

/-- **`otherwise` holds for rule 17 at a `table.copy` left-hand side** where the bounds hold and
`n ≠ 0`. -/
theorem otherwise17 {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx} {ax ay : Nat}
    {tx ty : TableInst} (hn0 : n ≠ 0)
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (w : Value) :
    otherwiseAt (simEnv20 B) "Step_read" [] 17
      (.tuple [configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩,
        w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_tableCopyLe (B := B)
  have hT : ((relRules (simEnv20 B) "Step_read").map ruleTags).take 47 = readTags20 := by
    rw [relRules_simEnv20, readTags20_eq]
    rfl
  refine otherwiseAt_of_table hrel (tags_of_take hrel hT) (by decide) (lhsIn_tableCopy s f j i n x y)
    (exc := [15, 16]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := sameLhs_inv hw
  rcases List.mem_pair.1 hk with rfl | rfl
  · rw [rule_of_hasRuleAt hrel hasRuleAt_tableCopyTrap hr]
    exact not_trapBody_copy hax htx hay hty hb c'
  · rw [rule_of_hasRuleAt hrel hasRuleAt_tableCopyZero hr]
    exact not_zeroBody_copy hn0 c'

/-- The value of `table.copy-le`'s right-hand side. -/
def copyLeVals (j i n : BitVec 32) (x y : TableIdx) : List Value :=
  [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
    .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), .case "TABLE.GET" (idxV y),
    .case "TABLE.SET" (idxV x), .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
    .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
    .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
    .case "TABLE.COPY" (.tuple [idxV x, idxV y])]

/-- **`table.copy-le`'s body**, when `j ≤ i`, `n ≥ 1` and its `otherwise` holds. -/
theorem leBody_of {σ : List (IL.Id × Value)} {c : Config H} {j i n : BitVec 32} {x y : TableIdx}
    {els : Prop} (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) copyQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableCopyLhs (configV hn c))
    (S : CopyScope σ j i n x y) (hn1 : 1 ≤ n.toNat) (hle : j.toNat ≤ i.toNat) (ho : els) :
    RuleBody (simEnv20 B) (DDerives (simEnv20 B) noElse) els [] [] "%~>%" tableCopyLeRule
      (.tuple [configV hn c, .list (copyLeVals j i n x y)]) := by
  have hrhs : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.listE [constJE, constIE,
      .caseE "TABLE.GET" (.varE "y"), .caseE "TABLE.SET" (.varE "x"), constSuccE jPay,
      constSuccE iPay, constPE predE, tableCopyE]) (.list (copyLeVals j i n x y)) :=
    evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_constVar S.fj)
      (evalExps_cons (evalExp_constVar S.fi) (evalExps_cons (evalExp_case (evalExp_var S.fy))
      (evalExps_cons (evalExp_case (evalExp_var S.fx))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay S.fj) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay S.fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 S.fn))
      (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var S.fx) (evalExp_var S.fy)))
        evalExps_nil))))))), rfl⟩
  have hcmp : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .leOp (.numT .natT) jPay iPay) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_jPay S.fj, evalExp_iPay S.fi,
      by simp [cmpValues, Num.cmp, Res.ofOption, hle]⟩
  exact ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl hrhs, prems_else_if ho hcmp⟩

/-- The image of `table.copy-gt`'s V2 right-hand side. -/
theorem adminsToV_tableCopyGt (j i n : BitVec 32) (x y : TableIdx) (hn1 : 1 ≤ n.toNat)
    (hj : j.toNat + n.toNat - 1 < 2 ^ 32) (hi : i.toNat + n.toNat - 1 < 2 ^ 32) :
    adminsToV [constI32 (j + n - 1), constI32 (i + n - 1), .plain (.tableGet y),
        .plain (.tableSet x), constI32 j, constI32 i, constI32 (n - 1), .plain (.tableCopy x y)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + n.toNat - 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + n.toNat - 1)]),
        .case "TABLE.GET" (idxV y), .case "TABLE.SET" (idxV x),
        .case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "TABLE.COPY" (.tuple [idxV x, idxV y])] := by
  simp only [adminsToV, adminToV_constI32, toNat_add_sub_one hn1 hj, toNat_add_sub_one hn1 hi,
    toNat_sub_one (ne_zero_of_toNat hn1)]
  rfl

/-- **`Step_read/table.copy-gt` backwards**, at a `GoodW` configuration with a typed result. -/
theorem bwdRead_tableCopyGt {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 18 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableCopyGt hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, y, rfl, fx, fy⟩ := copyIdx_of_lhs h₄
  have S : CopyScope σ j i n x y := ⟨fj, fi, fn, fx, fy⟩
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableCopy x y) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨ax, tx, hax, htx⟩ := table_of_isSome hres.1
  obtain ⟨ay, ty, hay, hty⟩ := table_of_isSome hres.2
  have ho := else_of_prem (hp _ (List.mem_singleton_self _))
  have hb := copy_bound (by decide) hq hl fz fj fi fn fx fy hax htx hay hty ho
  have h7 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₇⟩ := seventh_of_list hr
    exact constPE_inv h₇
  obtain ⟨u, hu⟩ := h7
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hgt : i.toNat < j.toNat := Nat.lt_of_not_le fun hle =>
    otherwise_absurd hasRuleAt_tableCopyLe (by decide) ho
      (leBody_of hq hl S hn1 hle (otherwise17 (ne_zero_of_toNat hn1) hax htx hay hty hb _))
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + n.toNat - 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + n.toNat - 1)]),
      .case "TABLE.GET" (idxV y), .case "TABLE.SET" (idxV x),
      .case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "TABLE.COPY" (.tuple [idxV x, idxV y])] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constPE (evalExp_sumPred hn1 (evalExp_jPay fj) fn))
      (evalExps_cons (evalExp_constPE (evalExp_sumPred hn1 (evalExp_iPay fi) fn))
      (evalExps_cons (evalExp_case (evalExp_var fy)) (evalExps_cons (evalExp_case (evalExp_var fx))
      (evalExps_cons (evalExp_constVar fj) (evalExps_cons (evalExp_constVar fi)
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
        evalExps_nil))))))), rfl⟩))
  have hj1 : j.toNat + n.toNat - 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  have hi1 : i.toNat + n.toNat - 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_tableCopyGt j i n x y hn1 hj1 hi1).symm,
    .tableCopyGt (tx := tx) (ty := ty)
      (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hax, htx])
      (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hay, hty]) hb
      (ne_zero_of_toNat hn1) hgt⟩

/-! ## `memory.copy-gt` -/

/-- `Step_read/memory.copy-gt`, rule 43 (verbatim). -/
def memCopyGtRule : Rule :=
  .ruleD "memory.copy-gt" memCopyQs "%~>%" (.tupE [memCopyLhs, .listE [constPE (sumPredE jPay),
    constPE (sumPredE iPay), load8E, store8E, constJE, constIE, constPE predE, memCopyE]]) [.elsePr]

theorem hasRuleAt_memCopyGt : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 43 memCopyGtRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The scope of a `memory.copy` rule body, read back. -/
structure MemCopyScope (σ : List (IL.Id × Value)) (j i n : BitVec 32) : Prop where
  fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat)
  fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat)
  fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat))

theorem memCopyScope_of {σ : List (IL.Id × Value)} {j i n : BitVec 32}
    (hes : EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) [constJE, constIE, constNE, memCopyE]
      (adminsToV [constI32 j, constI32 i, constI32 n, .plain .memoryCopy])) :
    MemCopyScope σ j i n := by
  obtain ⟨j', i', n', a₄, hc, fj, fi, fn, -⟩ := const3_of_lhs hes
  have hc' : constI32 j = constI32 j' ∧ constI32 i = constI32 i' ∧ constI32 n = constI32 n' := by
    simp only [List.cons.injEq] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  obtain ⟨hj, hi, hn⟩ := hc'
  rw [constI32_inj hj, constI32_inj hi, constI32_inj hn]
  exact ⟨fj, fi, fn⟩

theorem lhsIn_memCopy (s : Store H) (f : Frame) (j i n : BitVec 32) :
    LhsIn ["CONST", "MEMORY.COPY"]
      (configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩) := by
  refine Or.inr ⟨_, _, rfl, ?_⟩
  intro u hu op w hw
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
  · rw [← adminToV_case20 hw]
    simp [adminHead20, instrHead20]

/-- The `memory.copy-trap` body is refuted where both bounds hold. -/
theorem not_trapBody_memCopy {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {j i n : BitVec 32} {a : Nat} {mi : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (c' : Value) :
    ¬ RuleBody (simEnv20 B) D els [] [] "%~>%" memCopyTrapRule
      (.tuple [configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩, c']) := by
  intro hbody
  obtain ⟨σ, -, fz, hes, -, hp⟩ := bodyCfg_inv hbody
  have S := memCopyScope_of hes
  have hm' := evalExp_memLen20 (B := B) rfl fz ha hm
  have h₁ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) iPay (.varE "n")) memLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_iPay S.fi) (evalExp_var S.fn)) hm'
    rwa [show decide (mi.bytes.size < i.toNat + n.toNat) = false by simp; omega] at h
  have h₂ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) jPay (.varE "n")) memLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_jPay S.fj) (evalExp_var S.fn)) hm'
    rwa [show decide (mi.bytes.size < j.toNat + n.toNat) = false by simp; omega] at h
  exact not_or_true h₁ h₂ (Pure.ifPrem (hp _ (List.mem_singleton_self _)))

/-- The `memory.copy-zero` body is refuted at `n ≠ 0`. -/
theorem not_zeroBody_memCopy {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {j i n : BitVec 32} (hn0 : n ≠ 0) (c' : Value) :
    ¬ RuleBody (simEnv20 B) D els [] [] "%~>%" memCopyZeroRule
      (.tuple [configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩, c']) := by
  intro hbody
  obtain ⟨σ, -, -, hes, -, hp⟩ := bodyCfg_inv hbody
  exact hn0 (zero_of_prem (memCopyScope_of hes).fn
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))

/-- **`otherwise` holds for rule 42 at a `memory.copy` left-hand side** where the bounds hold
and `n ≠ 0`. -/
theorem otherwise42 {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat} {mi : MemInst}
    (hn0 : n ≠ 0) (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    otherwiseAt (simEnv20 B) "Step_read" [] 42
      (.tuple [configV hn ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_memCopyLe (B := B)
  have hT : ((relRules (simEnv20 B) "Step_read").map ruleTags).take 47 = readTags20 := by
    rw [relRules_simEnv20, readTags20_eq]
    rfl
  refine otherwiseAt_of_table hrel (tags_of_take hrel hT) (by decide) (lhsIn_memCopy s f j i n)
    (exc := [40, 41]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := sameLhs_inv hw
  rcases List.mem_pair.1 hk with rfl | rfl
  · rw [rule_of_hasRuleAt hrel hasRuleAt_memCopyTrap hr]
    exact not_trapBody_memCopy ha hm hb c'
  · rw [rule_of_hasRuleAt hrel hasRuleAt_memCopyZero hr]
    exact not_zeroBody_memCopy hn0 c'

/-- The value of `memory.copy-le`'s right-hand side. -/
def memCopyLeVals (j i n : BitVec 32) : List Value :=
  [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
    .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), adminToV load8u, adminToV store8,
    .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
    .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
    .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]), .case "MEMORY.COPY" (.tuple [])]

/-- **`memory.copy-le`'s body**, when `j ≤ i`, `n ≥ 1` and its `otherwise` holds. -/
theorem memLeBody_of {σ : List (IL.Id × Value)} {c : Config H} {j i n : BitVec 32} {els : Prop}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) memCopyQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) memCopyLhs (configV hn c))
    (S : MemCopyScope σ j i n) (hn1 : 1 ≤ n.toNat) (hle : j.toNat ≤ i.toNat) (ho : els) :
    RuleBody (simEnv20 B) (DDerives (simEnv20 B) noElse) els [] [] "%~>%" memCopyLeRule
      (.tuple [configV hn c, .list (memCopyLeVals j i n)]) := by
  have hrhs : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.listE [constJE, constIE, load8E,
      store8E, constSuccE jPay, constSuccE iPay, constPE predE, memCopyE])
      (.list (memCopyLeVals j i n)) :=
    evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_constVar S.fj)
      (evalExps_cons (evalExp_constVar S.fi) (evalExps_cons (evalExp_load8 rfl)
      (evalExps_cons (evalExp_store8 rfl)
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay S.fj) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay S.fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 S.fn))
      (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        evalExps_nil))))))), rfl⟩
  have hcmp : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .leOp (.numT .natT) jPay iPay) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_jPay S.fj, evalExp_iPay S.fi,
      by simp [cmpValues, Num.cmp, Res.ofOption, hle]⟩
  exact ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl hrhs, prems_else_if ho hcmp⟩

/-- The image of `memory.copy-gt`'s V2 right-hand side. -/
theorem adminsToV_memoryCopyGt (j i n : BitVec 32) (hn1 : 1 ≤ n.toNat)
    (hj : j.toNat + n.toNat - 1 < 2 ^ 32) (hi : i.toNat + n.toNat - 1 < 2 ^ 32) :
    adminsToV [constI32 (j + n - 1), constI32 (i + n - 1), load8u, store8, constI32 j, constI32 i,
        constI32 (n - 1), .plain .memoryCopy] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + n.toNat - 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + n.toNat - 1)]),
        adminToV load8u, adminToV store8,
        .case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "MEMORY.COPY" (.tuple [])] := by
  simp only [adminsToV, adminToV_constI32, toNat_add_sub_one hn1 hj, toNat_add_sub_one hn1 hi,
    toNat_sub_one (ne_zero_of_toNat hn1)]
  rfl

/-- **`Step_read/memory.copy-gt` backwards**, at a `GoodW` configuration with a typed result. -/
theorem bwdRead_memoryCopyGt {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 43 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memCopyGt hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain rfl := head20_memoryCopy (head20_of_caseE h₄)
  have S : MemCopyScope σ j i n := ⟨fj, fi, fn⟩
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryCopy := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  have ho := else_of_prem (hp _ (List.mem_singleton_self _))
  have hb := memCopy_bound (by decide) hq hl fz fj fi fn ha hm ho
  have h7 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₇⟩ := seventh_of_list hr
    exact constPE_inv h₇
  obtain ⟨u, hu⟩ := h7
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hgt : i.toNat < j.toNat := Nat.lt_of_not_le fun hle =>
    otherwise_absurd hasRuleAt_memCopyLe (by decide) ho
      (memLeBody_of hq hl S hn1 hle (otherwise42 (ne_zero_of_toNat hn1) ha hm hb _))
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + n.toNat - 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + n.toNat - 1)]),
      adminToV load8u, adminToV store8,
      .case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "MEMORY.COPY" (.tuple [])] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constPE (evalExp_sumPred hn1 (evalExp_jPay fj) fn))
      (evalExps_cons (evalExp_constPE (evalExp_sumPred hn1 (evalExp_iPay fi) fn))
      (evalExps_cons (evalExp_load8 rfl) (evalExps_cons (evalExp_store8 rfl)
      (evalExps_cons (evalExp_constVar fj) (evalExps_cons (evalExp_constVar fi)
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        evalExps_nil))))))), rfl⟩))
  have hj1 : j.toNat + n.toNat - 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  have hi1 : i.toNat + n.toNat - 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_memoryCopyGt j i n hn1 hj1 hi1).symm,
    .memoryCopyGt (mi := mi) (by simp [State.mem?, ha, hm]) hb (ne_zero_of_toNat hn1) hgt⟩

/-! ## What is left: only `Step` -/

/-- **What is left of `BwdRestW8`**: no `Step_read` rule; the `Step` rules from 6 on other than
the inert ones and those of `doneStep4`, i.e. 8, 11, 13, 15, 17, 19 (`step9_left`). -/
structure BwdRestW9 (B : Builtins) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) : Prop where
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → i ∉ doneStep4 → ∀ (c : Config H) (w : Value),
    GoodW c → Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- A `Step_read` rule beyond the 47 does not fire. -/
theorem not_firesRead_ge {i : Nat} (hi : 47 ≤ i) {v : Value} :
    ¬ Fires (simEnv20 B) "Step_read" i v := by
  rintro ⟨t, rules, r, hrel, hr, -⟩
  have hl : rules.length = 47 := by
    have h : relRules (simEnv20 B) "Step_read" = rules := by simp [relRules, hrel]
    rw [← h, relRules_simEnv20]
    have h47 : readTags20.length = 47 := rfl
    have := congrArg List.length readTags20_eq
    rw [List.length_map, h47] at this
    exact this
  have : rules[i]? = none := List.getElem?_eq_none (by omega)
  rw [this] at hr
  cases hr

/-- `BwdRestW8` from what is left. -/
theorem bwdRestW8_of_rest9 {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (R : BwdRestW9 B hn P host) : BwdRestW8 B hn P host where
  read i hd h78 hin hdn hsz hfl hd7 h45 c w hg hc hw hf := by
    by_cases hi : i < 47
    · rcases read8_left hi hd h78 hin hdn hsz hfl hd7 h45 with rfl | rfl
      · exact bwdRead_tableCopyGt hg hw hf
      · exact bwdRead_memoryCopyGt hg hw hf
    · exact absurd hf (not_firesRead_ge (by omega))
  step := R.step

/-- The `Step` rules a `BwdRestW9` still needs. -/
theorem step9_left {i : Nat} (hi : i < 22) (h6 : 6 ≤ i) (hin : i ∉ inertStep20)
    (hdn : i ∉ doneStep4) : i ∈ [8, 11, 13, 15, 17, 19] := by
  simp only [inertStep20, doneStep4, List.mem_cons, List.not_mem_nil, or_false, not_or] at hin hdn ⊢
  omega

/-- **`Task.wholeStepBwdW` from the six `Step` rules left** (`BwdRestW9`): every rule of `Step_pure`
and `Step_read` is discharged at the spec's builtins. -/
theorem wholeStepBwdW_of_rest9
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW9 (Sim.Floats.floatIntB (Silmaril.Wasm.Numerics.Profile.spec nd r)) hn
          (Silmaril.Wasm.Numerics.Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest8 fun H hn hinj host nd r => bwdRestW8_of_rest9 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
