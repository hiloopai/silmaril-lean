module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestMemFill

/-!
# `table.copy` and `memory.copy`, `-zero` and `-le`, backwards

`Step_read` 15–18 are `table.copy-trap`, `-zero`, `-le` and `-gt`, and 40–43 their `memory.*`
counterparts. The `-trap` premise is a disjunction of two bounds (`evalExp_or`); a firing `-zero`
or `-le` rule denies the `-trap` body, so both bounds hold (`copy_bound`, `memCopy_bound`).
`-le` has `n ≠ 0` from `$(n - 1)` and `j + 1`, `i + 1 < 2 ^ 32` from the typing of the result.

This discharges `Step_read` 16, 17, 41, 42. The `-gt` rules (18, 43) are not done here: their
`otherwise` denies the body of `-le`, which carries its own `otherwise` premise, so reading it back
needs `otherwise` constructed for rule 17 (43) against every earlier rule (the tag tables of
`RefsGC.otherwiseAt_of_table`).
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

/-! ## Generic pieces -/

/-- `e₁ ∨ e₂` on two booleans. -/
theorem evalExp_or {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {b₁ b₂ : Bool}
    (h₁ : EvalExp env ρ e₁ (.bool b₁)) (h₂ : EvalExp env ρ e₂ (.bool b₂)) (h : (b₁ || b₂) = true) :
    EvalExp env ρ (.binE .orOp .boolT e₁ e₂) (.bool true) := by
  cases b₁ with
  | true => exact evalExp_binE_iff.2 ⟨_, h₁, .inl rfl⟩
  | false =>
    have hb : b₂ = true := by simpa using h
    subst hb
    exact evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨rfl, _, h₂, by simp [binValues, boolBin]⟩⟩

/-- `p > q` on naturals, as a boolean. -/
theorem evalExp_gtNat {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {p q : Nat}
    (h₁ : EvalExp env ρ e₁ (.num (.natN p))) (h₂ : EvalExp env ρ e₂ (.num (.natN q))) :
    EvalExp env ρ (.cmpE .gtOp (.numT .natT) e₁ e₂) (.bool (decide (q < p))) :=
  evalExp_cmpE_iff.2 ⟨_, _, h₁, h₂, by simp [cmpValues, Num.cmp, Res.ofOption]⟩

/-- `j.%.0`, the payload of a `num_(I32)` variable `j`. -/
abbrev jPay : Exp := .projE (.uncaseE (.varE "j") "%") 0

/-- `CONST I32 j`. -/
abbrev constJE : Exp := .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"])

theorem evalExp_jPay {env : Env} {ρ : VarEnv} {k : Nat} (h : ρ.findVal? "j" = some (pctV k)) :
    EvalExp env ρ jPay (.num (.natN k)) :=
  evalExp_projE_iff.2 ⟨[.num (.natN k)], evalExp_uncaseE_iff.2 (evalExp_var h), Int.le_refl 0, rfl⟩

theorem constJ_of_lhs {env : Env} {ρ : VarEnv} {a : Admin}
    (h : EvalExp env ρ constJE (adminToV a)) :
    ∃ c : BitVec 32, a = constI32 c ∧ ρ.findVal? "j" = some (pctV c.toNat) := by
  obtain ⟨c, rfl⟩ := constI32_of_lhs h
  exact ⟨c, rfl, var_snd (tup_of_caseE h (adminToV_constI32 c))⟩

/-- `CONST I32 v`, evaluated from a variable. -/
theorem evalExp_constVar {env : Env} {ρ : VarEnv} {y : IL.Id} {k : Nat}
    (h : ρ.findVal? y = some (pctV k)) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE y]))
      (.case "CONST" (.tuple [caseNilV "I32", pctV k])) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_var h))

/-- The seventh element of an evaluated eight-element list. -/
theorem seventh_of_list {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : Exp} {w : List Value}
    (h : EvalExp env ρ (.listE [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈]) (.list w)) :
    ∃ u, EvalExp env ρ e₇ u := by
  have hes := Sim.RefsGC.elems_of_list h
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hes
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨u, -, hu, -, -⟩ := evalExps_cons_iff.1 hws
  exact ⟨u, hu⟩

/-- The three constants `j i n` of a `copy`/`init` left-hand side, read back. -/
theorem const3_of_lhs {σ : List (IL.Id × Value)} {e₄ : Exp} {code : List Admin}
    (hes : EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) [constJE, constIE, constNE, e₄]
      (adminsToV code)) :
    ∃ (j i n : BitVec 32) (a : Admin), code = [constI32 j, constI32 i, constI32 n, a] ∧
      (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)) ∧
      EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) e₄ (adminToV a) := by
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes20_four hes
  obtain ⟨j, rfl, fj⟩ := constJ_of_lhs h₁
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₂
  obtain ⟨n, rfl, fn⟩ := constN_of_lhs h₃
  exact ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩

/-- `n = 0`, read back from the `-zero` rules' second premise. -/
theorem zero_of_prem {env : Env} {ρ : VarEnv} {n : BitVec 32}
    (fn : ρ.findVal? "n" = some (.num (.natN n.toNat)))
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0))) (.bool true)) : n = 0 := by
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e : v₁ = v₂ := cmpValues_eq_true_iff.1 hcmp
  rw [EvalExp.unique e₁ (evalExp_var fn), EvalExp.unique e₂ (evalExp_numE_iff.2 rfl)] at e
  have hn0 : n.toNat = 0 := by simpa using e
  exact BitVec.eq_of_toNat_eq (by simpa using hn0)

/-- `j ≤ i`, read back from the `-le` rules' second premise. -/
theorem le_of_prem {env : Env} {ρ : VarEnv} {j i : BitVec 32}
    (fj : ρ.findVal? "j" = some (pctV j.toNat)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (h : EvalExp env ρ (.cmpE .leOp (.numT .natT) jPay iPay) (.bool true)) : j.toNat ≤ i.toNat := by
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  rw [EvalExp.unique e₁ (evalExp_jPay fj), EvalExp.unique e₂ (evalExp_iPay fi)] at hcmp
  simpa [cmpValues, Num.cmp, Res.ofOption] using hcmp

/-! ## `table.copy`, verbatim -/

/-- The quantifiers of the `table.copy` and `table.init` rules. -/
abbrev copyQs : List Param :=
  [.expP "z" (.varT "state" []), .expP "j" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
    .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "n" (.varT "n" []),
    .expP "x" (.varT "idx" []), .expP "y" (.varT "idx" [])]

/-- `TABLE.COPY x y`. -/
abbrev tableCopyE : Exp := .caseE "TABLE.COPY" (.tupE [.varE "x", .varE "y"])

/-- The left-hand side of the `table.copy` rules. -/
abbrev tableCopyLhs : Exp :=
  .caseE "%;%" (.tupE [.varE "z", .listE [constJE, constIE, constNE, tableCopyE]])

/-- `|$table(z, y).REFS|`. -/
abbrev tableLenYE : Exp := .lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")

/-- `Step_read/table.copy-trap`, rule 15 (verbatim). -/
def tableCopyTrapRule : Rule :=
  .ruleD "table.copy-trap" copyQs "%~>%" (.tupE [tableCopyLhs, trapRhs])
    [.ifPr (.binE .orOp .boolT
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) iPay (.varE "n")) tableLenYE)
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) jPay (.varE "n")) tableLenE))]

/-- `Step_read/table.copy-zero`, rule 16 (verbatim). -/
def tableCopyZeroRule : Rule :=
  .ruleD "table.copy-zero" copyQs "%~>%" (.tupE [tableCopyLhs, .listE []])
    [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))]

/-- `CONST I32 (% $(v.%.0 + 1))`. -/
abbrev constSuccE (p : Exp) : Exp := constPE (.binE .addOp (.numT .natT) p (.numE (.natN 1)))

/-- `Step_read/table.copy-le`, rule 17 (verbatim). -/
def tableCopyLeRule : Rule :=
  .ruleD "table.copy-le" copyQs "%~>%" (.tupE [tableCopyLhs, .listE [constJE, constIE,
    .caseE "TABLE.GET" (.varE "y"), .caseE "TABLE.SET" (.varE "x"), constSuccE jPay,
    constSuccE iPay, constPE predE, tableCopyE]])
    [.elsePr, .ifPr (.cmpE .leOp (.numT .natT) jPay iPay)]

theorem hasRuleAt_tableCopyTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 15 tableCopyTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableCopyZero : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 16 tableCopyZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableCopyLe : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 17 tableCopyLeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head20_tableCopy {a : Admin} (h : adminHead20 a = "TABLE.COPY") :
    ∃ x y, a = .plain (.tableCopy x y) := by
  revert h; admin_head_inv20

/-- The indices of `TABLE.COPY x y`, read back. -/
theorem copyIdx_of_lhs {ρ : VarEnv} {a : Admin}
    (h : EvalExp (simEnv20 B) ρ tableCopyE (adminToV a)) :
    ∃ x y, a = .plain (.tableCopy x y) ∧ ρ.findVal? "x" = some (idxV x) ∧
      ρ.findVal? "y" = some (idxV y) := by
  obtain ⟨x, y, rfl⟩ := head20_tableCopy (head20_of_caseE h)
  have hs := tup_of_caseE h (us := [idxV x, idxV y]) rfl
  exact ⟨x, y, rfl, var_fst hs, var_snd hs⟩

/-- `|$table(z, v).REFS|`, for any index variable `v`. -/
theorem evalExp_tableLenVar20 {ρ : VarEnv} {s : Store H} {f : Frame} {v : IL.Id} {x : TableIdx}
    {a : Nat} {ti : TableInst} (hρ : ρ.findDef? "table" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? v = some (idxV x))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti) :
    EvalExp (simEnv20 B) ρ (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE v)])
      "REFS")) (.num (.natN ti.refs.length)) := by
  refine evalExp_lenE_iff.2 ⟨ti.refs.map refV, evalExp_dotE_iff.2 ⟨tableInstV ti,
    evalExp_table20 hρ (evalExp_var fz) (evalExp_var fx) ha ht, rfl⟩, ?_⟩
  simp

/-- **A firing `table.copy` rule after 15 gives both bounds.** -/
theorem copy_bound {k : Nat} (hk : 15 < k) {σ : List (IL.Id × Value)} {c : Config H} {w : Value}
    {j i n : BitVec 32} {x y : TableIdx} {ax ay : Nat} {tx ty : TableInst}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) copyQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableCopyLhs (configV hn c))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y))
    (hax : c.frame.module.tables[x.toNat]? = some ax) (htx : c.store.tables[ax]? = some tx)
    (hay : c.frame.module.tables[y.toNat]? = some ay) (hty : c.store.tables[ay]? = some ty)
    (ho : otherwise (simEnv20 B) "Step_read" [] k (.tuple [configV hn c, w])) :
    i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length := by
  by_contra hb
  refine otherwise_absurd hasRuleAt_tableCopyTrap hk ho (b' := .list [caseNilV "TRAP"])
    (body_ifRule hq (evalExp_tup2 hl evalExp_trapRhs) ?_)
  have hy : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableLenYE
      (.num (.natN ty.refs.length)) := evalExp_tableLenVar20 rfl fz fy hay hty
  refine evalExp_or (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)) hy)
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay fj) (evalExp_var fn))
      (evalExp_tableLen20 rfl fz fx hax htx)) ?_
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

/-! ## `table.copy-zero`, `table.copy-le` backwards -/

theorem bwdRead_tableCopyZero {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 16 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableCopyZero hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, y, rfl, fx, fy⟩ := copyIdx_of_lhs h₄
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableCopy x y) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨ax, tx, hax, htx⟩ := table_of_isSome hres.1
  obtain ⟨ay, ty, hay, hty⟩ := table_of_isSome hres.2
  have hb := copy_bound (by decide) hq hl fz fj fi fn fx fy hax htx hay hty
    (else_of_prem (hp _ (List.mem_cons_self ..)))
  obtain rfl := zero_of_prem fn
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have ew : w = [] := Value.list.inj (EvalExp.unique hr Pure.evalExp_list0)
  refine ⟨[], ew, .tableCopyZero (tx := tx) (ty := ty)
    (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hax, htx])
    (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hay, hty]) ?_⟩
  simpa using hb

/-- The image of `table.copy-le`'s V2 right-hand side. -/
theorem adminsToV_tableCopyLe (j i n : BitVec 32) (x y : TableIdx) (hj : j.toNat + 1 < 2 ^ 32)
    (hi : i.toNat + 1 < 2 ^ 32) (hn : n ≠ 0) :
    adminsToV [constI32 j, constI32 i, .plain (.tableGet y), .plain (.tableSet x),
        constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableCopy x y)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), .case "TABLE.GET" (idxV y),
        .case "TABLE.SET" (idxV x), .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "TABLE.COPY" (.tuple [idxV x, idxV y])] := by
  simp only [adminsToV, adminToV_constI32, toNat_add_one hj, toNat_add_one hi, toNat_sub_one hn]
  rfl

theorem bwdRead_tableCopyLe {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 17 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableCopyLe hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, y, rfl, fx, fy⟩ := copyIdx_of_lhs h₄
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableCopy x y) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨ax, tx, hax, htx⟩ := table_of_isSome hres.1
  obtain ⟨ay, ty, hay, hty⟩ := table_of_isSome hres.2
  have hb := copy_bound (by decide) hq hl fz fj fi fn fx fy hax htx hay hty
    (else_of_prem (hp _ (List.mem_cons_self ..)))
  have hle := le_of_prem fj fi
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have h7 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₇⟩ := seventh_of_list hr
    exact constPE_inv h₇
  obtain ⟨u, hu⟩ := h7
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hn : n ≠ 0 := ne_zero_of_toNat hn1
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), .case "TABLE.GET" (idxV y),
      .case "TABLE.SET" (idxV x), .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "TABLE.COPY" (.tuple [idxV x, idxV y])] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_constVar fj)
      (evalExps_cons (evalExp_constVar fi) (evalExps_cons (evalExp_case (evalExp_var fy))
      (evalExps_cons (evalExp_case (evalExp_var fx))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay fj) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
        evalExps_nil))))))), rfl⟩))
  have hj1 : j.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  have hi1 : i.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_tableCopyLe j i n x y hj1 hi1 hn).symm,
    .tableCopyLe (tx := tx) (ty := ty)
      (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hax, htx])
      (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hay, hty]) hb hn hle⟩

/-! ## `memory.copy`, verbatim -/

/-- The quantifiers of the `memory.copy` rules. -/
abbrev memCopyQs : List Param :=
  [.expP "z" (.varT "state" []), .expP "j" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
    .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "n" (.varT "n" [])]

/-- `MEMORY.COPY`. -/
abbrev memCopyE : Exp := .caseE "MEMORY.COPY" (.tupE [])

/-- The left-hand side of the `memory.copy` rules. -/
abbrev memCopyLhs : Exp :=
  .caseE "%;%" (.tupE [.varE "z", .listE [constJE, constIE, constNE, memCopyE]])

/-- `Step_read/memory.copy-trap`, rule 40 (verbatim). -/
def memCopyTrapRule : Rule :=
  .ruleD "memory.copy-trap" memCopyQs "%~>%" (.tupE [memCopyLhs, trapRhs])
    [.ifPr (.binE .orOp .boolT
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) iPay (.varE "n")) memLenE)
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) jPay (.varE "n")) memLenE))]

/-- `Step_read/memory.copy-zero`, rule 41 (verbatim). -/
def memCopyZeroRule : Rule :=
  .ruleD "memory.copy-zero" memCopyQs "%~>%" (.tupE [memCopyLhs, .listE []])
    [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))]

/-- `LOAD I32 (8 _ U) $memarg0`. -/
abbrev load8E : Exp :=
  .caseE "LOAD" (.tupE [.caseE "I32" (.tupE []), .optE (some (.caseE "%_%"
    (.tupE [.caseE "%" (.tupE [.numE (.natN 8)]), .caseE "U" (.tupE [])]))), .callE "memarg0" []])

/-- `Step_read/memory.copy-le`, rule 42 (verbatim). -/
def memCopyLeRule : Rule :=
  .ruleD "memory.copy-le" memCopyQs "%~>%" (.tupE [memCopyLhs, .listE [constJE, constIE, load8E,
    store8E, constSuccE jPay, constSuccE iPay, constPE predE, memCopyE]])
    [.elsePr, .ifPr (.cmpE .leOp (.numT .natT) jPay iPay)]

theorem hasRuleAt_memCopyTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 40 memCopyTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memCopyZero : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 41 memCopyZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memCopyLe : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 42 memCopyLeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head20_memoryCopy {a : Admin} (h : adminHead20 a = "MEMORY.COPY") :
    a = .plain .memoryCopy := by
  revert h; admin_head_inv20

/-- The image of V2's `load8u`. -/
theorem adminToV_load8u : adminToV load8u = .case "LOAD" (.tuple [caseNilV "I32",
    .opt (some (.case "%_%" (.tuple [pctV 8, caseNilV "U"]))), memargV memarg0]) := rfl

/-- `LOAD I32 (8 _ U) $memarg0`, evaluated. -/
theorem evalExp_load8 {ρ : VarEnv} (hρ : ρ.findDef? "memarg0" = none) :
    EvalExp (simEnv20 B) ρ load8E (adminToV load8u) := by
  rw [adminToV_load8u]
  exact evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
    (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) (evalExps_cons
      (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩))
        (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))), rfl⟩)
      (evalExps_cons (evalExp_memarg0 hρ) evalExps_nil)), rfl⟩)

/-- **A firing `memory.copy` rule after 40 gives both bounds.** -/
theorem memCopy_bound {k : Nat} (hk : 40 < k) {σ : List (IL.Id × Value)} {c : Config H}
    {w : Value} {j i n : BitVec 32} {a : Nat} {mi : MemInst}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) memCopyQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) memCopyLhs (configV hn c))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (ha : c.frame.module.memAddr? memIdx0 = some a) (hm : c.store.memInst? a = some mi)
    (ho : otherwise (simEnv20 B) "Step_read" [] k (.tuple [configV hn c, w])) :
    i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size := by
  by_contra hb
  refine otherwise_absurd hasRuleAt_memCopyTrap hk ho (b' := .list [caseNilV "TRAP"])
    (body_ifRule hq (evalExp_tup2 hl evalExp_trapRhs) ?_)
  have hm' : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) memLenE
      (.num (.natN mi.bytes.size)) := evalExp_memLen20 rfl fz ha hm
  refine evalExp_or (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)) hm')
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay fj) (evalExp_var fn)) hm') ?_
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem bwdRead_memoryCopyZero {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 41 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memCopyZero hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain rfl := head20_memoryCopy (head20_of_caseE h₄)
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryCopy := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  have hb := memCopy_bound (by decide) hq hl fz fj fi fn ha hm
    (else_of_prem (hp _ (List.mem_cons_self ..)))
  obtain rfl := zero_of_prem fn
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have ew : w = [] := Value.list.inj (EvalExp.unique hr Pure.evalExp_list0)
  refine ⟨[], ew, .memoryCopyZero (mi := mi) (by simp [State.mem?, ha, hm]) ?_⟩
  simpa using hb

/-- The image of `memory.copy-le`'s V2 right-hand side. -/
theorem adminsToV_memoryCopyLe (j i n : BitVec 32) (hj : j.toNat + 1 < 2 ^ 32)
    (hi : i.toNat + 1 < 2 ^ 32) (hn : n ≠ 0) :
    adminsToV [constI32 j, constI32 i, load8u, store8, constI32 (j + 1), constI32 (i + 1),
        constI32 (n - 1), .plain .memoryCopy] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), adminToV load8u, adminToV store8,
        .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "MEMORY.COPY" (.tuple [])] := by
  simp only [adminsToV, adminToV_constI32, toNat_add_one hj, toNat_add_one hi, toNat_sub_one hn]
  rfl

theorem bwdRead_memoryCopyLe {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 42 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memCopyLe hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain rfl := head20_memoryCopy (head20_of_caseE h₄)
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryCopy := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  have hb := memCopy_bound (by decide) hq hl fz fj fi fn ha hm
    (else_of_prem (hp _ (List.mem_cons_self ..)))
  have hle := le_of_prem fj fi
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have h7 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₇⟩ := seventh_of_list hr
    exact constPE_inv h₇
  obtain ⟨u, hu⟩ := h7
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hn : n ≠ 0 := ne_zero_of_toNat hn1
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), adminToV load8u, adminToV store8,
      .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "MEMORY.COPY" (.tuple [])] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_constVar fj)
      (evalExps_cons (evalExp_constVar fi) (evalExps_cons (evalExp_load8 rfl)
      (evalExps_cons (evalExp_store8 rfl)
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay fj) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        evalExps_nil))))))), rfl⟩))
  have hj1 : j.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  have hi1 : i.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_memoryCopyLe j i n hj1 hi1 hn).symm,
    .memoryCopyLe (mi := mi) (by simp [State.mem?, ha, hm]) hb hn hle⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
