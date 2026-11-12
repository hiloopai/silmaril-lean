module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestCopy

/-!
# `table.init`, `-zero` and `-succ`, backwards

`Step_read` 19–21 are `table.init-trap` (`i + n > |$elem(z, y).REFS|` or
`j + n > |$table(z, x).REFS|`), `-zero` and `-succ`. As for `table.copy` (`WholeRestCopy`), a firing
`-zero` or `-succ` denies the `-trap` body, so both bounds hold (`init_bound`); `-succ` reads the
segment entry `$elem(z, y).REFS[i]` (`evalExp_elem20`), has `n ≠ 0` from `$(n - 1)`, and
`j + 1`, `i + 1 < 2 ^ 32` from the typing of the result.

This discharges `Step_read` 20 and 21 (`bwdRead_tableInitZero`, `bwdRead_tableInitSucc`).
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
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 evalExp_idxPayload HasClause1 idxPayload)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `$elem` -/

theorem hasClause_elem20 : HasClause1 (simEnv20 B) "elem" State.sfxPat
    (.idxE (.dotE (.varE "s") "ELEMS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "ELEMS")
      idxPayload)) := ⟨_, _, _, rfl⟩

/-- **`$elem(z, y)`**, at a module listing element address `a` at `y` and a store holding a
segment there. -/
theorem evalExp_elem20 {ρ : VarEnv} {ez ey : Exp} {s : Store H} {f : Frame} {y : ElemIdx}
    {a : Nat} {ei : ElemInst} (hρ : ρ.findDef? "elem" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hy : EvalExp (simEnv20 B) ρ ey (idxV y))
    (ha : f.module.elems[y.toNat]? = some a) (he : s.elems[a]? = some ei) :
    EvalExp (simEnv20 B) ρ (.callE "elem" [.expA ez, .expA ey]) (elemInstV ei) :=
  evalExp_call1 hasClause_elem20 hρ (evalArgs_cons hz (evalArgs_cons hy evalArgs_nil))
    State.matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a, evalExp_dotE_iff.2 ⟨storeV hn s,
      evalExp_var rfl, rfl⟩, evalExp_idxE_iff.2 ⟨_, y.toNat, evalExp_dotE_iff.2
        ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl,
          State.frameV_module f⟩, rfl⟩, evalExp_idxPayload rfl,
        by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, he]⟩)

/-- `$elem(z, y).REFS`. -/
abbrev elemRefsE : Exp := .dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS"

/-- A defined element segment, from `InstrResOk`. -/
theorem elem_of_isSome {s : Store H} {f : Frame} {y : ElemIdx}
    (h : ((⟨s, f⟩ : State H).elem? y).isSome) :
    ∃ a ei, f.module.elems[y.toNat]? = some a ∧ s.elems[a]? = some ei :=
  elem_of_res (x := y) h

/-! ## `table.init`, verbatim -/

/-- `TABLE.INIT x y`. -/
abbrev tableInitE : Exp := .caseE "TABLE.INIT" (.tupE [.varE "x", .varE "y"])

/-- The left-hand side of the `table.init` rules. -/
abbrev tableInitLhs : Exp :=
  .caseE "%;%" (.tupE [.varE "z", .listE [constJE, constIE, constNE, tableInitE]])

/-- `Step_read/table.init-trap`, rule 19 (verbatim). -/
def tableInitTrapRule : Rule :=
  .ruleD "table.init-trap" copyQs "%~>%" (.tupE [tableInitLhs, trapRhs])
    [.ifPr (.binE .orOp .boolT
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) iPay (.varE "n")) (.lenE elemRefsE))
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) jPay (.varE "n")) tableLenE))]

/-- `Step_read/table.init-zero`, rule 20 (verbatim). -/
def tableInitZeroRule : Rule :=
  .ruleD "table.init-zero" copyQs "%~>%" (.tupE [tableInitLhs, .listE []])
    [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))]

/-- `Step_read/table.init-succ`, rule 21 (verbatim). -/
def tableInitSuccRule : Rule :=
  .ruleD "table.init-succ" copyQs "%~>%" (.tupE [tableInitLhs, .listE [constJE,
    .subE (.idxE elemRefsE iPay) (.varT "ref" []) (.varT "admininstr" []),
    .caseE "TABLE.SET" (.varE "x"), constSuccE jPay, constSuccE iPay, constPE predE, tableInitE]])
    [.elsePr]

theorem hasRuleAt_tableInitTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 19 tableInitTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableInitZero : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 20 tableInitZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableInitSucc : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 21 tableInitSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head20_tableInit {a : Admin} (h : adminHead20 a = "TABLE.INIT") :
    ∃ x y, a = .plain (.tableInit x y) := by
  revert h; admin_head_inv20

/-- The indices of `TABLE.INIT x y`, read back. -/
theorem initIdx_of_lhs {ρ : VarEnv} {a : Admin}
    (h : EvalExp (simEnv20 B) ρ tableInitE (adminToV a)) :
    ∃ x y, a = .plain (.tableInit x y) ∧ ρ.findVal? "x" = some (idxV x) ∧
      ρ.findVal? "y" = some (idxV y) := by
  obtain ⟨x, y, rfl⟩ := head20_tableInit (head20_of_caseE h)
  have hs := tup_of_caseE h (us := [idxV x, idxV y]) rfl
  exact ⟨x, y, rfl, var_fst hs, var_snd hs⟩

/-- **A firing `table.init` rule after 19 gives both bounds.** -/
theorem init_bound {k : Nat} (hk : 19 < k) {σ : List (IL.Id × Value)} {c : Config H} {w : Value}
    {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx} {ax ay : Nat} {ti : TableInst}
    {ei : ElemInst}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) copyQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableInitLhs (configV hn c))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y))
    (hax : c.frame.module.tables[x.toNat]? = some ax) (htx : c.store.tables[ax]? = some ti)
    (hay : c.frame.module.elems[y.toNat]? = some ay) (hey : c.store.elems[ay]? = some ei)
    (ho : Sim.otherwise (simEnv20 B) "Step_read" [] k (.tuple [configV hn c, w])) :
    i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length := by
  by_contra hb
  refine otherwise_absurd hasRuleAt_tableInitTrap hk ho (b' := .list [caseNilV "TRAP"])
    (body_ifRule hq (evalExp_tup2 hl evalExp_trapRhs) ?_)
  have hy : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.lenE elemRefsE)
      (.num (.natN ei.refs.length)) := by
    refine evalExp_lenE_iff.2 ⟨ei.refs.map refV, evalExp_dotE_iff.2 ⟨elemInstV ei,
      evalExp_elem20 rfl (evalExp_var fz) (evalExp_var fy) hay hey, rfl⟩, ?_⟩
    simp
  refine evalExp_or (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)) hy)
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay fj) (evalExp_var fn))
      (evalExp_tableLen20 rfl fz fx hax htx)) ?_
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

/-! ## The two rules backwards -/

theorem bwdRead_tableInitZero {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 20 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableInitZero hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, y, rfl, fx, fy⟩ := initIdx_of_lhs h₄
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableInit x y) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨ax, ti, hax, htx⟩ := table_of_isSome hres.1
  obtain ⟨ay, ei, hay, hey⟩ := elem_of_isSome hres.2
  have hb := init_bound (by decide) hq hl fz fj fi fn fx fy hax htx hay hey
    (else_of_prem (hp _ (List.mem_cons_self ..)))
  obtain rfl := zero_of_prem fn
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have ew : w = [] := Value.list.inj (EvalExp.unique hr Pure.evalExp_list0)
  refine ⟨[], ew, .tableInitZero (ti := ti) (ei := ei)
    (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hax, htx])
    (by simp [State.elem?, ModuleInst.elemAddr?, Store.elemInst?, hay, hey]) ?_⟩
  simpa using hb

/-- The image of `table.init-succ`'s V2 right-hand side. -/
theorem adminsToV_tableInitSucc (j i n : BitVec 32) (r : Ref) (x : TableIdx) (y : ElemIdx)
    (hj : j.toNat + 1 < 2 ^ 32) (hi : i.toNat + 1 < 2 ^ 32) (hn : n ≠ 0) :
    adminsToV [constI32 j, aref r, .plain (.tableSet x), constI32 (j + 1), constI32 (i + 1),
        constI32 (n - 1), .plain (.tableInit x y)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]), refV r, .case "TABLE.SET" (idxV x),
        .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "TABLE.INIT" (.tuple [idxV x, idxV y])] := by
  simp only [adminsToV, adminToV_constI32, aref, Pure.adminToV_toAdmin, toNat_add_one hj,
    toNat_add_one hi, toNat_sub_one hn]
  rfl

theorem bwdRead_tableInitSucc {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 21 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_tableInitSucc hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, y, rfl, fx, fy⟩ := initIdx_of_lhs h₄
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableInit x y) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨ax, ti, hax, htx⟩ := table_of_isSome hres.1
  obtain ⟨ay, ei, hay, hey⟩ := elem_of_isSome hres.2
  have hb := init_bound (by decide) hq hl fz fj fi fn fx fy hax htx hay hey
    (else_of_prem (hp _ (List.mem_singleton_self _)))
  have h6 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₆⟩ := sixth_of_list hr
    exact constPE_inv h₆
  obtain ⟨u, hu⟩ := h6
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hn : n ≠ 0 := ne_zero_of_toNat hn1
  have hlt : i.toNat < ei.refs.length := by omega
  have hr' : ei.refs[i.toNat]? = some ei.refs[i.toNat] := List.getElem?_eq_getElem hlt
  have hel : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.subE (.idxE elemRefsE iPay) (.varT "ref" []) (.varT "admininstr" []))
      (refV ei.refs[i.toNat]) :=
    evalExp_subE_iff.2 (evalExp_idxE_iff.2 ⟨_, i.toNat, evalExp_dotE_iff.2 ⟨elemInstV ei,
      evalExp_elem20 rfl (evalExp_var fz) (evalExp_var fy) hay hey, rfl⟩, evalExp_iPay fi,
      by simp [Value.idx?, List.getElem?_map, hr']⟩)
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]), refV ei.refs[i.toNat],
      .case "TABLE.SET" (idxV x), .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "TABLE.INIT" (.tuple [idxV x, idxV y])] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_constVar fj)
      (evalExps_cons hel (evalExps_cons (evalExp_case (evalExp_var fx))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay fj) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
        evalExps_nil)))))), rfl⟩))
  have hj1 : j.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  have hi1 : i.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_tableInitSucc j i n _ x y hj1 hi1 hn).symm,
    .tableInitSucc (ti := ti) (ei := ei)
      (by simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, hax, htx])
      (by simp [State.elem?, ModuleInst.elemAddr?, Store.elemInst?, hay, hey]) hb hn hr'⟩

/-! ## What is left -/

/-- The `copy`/`init` `Step_read` rules discharged in `WholeRestCopy` and here. -/
def doneRead7 : List Nat := [16, 17, 20, 21, 41, 42]

/-- **What is left of `BwdRestW6`**: without `Step_read` 16, 17, 20, 21, 41, 42. -/
structure BwdRestW7 (B : Builtins) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) : Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → i ∉ inertRead20 → i ∉ doneRead4 →
    i ∉ [11, 36] → i ∉ [13, 14, 38, 39] → i ∉ doneRead7 → ∀ (c : Config H) (w : List Value),
    GoodW c → TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → i ∉ doneStep4 → ∀ (c : Config H) (w : Value),
    GoodW c → Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW6` from what is left. -/
theorem bwdRestW6_of_rest7 {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (R : BwdRestW7 B hn P host) : BwdRestW6 B hn P host where
  read i hd h78 hin hdn hsz hfl c w hg hc hw hf := by
    by_cases e16 : i = 16
    · subst e16; exact bwdRead_tableCopyZero hg hf
    by_cases e17 : i = 17
    · subst e17; exact bwdRead_tableCopyLe hg hw hf
    by_cases e20 : i = 20
    · subst e20; exact bwdRead_tableInitZero hg hf
    by_cases e21 : i = 21
    · subst e21; exact bwdRead_tableInitSucc hg hw hf
    by_cases e41 : i = 41
    · subst e41; exact bwdRead_memoryCopyZero hg hf
    by_cases e42 : i = 42
    · subst e42; exact bwdRead_memoryCopyLe hg hw hf
    exact R.read i hd h78 hin hdn hsz hfl (by simp [doneRead7, e16, e17, e20, e21, e41, e42]) c w
      hg hc hw hf
  step := R.step

/-- **`Task.wholeStepBwdW` from what is left after the `copy`/`init` rules** (`BwdRestW7`). -/
theorem wholeStepBwdW_of_rest7
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW7 (Sim.Floats.floatIntB (Silmaril.Wasm.Numerics.Profile.spec nd r)) hn
          (Silmaril.Wasm.Numerics.Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest6 fun H hn hinj host nd r => bwdRestW6_of_rest7 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
