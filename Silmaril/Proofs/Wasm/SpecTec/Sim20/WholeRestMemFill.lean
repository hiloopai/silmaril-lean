module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestFill

/-!
# `memory.fill` backwards

`Step_read` 37–39 of the wasm-2.0 script are `memory.fill-trap`, `-zero` and `-succ`, the
`memory.*` counterparts of `table.fill` (`WholeRestFill`): the bound is read back from the
`otherwise` premise (`memFill_bound`), `n ≠ 0` from `$(n - 1)`, and `i + 1 < 2 ^ 32` from the typing
of the result. `-succ` stores one byte with `STORE I32 8 $memarg0`, V2's `store8`
(`evalExp_memarg0`, `adminToV_store8`).

This discharges `Step_read` 38 and 39 (`bwdRead_memoryFillZero`, `bwdRead_memoryFillSucc`).
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
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW RuleBody DDerives otherwise otherwiseAt noElse
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 HasClause1)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `$memarg0` and `store8` -/

/-- The body of `$memarg0`: `{ALIGN %0, OFFSET %0}`. -/
abbrev memarg0Body : Exp :=
  .strE [.mk "ALIGN" (.caseE "%" (.tupE [.numE (.natN 0)])),
    .mk "OFFSET" (.caseE "%" (.tupE [.numE (.natN 0)]))]

theorem hasClause_memarg0 : HasClause1 (simEnv20 B) "memarg0" [] memarg0Body := ⟨_, _, _, rfl⟩

/-- `$memarg0` is V2's `memarg0`. -/
theorem evalExp_memarg0 {ρ : VarEnv} (hρ : ρ.findDef? "memarg0" = none) :
    EvalExp (simEnv20 B) ρ (.callE "memarg0" []) (memargV memarg0) :=
  evalExp_call1 (ρ₀ := VarEnv.empty) hasClause_memarg0 hρ evalArgs_nil matchArgs_nil
    ⟨10, by with_unfolding_all rfl⟩

/-- `STORE I32 8 $memarg0`. -/
abbrev store8E : Exp :=
  .caseE "STORE" (.tupE [.caseE "I32" (.tupE []),
    .optE (some (.caseE "%" (.tupE [.numE (.natN 8)]))), .callE "memarg0" []])

/-- The image of V2's `store8`. -/
theorem adminToV_store8 :
    adminToV store8 = .case "STORE" (.tuple [caseNilV "I32", .opt (some (pctV 8)), memargV memarg0]) :=
  rfl

/-- `STORE I32 8 $memarg0`, evaluated. -/
theorem evalExp_store8 {ρ : VarEnv} (hρ : ρ.findDef? "memarg0" = none) :
    EvalExp (simEnv20 B) ρ store8E (adminToV store8) := by
  rw [adminToV_store8]
  exact evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
    (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) (evalExps_cons
      (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
        (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩), rfl⟩)
      (evalExps_cons (evalExp_memarg0 hρ) evalExps_nil)), rfl⟩)

/-! ## `memory.fill`, verbatim -/

/-- The quantifiers of the three `memory.fill` rules. -/
abbrev memFillQs : List Param :=
  [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
    .expP "val" (.varT "val" []), .expP "n" (.varT "n" [])]

/-- The code of the three `memory.fill` rules. -/
abbrev memFillEs : List Exp := [constIE, valE, constNE, .caseE "MEMORY.FILL" (.tupE [])]

/-- Their left-hand side. -/
abbrev memFillLhs : Exp := .caseE "%;%" (.tupE [.varE "z", .listE memFillEs])

/-- `|$mem(z, 0).BYTES|`. -/
abbrev memLenE : Exp := .lenE (.dotE mem0E "BYTES")

/-- `Step_read/memory.fill-trap`, rule 37 (verbatim). -/
def memFillTrapRule : Rule :=
  .ruleD "memory.fill-trap" memFillQs "%~>%" (.tupE [memFillLhs, trapRhs])
    [.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) iPay (.varE "n")) memLenE)]

/-- `Step_read/memory.fill-zero`, rule 38 (verbatim). -/
def memFillZeroRule : Rule :=
  .ruleD "memory.fill-zero" memFillQs "%~>%" (.tupE [memFillLhs, .listE []])
    [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))]

/-- The right-hand side of `memory.fill-succ`. -/
abbrev memFillSuccRhs : List Exp :=
  [constIE, valE, store8E, constPE (.binE .addOp (.numT .natT) iPay (.numE (.natN 1))), valE,
    constPE predE, .caseE "MEMORY.FILL" (.tupE [])]

/-- `Step_read/memory.fill-succ`, rule 39 (verbatim). -/
def memFillSuccRule : Rule :=
  .ruleD "memory.fill-succ" memFillQs "%~>%" (.tupE [memFillLhs, .listE memFillSuccRhs]) [.elsePr]

theorem hasRuleAt_memFillTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 37 memFillTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memFillZero : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 38 memFillZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memFillSucc : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 39 memFillSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head20_memoryFill {a : Admin} (h : adminHead20 a = "MEMORY.FILL") :
    a = .plain .memoryFill := by
  revert h; admin_head_inv20

/-- The operands of a `memory.fill` left-hand side, read back. -/
structure MemFillLhs (σ : List (IL.Id × Value)) (code : List Admin) : Prop where
  ops : ∃ (i n : BitVec 32) (v : Val),
    code = [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill] ∧
    (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) ∧
    (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v) ∧
    (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat))

theorem memFillLhs_of {σ : List (IL.Id × Value)} {code : List Admin}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) memFillQs)
    (hes : EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) memFillEs (adminsToV code)) :
    MemFillLhs σ code := by
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes20_four hes
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨v, rfl⟩ := val20_of_var hq (by simp) h₂
  obtain ⟨n, rfl, fn⟩ := constN_of_lhs h₃
  obtain rfl := head20_memoryFill (head20_of_caseE h₄)
  exact ⟨i, n, v, rfl, fi, val_of_subE h₂, fn⟩

/-- **A firing `-zero` or `-succ` rule of `memory.fill` gives the bound.** -/
theorem memFill_bound {k : Nat} (hk : 37 < k) {σ : List (IL.Id × Value)} {c : Config H}
    {w : Value} {i n : BitVec 32} {a : Nat} {mi : MemInst}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) memFillQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) memFillLhs (configV hn c))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (ha : c.frame.module.memAddr? memIdx0 = some a) (hm : c.store.memInst? a = some mi)
    (ho : otherwise (simEnv20 B) "Step_read" [] k (.tuple [configV hn c, w])) :
    i.toNat + n.toNat ≤ mi.bytes.size := by
  refine Nat.le_of_not_lt fun hlt => otherwise_absurd hasRuleAt_memFillTrap hk ho
    (b' := .list [caseNilV "TRAP"]) (body_ifRule hq (evalExp_tup2 hl evalExp_trapRhs) ?_)
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn),
    evalExp_memLen20 rfl fz ha hm, cmpValues_gtOp_nat20 hlt⟩

/-- The sixth element of an evaluated seven-element list. -/
theorem sixth_of_list {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ e₅ e₆ e₇ : Exp} {w : List Value}
    (h : EvalExp env ρ (.listE [e₁, e₂, e₃, e₄, e₅, e₆, e₇]) (.list w)) :
    ∃ u, EvalExp env ρ e₆ u := by
  have hes := Sim.RefsGC.elems_of_list h
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hes
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨-, ws, -, hws, -⟩ := evalExps_cons_iff.1 hws
  obtain ⟨u, -, hu, -, -⟩ := evalExps_cons_iff.1 hws
  exact ⟨u, hu⟩

/-! ## The two rules backwards -/

/-- **`Step_read/memory.fill-zero` backwards**, at a `GoodW` configuration. -/
theorem bwdRead_memoryFillZero {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 38 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memFillZero hf
  obtain ⟨i, n, v, rfl, fi, -, fn⟩ := (memFillLhs_of hq hes).ops
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryFill := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  have ho := else_of_prem (hp _ (List.mem_cons_self ..))
  have hb := memFill_bound (by decide) hq hl fz fi fn ha hm ho
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ :=
    evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have hn0 : n.toNat = 0 := by
    have e : v₁ = v₂ := cmpValues_eq_true_iff.1 hcmp
    rw [EvalExp.unique e₁ (evalExp_var fn), EvalExp.unique e₂ (evalExp_numE_iff.2 rfl)] at e
    simpa using e
  have en : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn0)
  subst en
  have ew : w = [] := Value.list.inj (EvalExp.unique hr Pure.evalExp_list0)
  refine ⟨[], ew, .memoryFillZero (mi := mi) (by simp [State.mem?, ha, hm]) ?_⟩
  simpa using hb

/-- The image of `memory.fill-succ`'s V2 right-hand side. -/
theorem adminsToV_memoryFillSucc (i n : BitVec 32) (v : Val) (hi : i.toNat + 1 < 2 ^ 32)
    (hn : n ≠ 0) :
    adminsToV [constI32 i, v.toAdmin, store8, constI32 (i + 1), v.toAdmin,
        constI32 (n - 1), .plain .memoryFill] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), valV v, adminToV store8,
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]), valV v,
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "MEMORY.FILL" (.tuple [])] := by
  simp only [adminsToV, adminToV_constI32, Pure.adminToV_toAdmin, toNat_add_one hi,
    toNat_sub_one hn]
  rfl

/-- **`Step_read/memory.fill-succ` backwards**, at a `GoodW` configuration with a typed result. -/
theorem bwdRead_memoryFillSucc {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 39 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memFillSucc hf
  obtain ⟨i, n, v, rfl, fi, fv, fn⟩ := (memFillLhs_of hq hes).ops
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryFill := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  have ho := else_of_prem (hp _ (List.mem_singleton_self _))
  have hb := memFill_bound (by decide) hq hl fz fi fn ha hm ho
  have h6 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₆⟩ := sixth_of_list hr
    exact constPE_inv h₆
  obtain ⟨u, hu⟩ := h6
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hn : n ≠ 0 := ne_zero_of_toNat hn1
  have hv : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) valE (valV v) :=
    evalExp_subE_iff.2 (evalExp_var fv)
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), valV v, adminToV store8,
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]), valV v,
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "MEMORY.FILL" (.tuple [])] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        (evalExp_var fi))) (evalExps_cons hv (evalExps_cons (evalExp_store8 rfl)
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons hv (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil)))))),
      rfl⟩))
  have hi1 : i.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_memoryFillSucc i n v hi1 hn).symm,
    .memoryFillSucc (mi := mi) (by simp [State.mem?, ha, hm]) hb hn⟩

/-! ## What is left -/

/-- **What is left of `BwdRestW5`** after `table.fill` and `memory.fill`: `BwdRestW5` without
`Step_read` 13, 14, 38, 39. -/
structure BwdRestW6 (B : Builtins) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) : Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → i ∉ inertRead20 → i ∉ doneRead4 →
    i ∉ [11, 36] → i ∉ [13, 14, 38, 39] → ∀ (c : Config H) (w : List Value), GoodW c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → i ∉ doneStep4 → ∀ (c : Config H) (w : Value),
    GoodW c → Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW5` from what is left. -/
theorem bwdRestW5_of_rest6 {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (R : BwdRestW6 B hn P host) : BwdRestW5 B hn P host where
  read i hd h78 hin hdn hsz c w hg hc hw hf := by
    by_cases e13 : i = 13
    · subst e13; exact bwdRead_tableFillZero hg hf
    by_cases e14 : i = 14
    · subst e14; exact bwdRead_tableFillSucc hg hw hf
    by_cases e38 : i = 38
    · subst e38; exact bwdRead_memoryFillZero hg hf
    by_cases e39 : i = 39
    · subst e39; exact bwdRead_memoryFillSucc hg hw hf
    exact R.read i hd h78 hin hdn hsz (by simp [e13, e14, e38, e39]) c w hg hc hw hf
  step := R.step

/-- **`Task.wholeStepBwdW` from what is left after the fill rules** (`BwdRestW6`). -/
theorem wholeStepBwdW_of_rest6
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW6 (Sim.Floats.floatIntB (Silmaril.Wasm.Numerics.Profile.spec nd r)) hn
          (Silmaril.Wasm.Numerics.Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest5 fun H hn hinj host nd r => bwdRestW5_of_rest6 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
