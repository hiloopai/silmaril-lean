module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Common

/-!
# The remaining table rules, Core → SpecTec

`Step_read/table.size` (27), `table.fill-zero/succ` (29, 30), `table.copy-oob/zero/le/gt`
(31–34) and `table.init-oob/zero/succ` (35–37), constructed for arbitrary state values
(`sread_*`) and instantiated at the Core encoding (`fwd_*`).

The `-zero`, `-succ`, `-le`, `-gt` rules carry `otherwise`; it is discharged by opcode
(`RefsGC.otherwise_of_ruleAt`), refuting by hand only the earlier rules of the same instruction
(`not_*`), from their premises evaluated in the bindings the left-hand side forces.

**Wrap (G1).** Core computes `table.size`'s result with `BitVec.ofNat` and the residual operands
of the iterating rules with bit-vector `+ 1`; SpecTec writes `% n` and `% (i + 1)` in ℕ. The two
agree exactly when no wrap happens, which each `fwd_*` lemma takes as an explicit hypothesis
(`hw`): `|refs| < 2 ^ |at|` for `table.size`, `i + 1 < 2 ^ |at|` (and `j + 1 < 2 ^ 32`) for the
iterating rules, `i + n ≤ 2 ^ |at|` for `table.copy-gt`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open State (StateDefs StateTyping TableAt aconstV idxV)

/-! ## Generic pieces -/

section Generic

variable {env : Env}

/-- The length of the `REFS` of the table at `n`, in any assignment binding no definitions. -/
theorem evalExp_tableRefsLen (D : StateDefs env) {σ : List (IL.Id × Value)} {ez ex : Exp}
    {S F t : Value} {rs : List Value} {n : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n)) (ht : TableAt S F n t)
    (hR : t.field? "REFS" = some (.list rs)) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "table" [.expA ez, .expA ex]) "REFS")) (.num (.natN rs.length)) :=
  RefsGC.evalExp_len (RefsGC.evalExp_dot
    (State.evalExp_table_of D (findDef_bindVals_empty σ _) hz hx ht) hR)

/-- The length of the `REFS` of the element segment at `n`. -/
theorem evalExp_elemRefsLen (D : StateDefs env) {σ : List (IL.Id × Value)} {ez ex : Exp}
    {S F M e : Value} {Ls As rs : List Value} {n a : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n))
    (hS : S.field? "ELEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "ELEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (he : Ls[a]? = some e) (hR : e.field? "REFS" = some (.list rs)) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "elem" [.expA ez, .expA ex]) "REFS")) (.num (.natN rs.length)) :=
  RefsGC.evalExp_len (RefsGC.evalExp_dot
    (State.evalExp_elem D (findDef_bindVals_empty σ _) hz hx hS hM hA ha he) hR)

/-- A comparison premise that holds is the comparison's value. -/
theorem cmp_true {σ : List (IL.Id × Value)} {e₁ e₂ : Exp} {op : CmpOp} {t : OpTyp} {a b : Nat}
    {c : Bool} (hif : EvalExp env (VarEnv.empty.bindVals σ) (.cmpE op t e₁ e₂) (.bool true))
    (h₁ : EvalExp env (VarEnv.empty.bindVals σ) e₁ (.num (.natN a)))
    (h₂ : EvalExp env (VarEnv.empty.bindVals σ) e₂ (.num (.natN b)))
    (hc : Num.cmp op (.natN a) (.natN b) = some c) : c = true := by
  have hb := EvalExp.unique hif (RefsGC.evalExp_cmpNat h₁ h₂ hc)
  simp only [Value.bool.injEq] at hb
  exact hb.symm

end Generic

/-! ## `table.size` -/

section Size

variable {env : Env} (D : StateDefs env) (St : StateTyping env)
include D St

/-- `Step_read/table.size`: `z; (TABLE.SIZE x) ~> (CONST at (% n))` where `n = |REFS|` and the
table's type is `at lim rt`. -/
theorem sread_tableSize (h : HasRuleAt env "Step_read" "%~>%" 27 tableSizeRule)
    {S F t L RT : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType} {n : Nat}
    (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hL : TypedV env Memory.limitsT L)
    (hRT : TypedV env Memory.reftypeT RT) (ht : TableAt S F n t)
    (hR : t.field? "REFS" = some (.list rs))
    (hT : t.field? "TYPE" = some (.case "%%%" (.tuple [Encode.toValue a, L, RT]))) :
    SRead env (cfgV (stV S F) [.case "TABLE.SIZE" (idxV n)])
      [aconstV (Encode.toValue a) rs.length] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("x", idxV n), ("at", Encode.toValue a),
    ("n", .num (.natN rs.length)), ("lim", L), ("rt", RT)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have ex : EvalExp env (VarEnv.empty.bindVals σ) (.varE "x") (idxV n) := evalExp_var rfl
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
      (QuantsOk.cons rfl (St.addr a _ hρ) (QuantsOk.cons rfl (St.nat _ _ hρ)
        (QuantsOk.cons rfl (hL _ hρ) (QuantsOk.cons rfl (hRT _ hρ) QuantsOk.nil))))))
    (by eval_tac)
    (prems_two
      (.ifPr (RefsGC.evalExp_eq_true (evalExp_tableRefsLen D ez ex ht hR) (evalExp_var rfl)))
      (.ifPr (RefsGC.evalExp_eq_true
        (RefsGC.evalExp_dot (State.evalExp_table_of D rfl ez ex ht) hT) (by eval_tac))))

end Size

/-! ## `table.fill` -/

section Fill

variable {env : Env} (D : StateDefs env) (St : StateTyping env)

/-- The code of a `table.fill` step. -/
abbrev fillCode (A V : Value) (i k n : Nat) : List Value :=
  [aconstV A i, V, aconstV A k, .case "TABLE.FILL" (idxV n)]

/-- The bindings a `table.fill` left-hand side forces. -/
theorem binds_tableFill {ρ : VarEnv} {z : Value} {A V : Value} {i k n : Nat}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"]),
      .subE (.varE "val") (.varT "val" []) (.varT "instr" []),
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "TABLE.FILL" (.varE "x")]])) (cfgV z (fillCode A V i k n))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i") (idxV i) ∧
      EvalExp env ρ (.varE "n") (.num (.natN k)) ∧ EvalExp env ρ (.varE "x") (idxV n) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl),
    const_pct_inv (RefsGC.evalExps_get hs 2 rfl rfl), RefsGC.case_inv (RefsGC.evalExps_get hs 3 rfl rfl)⟩

include D in
/-- `table.fill-oob` does not fire in bounds. -/
theorem not_tableFillOob {Dr : Interp} {els : Prop} {S F t A V c : Value} {rs : List Value}
    {i k n : Nat} (ht : TableAt S F n t) (hR : t.field? "REFS" = some (.list rs))
    (h : i + k ≤ rs.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableFillOobRule
      (.tuple [cfgV (stV S F) (fillCode A V i k n), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi, hk, hx⟩ := binds_tableFill (RefsGC.lhs_of_concl he)
  have hc := cmp_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi) hk) (evalExp_tableRefsLen D hz hx ht hR) rfl
  simp only [decide_eq_true_eq] at hc
  omega

/-- `table.fill-zero` does not fire on a non-zero count. -/
theorem not_tableFillZero {Dr : Interp} {els : Prop} {z A V c : Value} {i k n : Nat}
    (hk : k ≠ 0) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableFillZeroRule
      (.tuple [cfgV z (fillCode A V i k n), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, -, hk', -⟩ := binds_tableFill (RefsGC.lhs_of_concl he)
  have h0 := RefsGC.eq_of_evalExp_eq
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hk'
    RefsGC.evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hk h0

/-- The left-hand side of a `table.fill` step has its constructors among `TABLE.FILL` and those
of values. -/
theorem lhsIn_tableFill {z A : Value} {i k n : Nat} {v : Silmaril.Wasm.Execution.Core.Val} :
    RefsGC.LhsIn (["TABLE.FILL"] ++ RefsGC.valTags) (cfgV z (fillCode A (valV v) i k n)) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_val (RefsGC.valTags_sub _) v)
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) (RefsGC.tagsIn_cons
      (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil)))⟩

include D St

/-- `Step_read/table.fill-zero`: `z; (CONST at i) val (CONST at 0) (TABLE.FILL x) ~> ε`, when
`table.fill-oob` does not apply. -/
theorem sread_tableFillZero (h : HasRuleAt env "Step_read" "%~>%" 29 tableFillZeroRule)
    (h₂₈ : HasRuleAt env "Step_read" "%~>%" 28 tableFillOobRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType} {i : BitVec a.intType.width}
    {v : Silmaril.Wasm.Execution.Core.Val} {n : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32) (hV : TypedV env State.valT (valV v)) (ht : TableAt S F n t)
    (hR : t.field? "REFS" = some (.list rs)) (hi : i.toNat ≤ rs.length) :
    SRead env (cfgV (stV S F) (fillCode (Encode.toValue a) (valV v) i.toNat 0 n)) [] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("val", valV v), ("n", .num (.natN 0)), ("x", idxV n)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (i := 29) (b := .list []) (by decide) (exc := [28])
    (a := (cfgV (stV S F) (fillCode (Encode.toValue a) (valV v) i.toNat 0 n)))
    lhsIn_tableFill (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j = 28 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt h₂₈ hr']
      exact not_tableFillOob D ht hR (by omega))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (hV _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
          QuantsOk.nil))))))
    (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) RefsGC.evalExp_num')))

/-- `Step_read/table.fill-succ`: `z; (CONST at i) val (CONST at n) (TABLE.FILL x) ~>
(CONST at i) val (TABLE.SET x) (CONST at (i + 1)) val (CONST at (n - 1)) (TABLE.FILL x)`, when
neither `table.fill-oob` nor `table.fill-zero` applies. -/
theorem sread_tableFillSucc (h : HasRuleAt env "Step_read" "%~>%" 30 tableFillSuccRule)
    (h₂₈ : HasRuleAt env "Step_read" "%~>%" 28 tableFillOobRule)
    (h₂₉ : HasRuleAt env "Step_read" "%~>%" 29 tableFillZeroRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType} {i : BitVec a.intType.width}
    {v : Silmaril.Wasm.Execution.Core.Val} {k n : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32) (hV : TypedV env State.valT (valV v)) (ht : TableAt S F n t)
    (hR : t.field? "REFS" = some (.list rs)) (hi : i.toNat + k ≤ rs.length) (hk : k ≠ 0) :
    SRead env (cfgV (stV S F) (fillCode (Encode.toValue a) (valV v) i.toNat k n))
      [aconstV (Encode.toValue a) i.toNat, valV v, .case "TABLE.SET" (idxV n),
        aconstV (Encode.toValue a) (i.toNat + 1), valV v, aconstV (Encode.toValue a) (k - 1),
        .case "TABLE.FILL" (idxV n)] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("val", valV v), ("n", .num (.natN k)), ("x", idxV n)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a) i.toNat, valV v, .case "TABLE.SET" (idxV n), aconstV (Encode.toValue a) (i.toNat + 1), valV v, aconstV (Encode.toValue a) (k - 1), .case "TABLE.FILL" (idxV n)])
    (i := 30) (by decide) (exc := [28, 29])
    (a := (cfgV (stV S F) (fillCode (Encode.toValue a) (valV v) i.toNat k n)))
    lhsIn_tableFill (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 28 ∨ j = 29) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₂₈ hr']
        exact not_tableFillOob D ht hR hi
      · rw [RefsGC.relRules_of_ruleAt h₂₉ hr']
        exact not_tableFillZero hk)
  have ea : EvalExp env (VarEnv.empty.bindVals σ)
      (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])) (Encode.toValue a) :=
    RefsGC.evalExp_sub_of (evalExp_var rfl)
  refine dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (hV _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
          QuantsOk.nil))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (evalExp_constPct ea (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (evalExp_constPct ea (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk))) (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil')))))))))
    (prems_one (.elsePr hel))

end Fill

/-! ## `table.copy` -/

section Copy

variable {env : Env} (D : StateDefs env) (St : StateTyping env)

/-- The code of a `table.copy` step. -/
abbrev copyCode (A₁ A₂ A' : Value) (i₁ i₂ k n₁ n₂ : Nat) : List Value :=
  [aconstV A₁ i₁, aconstV A₂ i₂, aconstV A' k, .case "TABLE.COPY" (.tuple [idxV n₁, idxV n₂])]

/-- The bindings a `table.copy` left-hand side forces (the index variables are named `X`, `Y`:
`x_1`, `x_2` in `table.copy-oob`, `x`, `y` in the others). -/
theorem binds_tableCopy {ρ : VarEnv} {X Y : IL.Id} {z A₁ A₂ A' : Value} {i₁ i₂ k n₁ n₂ : Nat}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_1"]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_2"]),
      .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "TABLE.COPY" (.tupE [.varE X, .varE Y])]]))
      (cfgV z (copyCode A₁ A₂ A' i₁ i₂ k n₁ n₂))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i_1") (idxV i₁) ∧
      EvalExp env ρ (.varE "i_2") (idxV i₂) ∧ EvalExp env ρ (.varE "n") (.num (.natN k)) ∧
      EvalExp env ρ (.varE X) (idxV n₁) ∧ EvalExp env ρ (.varE Y) (idxV n₂) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  have hxy := tup2_inv (RefsGC.case_inv (RefsGC.evalExps_get hs 3 rfl rfl))
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl),
    const_inv (RefsGC.evalExps_get hs 1 rfl rfl), const_pct_inv (RefsGC.evalExps_get hs 2 rfl rfl),
    hxy.1, hxy.2⟩

/-- `p ∨ q` evaluated from its two comparisons. -/
theorem or_true {σ : List (IL.Id × Value)} {e₁ e₂ e₃ e₄ : Exp} {t : OpTyp} {a b c d : Nat}
    (hif : EvalExp env (VarEnv.empty.bindVals σ)
      (.binE .orOp t (.cmpE .gtOp (.numT .natT) e₁ e₂) (.cmpE .gtOp (.numT .natT) e₃ e₄))
      (.bool true))
    (h₁ : EvalExp env (VarEnv.empty.bindVals σ) e₁ (.num (.natN a)))
    (h₂ : EvalExp env (VarEnv.empty.bindVals σ) e₂ (.num (.natN b)))
    (h₃ : EvalExp env (VarEnv.empty.bindVals σ) e₃ (.num (.natN c)))
    (h₄ : EvalExp env (VarEnv.empty.bindVals σ) e₄ (.num (.natN d))) : b < a ∨ d < c := by
  have hb := EvalExp.unique hif (evalExp_or (RefsGC.evalExp_cmpNat h₁ h₂ rfl)
    (RefsGC.evalExp_cmpNat h₃ h₄ rfl))
  simp only [Value.bool.injEq] at hb
  exact of_decide_eq_true hb.symm

include D in
/-- `table.copy-oob` does not fire when both ranges are in bounds. -/
theorem not_tableCopyOob {Dr : Interp} {els : Prop} {S F t₁ t₂ A₁ A₂ A' c : Value}
    {rs₁ rs₂ : List Value} {i₁ i₂ k n₁ n₂ : Nat} (ht₁ : TableAt S F n₁ t₁)
    (hR₁ : t₁.field? "REFS" = some (.list rs₁)) (ht₂ : TableAt S F n₂ t₂)
    (hR₂ : t₂.field? "REFS" = some (.list rs₂)) (h : i₁ + k ≤ rs₁.length ∧ i₂ + k ≤ rs₂.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableCopyOobRule
      (.tuple [cfgV (stV S F) (copyCode A₁ A₂ A' i₁ i₂ k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi₁, hi₂, hk, hx, hy⟩ := binds_tableCopy (RefsGC.lhs_of_concl he)
  have ho := or_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi₁) hk) (evalExp_tableRefsLen D hz hx ht₁ hR₁)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi₂) hk) (evalExp_tableRefsLen D hz hy ht₂ hR₂)
  omega

/-- `table.copy-zero` does not fire on a non-zero count. -/
theorem not_tableCopyZero {Dr : Interp} {els : Prop} {z A₁ A₂ A' c : Value} {i₁ i₂ k n₁ n₂ : Nat}
    (hk : k ≠ 0) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableCopyZeroRule
      (.tuple [cfgV z (copyCode A₁ A₂ A' i₁ i₂ k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, -, -, hk', -, -⟩ := binds_tableCopy (RefsGC.lhs_of_concl he)
  have h0 := RefsGC.eq_of_evalExp_eq
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hk'
    RefsGC.evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hk h0

/-- `table.copy-le` does not fire when the destination is above the source. -/
theorem not_tableCopyLe {Dr : Interp} {els : Prop} {z A₁ A₂ A' c : Value} {i₁ i₂ k n₁ n₂ : Nat}
    (hgt : i₂ < i₁) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableCopyLeRule
      (.tuple [cfgV z (copyCode A₁ A₂ A' i₁ i₂ k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, hi₁, hi₂, -, -, -⟩ := binds_tableCopy (RefsGC.lhs_of_concl he)
  have hc := cmp_true (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    (RefsGC.evalExp_unpct hi₁) (RefsGC.evalExp_unpct hi₂) rfl
  simp only [decide_eq_true_eq] at hc
  omega

/-- The left-hand side of a `table.copy` step has its constructors among `TABLE.COPY` and
`CONST`. -/
theorem lhsIn_tableCopy {z A₁ A₂ A' : Value} {i₁ i₂ k n₁ n₂ : Nat} :
    RefsGC.LhsIn (["TABLE.COPY"] ++ RefsGC.valTags) (cfgV z (copyCode A₁ A₂ A' i₁ i₂ k n₁ n₂)) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) (RefsGC.tagsIn_cons
      (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil)))⟩

include D St

/-- `Step_read/table.copy-oob`. -/
theorem sread_tableCopyOob (h : HasRuleAt env "Step_read" "%~>%" 31 tableCopyOobRule)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : TableAt S F n₁ t₁) (hR₁ : t₁.field? "REFS" = some (.list rs₁))
    (ht₂ : TableAt S F n₂ t₂) (hR₂ : t₂.field? "REFS" = some (.list rs₂))
    (hoob : rs₁.length < i₁.toNat + k ∨ rs₂.length < i₂.toNat + k) :
    SRead env (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂)) [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN k)), ("x_1", idxV n₁), ("x_2", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have ho := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_tableRefsLen D ez (evalExp_var (x := "x_1") rfl) ht₁ hR₁) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_tableRefsLen D ez (evalExp_var (x := "x_2") rfl) ht₂ hR₂) rfl)
  rw [decide_eq_true hoob] at ho
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (by eval_tac) (prems_one (.ifPr ho))

/-- `Step_read/table.copy-zero`. -/
theorem sread_tableCopyZero (h : HasRuleAt env "Step_read" "%~>%" 32 tableCopyZeroRule)
    (h₃₁ : HasRuleAt env "Step_read" "%~>%" 31 tableCopyOobRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : TableAt S F n₁ t₁) (hR₁ : t₁.field? "REFS" = some (.list rs₁))
    (ht₂ : TableAt S F n₂ t₂) (hR₂ : t₂.field? "REFS" = some (.list rs₂))
    (hb : i₁.toNat ≤ rs₁.length ∧ i₂.toNat ≤ rs₂.length) :
    SRead env (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat 0 n₁ n₂)) [] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN 0)), ("x", idxV n₁), ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (i := 32) (b := .list []) (by decide) (exc := [31])
    (a := (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂) (Encode.toValue a') i₁.toNat i₂.toNat 0 n₁ n₂)))
    lhsIn_tableCopy (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j = 31 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt h₃₁ hr']
      exact not_tableCopyOob D ht₁ hR₁ ht₂ hR₂ (by omega))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) RefsGC.evalExp_num')))

/-- `Step_read/table.copy-le`. -/
theorem sread_tableCopyLe (h : HasRuleAt env "Step_read" "%~>%" 33 tableCopyLeRule)
    (h₃₁ : HasRuleAt env "Step_read" "%~>%" 31 tableCopyOobRule)
    (h₃₂ : HasRuleAt env "Step_read" "%~>%" 32 tableCopyZeroRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : TableAt S F n₁ t₁) (hR₁ : t₁.field? "REFS" = some (.list rs₁))
    (ht₂ : TableAt S F n₂ t₂) (hR₂ : t₂.field? "REFS" = some (.list rs₂))
    (hb : i₁.toNat + k ≤ rs₁.length ∧ i₂.toNat + k ≤ rs₂.length) (hk : k ≠ 0)
    (hle : i₁.toNat ≤ i₂.toNat) :
    SRead env (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂))
      [aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat,
        .case "TABLE.GET" (idxV n₂), .case "TABLE.SET" (idxV n₁),
        aconstV (Encode.toValue a₁) (i₁.toNat + 1), aconstV (Encode.toValue a₂) (i₂.toNat + 1),
        aconstV (Encode.toValue a') (k - 1), .case "TABLE.COPY" (.tuple [idxV n₁, idxV n₂])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN k)), ("x", idxV n₁), ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat, .case "TABLE.GET" (idxV n₂), .case "TABLE.SET" (idxV n₁), aconstV (Encode.toValue a₁) (i₁.toNat + 1), aconstV (Encode.toValue a₂) (i₂.toNat + 1), aconstV (Encode.toValue a') (k - 1), .case "TABLE.COPY" (.tuple [idxV n₁, idxV n₂])])
    (i := 33) (by decide) (exc := [31, 32])
    (a := (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂) (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂)))
    lhsIn_tableCopy (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 31 ∨ j = 32) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₃₁ hr']
        exact not_tableCopyOob D ht₁ hR₁ ht₂ hR₂ hb
      · rw [RefsGC.relRules_of_ruleAt h₃₂ hr']
        exact not_tableCopyZero hk)
  refine dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_1") rfl) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl)) (RefsGC.evalExp_num' (m := .natN 1))))
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_2") rfl) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at'") rfl) (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk)))
      (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil')))))))))) ?_
  exact prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_leNat
    (RefsGC.evalExp_unpct (evalExp_var rfl)) (RefsGC.evalExp_unpct (evalExp_var rfl)) hle))

/-- `Step_read/table.copy-gt`. -/
theorem sread_tableCopyGt (h : HasRuleAt env "Step_read" "%~>%" 34 tableCopyGtRule)
    (h₃₁ : HasRuleAt env "Step_read" "%~>%" 31 tableCopyOobRule)
    (h₃₂ : HasRuleAt env "Step_read" "%~>%" 32 tableCopyZeroRule)
    (h₃₃ : HasRuleAt env "Step_read" "%~>%" 33 tableCopyLeRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : TableAt S F n₁ t₁) (hR₁ : t₁.field? "REFS" = some (.list rs₁))
    (ht₂ : TableAt S F n₂ t₂) (hR₂ : t₂.field? "REFS" = some (.list rs₂))
    (hb : i₁.toNat + k ≤ rs₁.length ∧ i₂.toNat + k ≤ rs₂.length) (hk : k ≠ 0)
    (hgt : i₂.toNat < i₁.toNat) :
    SRead env (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂))
      [aconstV (Encode.toValue a₁) (i₁.toNat + k - 1), aconstV (Encode.toValue a₂) (i₂.toNat + k - 1),
        .case "TABLE.GET" (idxV n₂), .case "TABLE.SET" (idxV n₁),
        aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat,
        aconstV (Encode.toValue a') (k - 1), .case "TABLE.COPY" (.tuple [idxV n₁, idxV n₂])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN k)), ("x", idxV n₁), ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a₁) (i₁.toNat + k - 1), aconstV (Encode.toValue a₂) (i₂.toNat + k - 1), .case "TABLE.GET" (idxV n₂), .case "TABLE.SET" (idxV n₁), aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat, aconstV (Encode.toValue a') (k - 1), .case "TABLE.COPY" (.tuple [idxV n₁, idxV n₂])])
    (i := 34) (by decide) (exc := [31, 32, 33])
    (a := (cfgV (stV S F) (copyCode (Encode.toValue a₁) (Encode.toValue a₂) (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂)))
    lhsIn_tableCopy (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 31 ∨ j = 32 ∨ j = 33) with rfl | rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₃₁ hr']
        exact not_tableCopyOob D ht₁ hR₁ ht₂ hR₂ hb
      · rw [RefsGC.relRules_of_ruleAt h₃₂ hr']
        exact not_tableCopyZero hk
      · rw [RefsGC.relRules_of_ruleAt h₃₃ hr']
        exact not_tableCopyLe hgt)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_1") rfl) (RefsGC.evalExp_predNat (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl)) (evalExp_var (x := "n") rfl)) (by omega)))
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_2") rfl) (RefsGC.evalExp_predNat (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl)) (evalExp_var (x := "n") rfl)) (by omega))) (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at'") rfl) (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk)))
      (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil'))))))))))
    (prems_one (.elsePr hel))

end Copy

/-! ## `table.init` -/

section Init

variable {env : Env} (D : StateDefs env) (St : StateTyping env)

/-- `I32`, the number type of the segment offset and count. -/
abbrev i32V : Value := .case "I32" (.tuple [])

/-- The element segment the frame's module lists at index `n` is `e`, in the store `S`. -/
def ElemAt (S F : Value) (n : Nat) (e : Value) : Prop :=
  ∃ M Ls As a, S.field? "ELEMS" = some (.list Ls) ∧ F.field? "MODULE" = some M ∧
    M.field? "ELEMS" = some (.list As) ∧ As[n]? = some (.num (.natN a)) ∧ Ls[a]? = some e

include D in
/-- `$elem(z, x)` on a state whose element segment at `n` is `e`. -/
theorem evalExp_elem_of {σ : List (IL.Id × Value)} {ez ex : Exp} {S F e : Value} {n : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n)) (he : ElemAt S F n e) :
    EvalExp env (VarEnv.empty.bindVals σ) (.callE "elem" [.expA ez, .expA ex]) e := by
  obtain ⟨M, Ls, As, a, hS, hM, hA, ha, hr⟩ := he
  exact State.evalExp_elem D (findDef_bindVals_empty σ _) hz hx hS hM hA ha hr

/-- The code of a `table.init` step. -/
abbrev initCode (A : Value) (i j k n₁ n₂ : Nat) : List Value :=
  [aconstV A i, aconstV i32V j, aconstV i32V k, .case "TABLE.INIT" (.tuple [idxV n₁, idxV n₂])]

/-- The bindings a `table.init` left-hand side forces. -/
theorem binds_tableInit {ρ : VarEnv} {z A : Value} {i j k n₁ n₂ : Nat}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "TABLE.INIT" (.tupE [.varE "x", .varE "y"])]]))
      (cfgV z (initCode A i j k n₁ n₂))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i") (idxV i) ∧
      EvalExp env ρ (.varE "j") (idxV j) ∧ EvalExp env ρ (.varE "n") (.num (.natN k)) ∧
      EvalExp env ρ (.varE "x") (idxV n₁) ∧ EvalExp env ρ (.varE "y") (idxV n₂) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  have hxy := tup2_inv (RefsGC.case_inv (RefsGC.evalExps_get hs 3 rfl rfl))
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl),
    const_inv (RefsGC.evalExps_get hs 1 rfl rfl), const_pct_inv (RefsGC.evalExps_get hs 2 rfl rfl),
    hxy.1, hxy.2⟩

include D in
/-- `table.init-oob` does not fire when both ranges are in bounds. -/
theorem not_tableInitOob {Dr : Interp} {els : Prop} {S F t e A c : Value}
    {rs es : List Value} {i j k n₁ n₂ : Nat} (ht : TableAt S F n₁ t)
    (hR : t.field? "REFS" = some (.list rs)) (he : ElemAt S F n₂ e)
    (hE : e.field? "REFS" = some (.list es)) (h : i + k ≤ rs.length ∧ j + k ≤ es.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableInitOobRule
      (.tuple [cfgV (stV S F) (initCode A i j k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he', hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi, hj, hk, hx, hy⟩ := binds_tableInit (RefsGC.lhs_of_concl he')
  have ho := or_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi) hk) (evalExp_tableRefsLen D hz hx ht hR)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hj) hk)
    (RefsGC.evalExp_len (RefsGC.evalExp_dot (evalExp_elem_of D hz hy he) hE))
  omega

/-- `table.init-zero` does not fire on a non-zero count. -/
theorem not_tableInitZero {Dr : Interp} {els : Prop} {z A c : Value} {i j k n₁ n₂ : Nat}
    (hk : k ≠ 0) :
    ¬ RuleBody env Dr els [] [] "%~>%" tableInitZeroRule
      (.tuple [cfgV z (initCode A i j k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, -, -, hk', -, -⟩ := binds_tableInit (RefsGC.lhs_of_concl he)
  have h0 := RefsGC.eq_of_evalExp_eq
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hk'
    RefsGC.evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hk h0

/-- The left-hand side of a `table.init` step has its constructors among `TABLE.INIT` and
`CONST`. -/
theorem lhsIn_tableInit {z A : Value} {i j k n₁ n₂ : Nat} :
    RefsGC.LhsIn (["TABLE.INIT"] ++ RefsGC.valTags) (cfgV z (initCode A i j k n₁ n₂)) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) (RefsGC.tagsIn_cons
      (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil)))⟩

include D St

/-- `Step_read/table.init-oob`. -/
theorem sread_tableInitOob (h : HasRuleAt env "Step_read" "%~>%" 35 tableInitOobRule)
    {S F t e : Value} {rs es : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht : TableAt S F n₁ t) (hR : t.field? "REFS" = some (.list rs))
    (he : ElemAt S F n₂ e) (hE : e.field? "REFS" = some (.list es))
    (hoob : rs.length < i.toNat + k ∨ es.length < j.toNat + k) :
    SRead env (cfgV (stV S F) (initCode (Encode.toValue a) i.toNat j.toNat k n₁ n₂))
      [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("j", idxV j.toNat), ("n", .num (.natN k)), ("x", idxV n₁),
    ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have ho := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_tableRefsLen D ez (evalExp_var (x := "x") rfl) ht hR) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl))
        (evalExp_var (x := "n") rfl))
      (RefsGC.evalExp_len (RefsGC.evalExp_dot
        (evalExp_elem_of D ez (evalExp_var (x := "y") rfl) he) hE)) rfl)
  rw [decide_eq_true hoob] at ho
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.num32 j _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))
    (by eval_tac) (prems_one (.ifPr ho))

/-- `Step_read/table.init-zero`. -/
theorem sread_tableInitZero (h : HasRuleAt env "Step_read" "%~>%" 36 tableInitZeroRule)
    (h₃₅ : HasRuleAt env "Step_read" "%~>%" 35 tableInitOobRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t e : Value} {rs es : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht : TableAt S F n₁ t) (hR : t.field? "REFS" = some (.list rs))
    (he : ElemAt S F n₂ e) (hE : e.field? "REFS" = some (.list es))
    (hb : i.toNat ≤ rs.length ∧ j.toNat ≤ es.length) :
    SRead env (cfgV (stV S F) (initCode (Encode.toValue a) i.toNat j.toNat 0 n₁ n₂)) [] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("j", idxV j.toNat), ("n", .num (.natN 0)), ("x", idxV n₁),
    ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (i := 36) (b := .list []) (by decide) (exc := [35])
    (a := (cfgV (stV S F) (initCode (Encode.toValue a) i.toNat j.toNat 0 n₁ n₂)))
    lhsIn_tableInit (by decide) (by
      intro j' hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j' = 35 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt h₃₅ hr']
      exact not_tableInitOob D ht hR he hE (by omega))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.num32 j _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))
    (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) RefsGC.evalExp_num')))

/-- `Step_read/table.init-succ`. -/
theorem sread_tableInitSucc (h : HasRuleAt env "Step_read" "%~>%" 37 tableInitSuccRule)
    (h₃₅ : HasRuleAt env "Step_read" "%~>%" 35 tableInitOobRule)
    (h₃₆ : HasRuleAt env "Step_read" "%~>%" 36 tableInitZeroRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t e R : Value} {rs es : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht : TableAt S F n₁ t) (hR : t.field? "REFS" = some (.list rs))
    (he : ElemAt S F n₂ e) (hE : e.field? "REFS" = some (.list es))
    (hb : i.toNat + k ≤ rs.length ∧ j.toNat + k ≤ es.length) (hk : k ≠ 0)
    (hr : es[j.toNat]? = some R) :
    SRead env (cfgV (stV S F) (initCode (Encode.toValue a) i.toNat j.toNat k n₁ n₂))
      [aconstV (Encode.toValue a) i.toNat, R, .case "TABLE.SET" (idxV n₁),
        aconstV (Encode.toValue a) (i.toNat + 1), aconstV i32V (j.toNat + 1),
        aconstV i32V (k - 1), .case "TABLE.INIT" (.tuple [idxV n₁, idxV n₂])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("j", idxV j.toNat), ("n", .num (.natN k)), ("x", idxV n₁),
    ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a) i.toNat, R, .case "TABLE.SET" (idxV n₁), aconstV (Encode.toValue a) (i.toNat + 1), aconstV i32V (j.toNat + 1), aconstV i32V (k - 1), .case "TABLE.INIT" (.tuple [idxV n₁, idxV n₂])])
    (i := 37) (by decide) (exc := [35, 36])
    (a := (cfgV (stV S F) (initCode (Encode.toValue a) i.toNat j.toNat k n₁ n₂)))
    lhsIn_tableInit (by decide) (by
      intro j' hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j' = 35 ∨ j' = 36) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₃₅ hr']
        exact not_tableInitOob D ht hR he hE hb
      · rw [RefsGC.relRules_of_ruleAt h₃₆ hr']
        exact not_tableInitZero hk)
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have e₂ : EvalExp env (VarEnv.empty.bindVals σ)
      (.subE (.idxE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
        (.projE (.uncaseE (.varE "j") "%") 0)) (.varT "ref" []) (.varT "instr" [])) R :=
    RefsGC.evalExp_sub_of (RefsGC.evalExp_idx (RefsGC.evalExp_dot
      (evalExp_elem_of D ez (evalExp_var (x := "y") rfl) he) hE)
      (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl)) hr)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.num32 j _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' e₂ (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at") rfl) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (et := .caseE "I32" (.tupE [])) (by eval_tac) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (et := .caseE "I32" (.tupE [])) (by eval_tac) (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk)))
      (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil')))))))))
    (prems_one (.elsePr hel))

end Init

end Silmaril.Wasm.SpecTec.Sim.Memory
