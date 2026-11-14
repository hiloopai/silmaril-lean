module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.TypingF

/-!
# Building steps of their `Step_exp`, in `fixed`

One lemma per rule the fragment uses: given values of the right types for the rule's
quantifiers, the rule derives the expected step (`unCtx_mk`, `ctx1_mk`, `ctx2_mk`, `unBool_mk`,
`unNum_mk`, `binBool_mk`, `binNum_mk`, `cmpVal_mk`, `cmpNum_mk`). The instance is explicit:
the scope `VarEnv.empty.bindVals σ` for a literal `σ`, its lookups by `rfl`, the typing from
`TypingF`, the conclusion evaluated forwards.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives DPrem QuantsOk TypedV ValsOnly otherwise)

set_option maxRecDepth 100000

/-- The scope of a rule instance. -/
abbrev inst (σ : List (IL.Id × Value)) : VarEnv := VarEnv.empty.bindVals σ

theorem valsOnly_inst (σ : List (IL.Id × Value)) : ValsOnly (inst σ) :=
  ValsOnly.bindVals valsOnly_empty σ

/-- A step by rule `k` of `Step_exp`, at an explicit instance. -/
theorem mstep_mk {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hk : (rulesOf envF "Step_exp")[k]? = some (.ruleD nm qs "%|-%~>%" e prems))
    (σ : List (IL.Id × Value)) {S a b : Value} (hq : QuantsOk envF (inst σ) qs)
    (he : EvalExp envF (inst σ) e (.tuple [S, a, b]))
    (hp : ∀ pr ∈ prems, DPrem envF (otherwise envF)
      (otherwise envF "Step_exp" [] k (.tuple [S, a, b])) (inst σ) pr) :
    MStep envF S a b :=
  Sim.DDerives.rule findRel_stepF hk rfl hq he hp

/-- The premise `Step_exp (S, e, e')` of a congruence rule. -/
theorem prem_step {σ : List (IL.Id × Value)} {els : Prop} {x₁ x₂ x₃ : IL.Id} {S a b : Value}
    (h₁ : (inst σ).findVal? x₁ = some S) (h₂ : (inst σ).findVal? x₂ = some a)
    (h₃ : (inst σ).findVal? x₃ = some b) (h : MStep envF S a b) :
    ∀ pr ∈ [Prem.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE x₁, .varE x₂, .varE x₃])],
      DPrem envF (otherwise envF) els (inst σ) pr :=
  Sim.prems_one (.rulePr Equiv.evalArgs_nil
    (evalExp_tuple (evalExps_three (evalExp_var h₁) (evalExp_var h₂) (evalExp_var h₃))) h)

/-! ## Congruence -/

theorem unCtx_mk {S o a a' : Value} (hS : TypedV envF (.varT "S" []) S)
    (ho : TypedV envF (.varT "unop" []) o) (ha : TypedV envF (.varT "exp" []) a)
    (ha' : TypedV envF (.varT "exp" []) a') (h : MStep envF S a a') :
    MStep envF S (con "UN" [o, a]) (con "UN" [o, a']) := by
  let σ : List (IL.Id × Value) := [("S", S), ("op", o), ("e", a), ("e'", a')]
  have hρ := valsOnly_inst σ
  refine mstep_mk stepF_0 σ ?_ ?_ (prem_step rfl rfl rfl h)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (ha _ hρ) (Sim.QuantsOk.cons rfl (ha' _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_two (evalExp_var rfl) (evalExp_var rfl)))
      (evalExp_con (evalExps_two (evalExp_var rfl) (evalExp_var rfl))))

/-- `BIN-ctx1` (`k = 3`, `T = binop`) and `CMP-ctx1` (`k = 7`, `T = cmpop`). -/
theorem ctx1_mk {k : Nat} {nm : IL.Id} {C : MixopS} {T : Typ}
    (hk : (rulesOf envF "Step_exp")[k]? = some (.ruleD nm [.expP "S" (.varT "S" []), .expP "op" T,
      .expP "e_1" (.varT "exp" []), .expP "e_2" (.varT "exp" []), .expP "e_1'" (.varT "exp" [])]
      "%|-%~>%" (.tupE [.varE "S", .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2"]),
        .caseE C (.tupE [.varE "op", .varE "e_1'", .varE "e_2"])])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e_1", .varE "e_1'"])]))
    {S o a a' b : Value} (hS : TypedV envF (.varT "S" []) S) (ho : TypedV envF T o)
    (ha : TypedV envF (.varT "exp" []) a) (ha' : TypedV envF (.varT "exp" []) a')
    (hb : TypedV envF (.varT "exp" []) b) (h : MStep envF S a a') :
    MStep envF S (con C [o, a, b]) (con C [o, a', b]) := by
  let σ : List (IL.Id × Value) := [("S", S), ("op", o), ("e_1", a), ("e_2", b), ("e_1'", a')]
  have hρ := valsOnly_inst σ
  refine mstep_mk hk σ ?_ ?_ (prem_step rfl rfl rfl h)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (ha _ hρ) (Sim.QuantsOk.cons rfl (hb _ hρ)
        (Sim.QuantsOk.cons rfl (ha' _ hρ) Sim.QuantsOk.nil))))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)))
      (evalExp_con (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))))

/-- `BIN-ctx2` (`k = 4`) and `CMP-ctx2` (`k = 8`), after erratum M1. -/
theorem ctx2_mk {k : Nat} {nm : IL.Id} {C : MixopS} {T : Typ}
    (hk : (rulesOf envF "Step_exp")[k]? = some (.ruleD nm [.expP "S" (.varT "S" []), .expP "op" T,
      .expP "e_1" (.varT "exp" []), .expP "e_2" (.varT "exp" []), .expP "e_2'" (.varT "exp" [])]
      "%|-%~>%" (.tupE [.varE "S", .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2"]),
        .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2'"])])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e_2", .varE "e_2'"])]))
    {S o a b b' : Value} (hS : TypedV envF (.varT "S" []) S) (ho : TypedV envF T o)
    (ha : TypedV envF (.varT "exp" []) a) (hb : TypedV envF (.varT "exp" []) b)
    (hb' : TypedV envF (.varT "exp" []) b') (h : MStep envF S b b') :
    MStep envF S (con C [o, a, b]) (con C [o, a, b']) := by
  let σ : List (IL.Id × Value) := [("S", S), ("op", o), ("e_1", a), ("e_2", b), ("e_2'", b')]
  have hρ := valsOnly_inst σ
  refine mstep_mk hk σ ?_ ?_ (prem_step rfl rfl rfl h)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (ha _ hρ) (Sim.QuantsOk.cons rfl (hb _ hρ)
        (Sim.QuantsOk.cons rfl (hb' _ hρ) Sim.QuantsOk.nil))))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)))
      (evalExp_con (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))))

/-! ## Computation -/

theorem no_prems {σ : List (IL.Id × Value)} {els : Prop} :
    ∀ pr ∈ ([] : List Prem), DPrem envF (otherwise envF) els (inst σ) pr :=
  fun _ h => nomatch h

theorem unBool_mk {S : Value} (hS : TypedV envF (.varT "S" []) S) (b : Bool) :
    MStep envF S (con "UN" [encUnOp .notOp, con "BOOL" [.bool b]]) (con "BOOL" [.bool (!b)]) := by
  let σ : List (IL.Id × Value) := [("S", S), ("boolunop", con "NOT" []), ("b", .bool b)]
  have hρ := valsOnly_inst σ
  have hc : TryClauses envF (fdef "boolun").2.2 (args2 (con "NOT" []) (.bool b)) (.bool (!b)) :=
    boolun_spec .notOp b
  refine mstep_mk stepF_1 σ ?_ ?_ no_prems
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl
      (typedV_nullary (c := "NOT") variant_boolunop rfl _ hρ)
      (Sim.QuantsOk.cons rfl (typedV_bool b _ hρ) Sim.QuantsOk.nil))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_two (evalExp_sub (evalExp_var rfl))
        (evalExp_con (evalExps_cons (evalExp_var rfl) evalExps_nil))))
      (evalExp_con (evalExps_cons (evalExp_callE_iff.2 ((callDef_iff_try hρ (findDef_fdef rfl)
        (builtins_envF _) (evalArgs_vars2 rfl rfl)).2 hc)) evalExps_nil)))

theorem unNum_mk {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : UnOp}
    (ho : TypedV envF (.varT "numunop" []) (encUnOp op)) {m m' : Num} (hm : NatInt m)
    (h : Num.un op m = some m') :
    MStep envF S (con "UN" [encUnOp op, encNum m]) (encNum m') := by
  let σ : List (IL.Id × Value) := [("S", S), ("numunop", encUnOp op), ("num", encNum m)]
  have hρ := valsOnly_inst σ
  have hc : TryClauses envF (fdef "numun").2.2 (args2 (encUnOp op) (encNum m)) (encNum m') := by
    have := numun_spec op hm
    rw [h] at this
    exact this
  refine mstep_mk stepF_2 σ ?_ ?_ no_prems
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (typedV_encNum hm _ hρ) Sim.QuantsOk.nil))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_two (evalExp_sub (evalExp_var rfl)) (evalExp_sub (evalExp_var rfl))))
      (evalExp_sub (evalExp_callE_iff.2 ((callDef_iff_try hρ (findDef_fdef rfl)
        (builtins_envF _) (evalArgs_vars2 rfl rfl)).2 hc))))

theorem binBool_mk {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : BinOp}
    (ho : TypedV envF (.varT "boolbinop" []) (encBinOp op)) {b₁ b₂ : Bool} {w : Value}
    (h : binValues op (.bool b₁) (.bool b₂) = .ok w) :
    MStep envF S (con "BIN" [encBinOp op, con "BOOL" [.bool b₁], con "BOOL" [.bool b₂]])
      (con "BOOL" [w]) := by
  let σ : List (IL.Id × Value) :=
    [("S", S), ("boolbinop", encBinOp op), ("b_1", .bool b₁), ("b_2", .bool b₂)]
  have hρ := valsOnly_inst σ
  have hc : TryClauses envF (fdef "boolbin").2.2 (args3 (encBinOp op) (.bool b₁) (.bool b₂)) w := by
    have := boolbin_spec op b₁ b₂
    rw [h] at this
    exact this
  refine mstep_mk stepF_5 σ ?_ ?_ no_prems
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (typedV_bool b₁ _ hρ)
        (Sim.QuantsOk.cons rfl (typedV_bool b₂ _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_sub (evalExp_var rfl))
        (evalExp_con (evalExps_cons (evalExp_var rfl) evalExps_nil))
        (evalExp_con (evalExps_cons (evalExp_var rfl) evalExps_nil))))
      (evalExp_con (evalExps_cons (evalExp_callE_iff.2 ((callDef_iff_try hρ (findDef_fdef rfl)
        (builtins_envF _) (evalArgs_vars3 rfl rfl rfl)).2 hc)) evalExps_nil)))

theorem binNum_mk {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : BinOp}
    (ho : TypedV envF (.varT "numbinop" []) (encBinOp op)) {m₁ m₂ m : Num} (hm₁ : NatInt m₁)
    (hm₂ : NatInt m₂) (hp : ¬ IntPow op m₁ m₂) (h : Num.bin op m₁ m₂ = some m) :
    MStep envF S (con "BIN" [encBinOp op, encNum m₁, encNum m₂]) (encNum m) := by
  let σ : List (IL.Id × Value) :=
    [("S", S), ("numbinop", encBinOp op), ("num_1", encNum m₁), ("num_2", encNum m₂)]
  have hρ := valsOnly_inst σ
  have hc : TryClauses envF Rules.F.numbinF (args3 (encBinOp op) (encNum m₁) (encNum m₂))
      (encNum m) := by
    have := numbin_spec op hm₁ hm₂ hp
    unfold NB at this
    rw [h] at this
    exact this
  refine mstep_mk stepF_6 σ ?_ ?_ no_prems
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (typedV_encNum hm₁ _ hρ)
        (Sim.QuantsOk.cons rfl (typedV_encNum hm₂ _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_sub (evalExp_var rfl)) (evalExp_sub (evalExp_var rfl))
        (evalExp_sub (evalExp_var rfl))))
      (evalExp_sub (evalExp_callE_iff.2 ((callDef_iff_try hρ findDef_numbin
        (builtins_envF _) (evalArgs_vars3 rfl rfl rfl)).2 hc))))

theorem cmpNum_mk {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : CmpOp}
    (ho : TypedV envF (.varT "numcmpop" []) (encCmpOp op)) {m₁ m₂ : Num} {b : Bool}
    (hm₁ : NatInt m₁) (hm₂ : NatInt m₂) (h : Num.cmp op m₁ m₂ = some b) :
    MStep envF S (con "CMP" [encCmpOp op, encNum m₁, encNum m₂]) (con "BOOL" [.bool b]) := by
  let σ : List (IL.Id × Value) :=
    [("S", S), ("numcmpop", encCmpOp op), ("num_1", encNum m₁), ("num_2", encNum m₂)]
  have hρ := valsOnly_inst σ
  have hc : TryClauses envF (fdef "numcmp").2.2 (args3 (encCmpOp op) (encNum m₁) (encNum m₂))
      (.bool b) := by
    have := numcmp_spec op hm₁ hm₂
    rw [h] at this
    exact this
  refine mstep_mk stepF_13 σ ?_ ?_ no_prems
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ho _ hρ)
      (Sim.QuantsOk.cons rfl (typedV_encNum hm₁ _ hρ)
        (Sim.QuantsOk.cons rfl (typedV_encNum hm₂ _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_sub (evalExp_var rfl)) (evalExp_sub (evalExp_var rfl))
        (evalExp_sub (evalExp_var rfl))))
      (evalExp_con (evalExps_cons (evalExp_callE_iff.2 ((callDef_iff_try hρ (findDef_fdef rfl)
        (builtins_envF _) (evalArgs_vars3 rfl rfl rfl)).2 hc)) evalExps_nil)))

/-- The four comparison rules on values (`k = 9 … 12`). -/
theorem cmpVal_mk {k : Nat} {nm : IL.Id} {C : MixopS} {r : Bool} {t : CmpOp}
    (hk : (rulesOf envF "Step_exp")[k]? = some (.ruleD nm [.expP "S" (.varT "S" []),
      .expP "val_1" (.varT "val" []), .expP "val_2" (.varT "val" [])] "%|-%~>%"
      (.tupE [.varE "S", .caseE "CMP" (.tupE [.caseE C (.tupE []),
        .subE (.varE "val_1") (.varT "val" []) (.varT "exp" []),
        .subE (.varE "val_2") (.varT "val" []) (.varT "exp" [])]),
        .caseE "BOOL" (.tupE [.boolE r])])
      [.ifPr (.cmpE t .boolT (.varE "val_1") (.varE "val_2"))]))
    {S u v : Value} (hS : TypedV envF (.varT "S" []) S) (hu : IsLitV u) (hv : IsLitV v)
    (h : cmpValues t (encVal u) (encVal v) = .ok (.bool true)) :
    MStep envF S (con "CMP" [con C [], encVal u, encVal v]) (con "BOOL" [.bool r]) := by
  let σ : List (IL.Id × Value) := [("S", S), ("val_1", encVal u), ("val_2", encVal v)]
  have hρ := valsOnly_inst σ
  refine mstep_mk hk σ ?_ ?_ (Sim.prems_one (.ifPr (evalExp_cmpE_iff.2
    ⟨_, _, evalExp_var rfl, evalExp_var rfl, h⟩)))
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (typedV_lit_val hu _ hρ)
      (Sim.QuantsOk.cons rfl (typedV_lit_val hv _ hρ) Sim.QuantsOk.nil))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_con evalExps_nil) (evalExp_sub (evalExp_var rfl))
        (evalExp_sub (evalExp_var rfl))))
      (evalExp_con (evalExps_cons (evalExp_boolE_iff.2 rfl) evalExps_nil)))

end Silmaril.Wasm.SpecTec.Meta
