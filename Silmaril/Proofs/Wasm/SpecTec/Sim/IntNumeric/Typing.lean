module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Calls

/-!
# Integer numerics: the quantified values are typed (`intTyping_simEnv`)

`IntTyping (simEnv B)`: the encodings of Core's integer types, bit patterns and operators inhabit
the IL types the integer rules quantify over (`numtype`, `num_(Inn)`, `unop_(Inn)`,
`binop_(Inn)`, `testop_(Inn)`, `relop_(Inn)`), computed through the fixed script's own type
definitions (`Original.d22`, `d24`, `d89`, `d210`, `d215`–`d220`), including the premises of
`uN(N)` (`i ≤ 2^N - 1`), `sz` (`8 | 16 | 32 | 64`) and `unop_`'s `EXTEND` (`sz < $sizenn(Inn)`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d22 Original.d24 Original.d89 Original.d210
  Original.d215 Original.d216 Original.d217 Original.d218 Original.d219 Original.d220)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

/-! ## Reading type definitions off the script -/

/-- The cases of the `k`-th instance of a variant type definition. -/
def instCases (d : Def) (k : Nat) : List TypCase :=
  match d with
  | .typD _ _ is => match is[k]? with
    | some (.instD _ _ (.variantT cs)) => cs
    | _ => []
  | _ => []

/-- The type and premises of the case `op` of a variant, if declared. -/
def findCase : List TypCase → MixopS → Option (Typ × List Prem)
  | [], _ => none
  | .mk o t _ prems :: cs, op => if o = op then some (t, prems) else findCase cs op

/-- The case `op` of a variant defines no quantifier (`Sem.quantDefs`), so its premises are read
in the scope its payload binds. -/
def quantFreeAt : List TypCase → MixopS → Bool
  | [], _ => true
  | .mk o _ qs prems :: cs, op =>
      if o = op then (quantDefs qs prems).isEmpty else quantFreeAt cs op

theorem hasTypCase_of_findCase_aux {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {t : Typ} {prems : List Prem} {w : Value},
      findCase cs op = some (t, prems) → HasTyp env σ t w →
      PremsOk env (caseScope σ t w) prems → quantFreeAt cs op = true →
      HasTypCase env σ cs op w
  | [], _, _, _, _, hf, _, _, _ => by simp [findCase] at hf
  | .mk o t' qs prems' :: cs, op, t, prems, w, hf, ht, hp, hq => by
      by_cases ho : o = op
      · simp only [findCase, ho, ite_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        simp only [quantFreeAt, ho, ite_true] at hq
        exact (hasTypCase_cons_hit_iff ho (List.isEmpty_iff.1 hq)).2 ⟨ht, hp⟩
      · simp only [findCase, ho, ite_false] at hf
        simp only [quantFreeAt, ho, ite_false] at hq
        exact (hasTypCase_cons_miss_iff ho).2 (hasTypCase_of_findCase_aux hf ht hp hq)

/-- A case found in the list, defining no quantifier, is inhabited by any payload of its type
satisfying its premises. -/
theorem hasTypCase_of_findCase {env : Env} {σ : VarEnv} {cs : List TypCase} {op : MixopS}
    {t : Typ} {prems : List Prem} {w : Value} (hf : findCase cs op = some (t, prems))
    (ht : HasTyp env σ t w) (hp : PremsOk env (caseScope σ t w) prems)
    (hq : quantFreeAt cs op = true := by rfl) : HasTypCase env σ cs op w :=
  hasTypCase_of_findCase_aux hf ht hp hq

/-- A premise list that holds is `PremsOk`. -/
theorem premsOk_of_hold {env : Env} {ρ ρ' : VarEnv} {prems : List Prem}
    (h : PremsHold env ρ prems ρ') : PremsOk env ρ prems := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, by rw [premsOk, h, Res.elimUndef_ok]⟩

/-- One `if` premise that evaluates to `true`. -/
theorem premsOk_if {env : Env} {ρ : VarEnv} {e : Exp} (h : EvalExp env ρ e (.bool true)) :
    PremsOk env ρ [.ifPr e] :=
  premsOk_of_hold (Equiv.Validation.premsHold_cons_iff.2 ⟨_,
    Equiv.Validation.premHolds_if_iff.2 ⟨rfl, h⟩, Equiv.Validation.premsHold_nil_iff.2 rfl⟩)

/-- A case without premises defines no quantifier. -/
theorem quantFreeAt_of_findCase_nil :
    ∀ {cs : List TypCase} {op : MixopS} {t : Typ}, findCase cs op = some (t, []) →
      quantFreeAt cs op = true
  | [], _, _, h => by simp [findCase] at h
  | .mk o t' qs prems :: cs, op, t, h => by
      by_cases ho : o = op
      · simp only [findCase, ho, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [quantFreeAt, ho, quantDefs]
      · simp only [findCase, ho, ite_false] at h
        simp only [quantFreeAt, ho, ite_false]
        exact quantFreeAt_of_findCase_nil h

/-- A nullary case: payload `()`, no premise. -/
theorem hasTypCase_nullary {env : Env} {σ : VarEnv} {cs : List TypCase} {op : MixopS}
    (hf : findCase cs op = some (.tupT [], [])) : HasTypCase env σ cs op (.tuple []) :=
  hasTypCase_of_findCase hf hasTyp_tupT_nil premsOk_nil (quantFreeAt_of_findCase_nil hf)

/-- `p ∧ q` on booleans. -/
theorem evalExp_and {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp} {q : Bool}
    (h₁ : EvalExp env ρ e₁ (.bool true)) (h₂ : EvalExp env ρ e₂ (.bool q)) :
    EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool q) := by
  refine evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨by simp [boolShort], _, h₂, ?_⟩⟩
  cases q <;> simp [binValues, boolBin]

variable {B : Builtins}

/-! ## Closed variants: `numtype`, `sx` -/

set_option maxRecDepth 100000 in
theorem findTyp_numtype :
    (simEnv B).findTyp? "numtype" =
      some ([], [.instD [] [] (.variantT (instCases Original.d89 0))]) :=
  rfl

set_option maxRecDepth 100000 in
theorem findTyp_sx :
    (simEnv B).findTyp? "sx" = some ([], [.instD [] [] (.variantT (instCases Original.d216 0))]) :=
  rfl

/-- A closed variant `x` holds a nullary case it declares. -/
theorem hasTyp_closedNullary {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {cs : List TypCase}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)])) {op : MixopS}
    (hf : findCase cs op = some (.tupT [], [])) :
    HasTyp (simEnv B) ρ (.varT x []) (.case op (.tuple [])) := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  exact hasTyp_varT_case hl htd Equiv.evalArgs_nil matchArgs_nil (hasTypCase_nullary hf)

/-- `numtype` holds `I32`, `I64`. -/
theorem hasTyp_numtype {ρ : VarEnv} (hρ : ValsOnly ρ) (t : Silmaril.Wasm.IntType) :
    HasTyp (simEnv B) ρ (.varT "numtype" []) (ntV t) := by
  cases t
  · exact hasTyp_closedNullary hρ findTyp_numtype rfl
  · exact hasTyp_closedNullary hρ findTyp_numtype rfl

/-- `sx` holds `U`, `S`. -/
theorem hasTyp_sx {ρ : VarEnv} (hρ : ValsOnly ρ) (s : Silmaril.Wasm.Signedness) :
    HasTyp (simEnv B) ρ (.varT "sx" []) (Equiv.sxV s) := by
  cases s
  · exact hasTyp_closedNullary hρ findTyp_sx rfl
  · exact hasTyp_closedNullary hρ findTyp_sx rfl


/-! ## `uN(N)`, `iN(N)`, `num_(Inn)` -/

set_option maxRecDepth 100000 in
theorem findTyp_uN : ∃ ps qs, (simEnv B).findTyp? "uN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d22 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_iN : ∃ ps qs, (simEnv B).findTyp? "iN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.aliasT (.varT "uN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

/-- The `Inn` argument pattern of the integer type families. -/
abbrev innPat : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])

set_option maxRecDepth 100000 in
theorem findTyp_num : ∃ ps qs rest, (simEnv B).findTyp? "num_" =
    some (ps, .instD qs [.expA innPat]
      (.aliasT (.varT "iN" [.expA (.callE "sizenn" [.expA innPat])])) :: rest) :=
  ⟨_, _, _, rfl⟩

/-- `uN(N)` holds every natural below `2^N`, through the case premise
`i >= 0 /\ i <= 2^N - 1`. -/
theorem hasTyp_uN {ρ : VarEnv} {e : Exp} {N n : Nat} (he : EvalExp (simEnv B) ρ e (natV N))
    (hn : n < 2 ^ N) :
    HasTyp (simEnv B) ρ (.varT "uN" [.expA e]) (.case "%" (.tuple [natV n])) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_uN (B := B)
  have hσ : (VarEnv.empty.bindVal "N" (natV N)).findVal? "N" = some (natV N) := by simp
  have htup : HasTyp (simEnv B) (VarEnv.empty.bindVal "N" (natV N))
      (.tupT [.mk "i" (.numT .natT)]) (.tuple [natV n]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hpow : EvalExp (simEnv B) ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV n))
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (by simp)
  have hsub := evalExp_binNum (op := .subOp) (t := .numT .intT) (Equiv.evalExp_toInt hpow)
    Equiv.evalExp_oneInt (m := .intN ((2 ^ N : Nat) - 1)) rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := natV n) rfl) evalExp_num (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := natV n) rfl) hk ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- `num_(Inn)` holds every bit pattern of the width, through `iN($sizenn(Inn))`. -/
theorem hasTyp_num {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType} (b : BitVec t.width)
    (he : EvalExp (simEnv B) ρ e (ntV t)) :
    HasTyp (simEnv B) ρ (.varT "num_" [.expA e]) (bvV b) := by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_num (B := B)
  obtain ⟨ps', qs', htd'⟩ := findTyp_iN (B := B)
  have hInn : (VarEnv.empty.bindVal "Inn" (ntV t)).findVal? "Inn" = some (ntV t) := by simp
  have hiN : HasTyp (simEnv B) (VarEnv.empty.bindVal "Inn" (ntV t))
      (.varT "iN" [.expA (.callE "sizenn" [.expA innPat])]) (bvV b) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd'
      (Equiv.evalArgs_cons (evalExp_sizennInn t rfl hInn) Equiv.evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (hasTyp_uN (evalExp_var (by simp)) b.isLt)))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_InnPat (by simp) (argSubOk_innPat_ntV _)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 hiN))


/-! ## The operator families `unop_`, `binop_`, `testop_`, `relop_` at `Inn` -/

set_option maxRecDepth 100000 in
theorem findTyp_unop : ∃ ps qs rest, (simEnv B).findTyp? "unop_" =
    some (ps, .instD qs [.expA innPat] (.variantT (instCases Original.d217 0)) :: rest) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_binop : ∃ ps qs rest, (simEnv B).findTyp? "binop_" =
    some (ps, .instD qs [.expA innPat] (.variantT (instCases Original.d218 0)) :: rest) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_testop : ∃ ps qs rest, (simEnv B).findTyp? "testop_" =
    some (ps, .instD qs [.expA innPat] (.variantT (instCases Original.d219 0)) :: rest) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_relop : ∃ ps qs rest, (simEnv B).findTyp? "relop_" =
    some (ps, .instD qs [.expA innPat] (.variantT (instCases Original.d220 0)) :: rest) :=
  ⟨_, _, _, rfl⟩

/-- A type family whose first instance is a variant at `Inn` holds that variant's cases. -/
theorem hasTyp_innVariant {ρ : VarEnv} {x : IL.Id} {e : Exp} {t : Silmaril.Wasm.IntType}
    {ps qs : List Param} {cs : List TypCase} {rest : List Inst} {op : MixopS} {w : Value}
    (htd : (simEnv B).findTyp? x = some (ps, .instD qs [.expA innPat] (.variantT cs) :: rest))
    (he : EvalExp (simEnv B) ρ e (ntV t))
    (hc : HasTypCase (simEnv B) (VarEnv.empty.bindVal "Inn" (ntV t)) cs op w) :
    HasTyp (simEnv B) ρ (.varT x [.expA e]) (.case op w) :=
  hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_InnPat (by simp) (argSubOk_innPat_ntV _)) matchArgs_nil)
      (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩))

/-- A case carrying an `sx`, with no premise. -/
theorem hasTypCase_sx {σ : VarEnv} (hσ : ValsOnly σ) {cs : List TypCase} {op : MixopS}
    (hf : findCase cs op = some (.varT "sx" [], [])) (s : Silmaril.Wasm.Signedness) :
    HasTypCase (simEnv B) σ cs op (Equiv.sxV s) :=
  hasTypCase_of_findCase hf (hasTyp_sx hσ s) premsOk_nil (quantFreeAt_of_findCase_nil hf)

/-- `binop_(Inn)` holds every integer binary operator. -/
theorem hasTyp_binop {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType}
    (he : EvalExp (simEnv B) ρ e (ntV t)) (op : Silmaril.Wasm.IntBinOp) :
    HasTyp (simEnv B) ρ (.varT "binop_" [.expA e]) (ibinopV op) := by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_binop (B := B)
  have hσ : ValsOnly (VarEnv.empty.bindVal "Inn" (ntV t)) := ⟨rfl, rfl, rfl⟩
  cases op with
  | div s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)
  | rem s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)
  | shr s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)
  | _ => exact hasTyp_innVariant htd he (hasTypCase_nullary rfl)

/-- `relop_(Inn)` holds every integer comparison. -/
theorem hasTyp_relop {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType}
    (he : EvalExp (simEnv B) ρ e (ntV t)) (op : Silmaril.Wasm.IntRelOp) :
    HasTyp (simEnv B) ρ (.varT "relop_" [.expA e]) (irelopV op) := by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_relop (B := B)
  have hσ : ValsOnly (VarEnv.empty.bindVal "Inn" (ntV t)) := ⟨rfl, rfl, rfl⟩
  cases op with
  | eq => exact hasTyp_innVariant htd he (hasTypCase_nullary rfl)
  | ne => exact hasTyp_innVariant htd he (hasTypCase_nullary rfl)
  | lt s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)
  | gt s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)
  | le s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)
  | ge s => exact hasTyp_innVariant htd he (hasTypCase_sx hσ rfl s)

/-- `testop_(Inn)` holds `EQZ`. -/
theorem hasTyp_testop {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType}
    (he : EvalExp (simEnv B) ρ e (ntV t)) (op : Silmaril.Wasm.IntTestOp) :
    HasTyp (simEnv B) ρ (.varT "testop_" [.expA e]) (itestopV op) := by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_testop (B := B)
  cases op
  exact hasTyp_innVariant htd he (hasTypCase_nullary rfl)

/-! ### `unop_`, whose `EXTEND sz` carries a premise -/

set_option maxRecDepth 100000 in
theorem findTyp_sz :
    (simEnv B).findTyp? "sz" = some ([], [.instD [] [] (.variantT (instCases Original.d215 0))]) :=
  rfl

/-- `p ∨ q` on booleans, any values. -/
theorem evalExp_orB {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp} {a b : Bool}
    (h₁ : EvalExp env ρ e₁ (.bool a)) (h₂ : EvalExp env ρ e₂ (.bool b)) :
    EvalExp env ρ (.binE .orOp t e₁ e₂) (.bool (a || b)) := by
  refine evalExp_binE_iff.2 ⟨_, h₁, ?_⟩
  cases a
  · exact .inr ⟨by simp [boolShort], _, h₂, by cases b <;> simp [binValues, boolBin]⟩
  · exact .inl (by simp [boolShort])

/-- A `%`-wrapped natural, read through `x!%.0`. -/
theorem evalExp_pctPayload {env : Env} {ρ : VarEnv} {x : IL.Id} {n : Nat}
    (h : ρ.findVal? x = some (.case "%" (.tuple [.num (.natN n)]))) :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) (.num (.natN n)) :=
  evalExp_projE_iff.2 ⟨[.num (.natN n)], evalExp_uncaseE_iff.2 (evalExp_var h), Int.le_refl 0, rfl⟩

/-- `sz` holds the four pack widths. -/
theorem hasTyp_sz {ρ : VarEnv} (hρ : ValsOnly ρ) (p : Silmaril.Wasm.PackSize) :
    HasTyp (simEnv B) ρ (.varT "sz" []) (.case "%" (.tuple [.num (.natN p.width)])) := by
  have hl : localTyp? ρ "sz" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have htup : HasTyp (simEnv B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN p.width)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_varT_case hl findTyp_sz Equiv.evalArgs_nil matchArgs_nil
    (hasTypCase_of_findCase rfl htup (premsOk_if ?_))
  have hi : (caseScope VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN p.width)])).findVal? "i" = some (.num (.natN p.width)) := rfl
  have hor := evalExp_orB (env := simEnv B) (t := .boolT) (evalExp_orB (t := .boolT)
    (evalExp_orB (t := .boolT)
    (evalExp_eq (t := .boolT) (evalExp_var hi) (evalExp_num (m := .natN 8)))
    (evalExp_eq (t := .boolT) (evalExp_var hi) (evalExp_num (m := .natN 16))))
    (evalExp_eq (t := .boolT) (evalExp_var hi) (evalExp_num (m := .natN 32))))
    (evalExp_eq (t := .boolT) (evalExp_var hi) (evalExp_num (m := .natN 64)))
  cases p <;> simpa [Silmaril.Wasm.PackSize.width] using hor

/-- `unop_(Inn)` holds every operator valid at the type: `EXTEND sz` needs
`sz < $sizenn(Inn)`. -/
theorem hasTyp_unop {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType}
    (he : EvalExp (simEnv B) ρ e (ntV t)) (op : Silmaril.Wasm.IntUnOp)
    (hv : op.valid t = true) :
    HasTyp (simEnv B) ρ (.varT "unop_" [.expA e]) (iunopV op) := by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_unop (B := B)
  have hσ : ValsOnly (VarEnv.empty.bindVal "Inn" (ntV t)) := ⟨rfl, rfl, rfl⟩
  cases op with
  | extend p =>
      have hlt : p.width < t.width := by simpa [Silmaril.Wasm.IntUnOp.valid] using hv
      have htup : HasTyp (simEnv B) (VarEnv.empty.bindVal "Inn" (ntV t))
          (.tupT [.mk "sz" (.varT "sz" [])]) (.tuple [.case "%" (.tuple [.num (.natN p.width)])]) :=
        hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_sz hσ p,
          hasTypTup_nil_iff.2 rfl⟩⟩
      refine hasTyp_innVariant htd he (hasTypCase_of_findCase rfl htup (premsOk_if ?_))
      exact evalExp_cmpNum (evalExp_pctPayload rfl) (evalExp_sizennInn t rfl rfl)
        (by simp [Num.cmp, hlt])
  | _ => exact hasTyp_innVariant htd he (hasTypCase_nullary rfl)

/-! ## The interface, discharged -/

/-- **The integer quantifier typings hold in `simEnv B`.** -/
theorem intTyping_simEnv (B : Builtins) : IntTyping (simEnv B) where
  numtype _ t hρ := hasTyp_numtype hρ t
  num _ _ _ b _ he := hasTyp_num b he
  unop _ _ _ op hv _ he := hasTyp_unop he op hv
  binop _ _ _ op _ he := hasTyp_binop he op
  testop _ _ _ op _ he := hasTyp_testop he op
  relop _ _ _ op _ he := hasTyp_relop he op

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
