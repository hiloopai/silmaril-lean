module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Eval
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Sound

/-!
# The original script disagrees: witnesses

Read by `DDerives`, the original `Step_exp`/`$numbin` (before errata M1, M2) gets fragment
expressions wrong in both directions:

* `original_mod`: `6 \ 3` reduces to `2` (MOD is division); ours gives `0`;
* `original_one_eq_two`: `1 = 1 + 1` reduces to `true` (the typo in `CMP-ctx2` replaces the left
  operand by anything, here `1 + 1`, and `CMP-EQ-true` compares expressions); ours gives `false`;
* `original_ne_stuck`: `k =/= 0` with `k ≠ 0` does not reduce to `true` (`CMP-NE-true` is
  missing); ours gives `true`;
* `original_mod_pow_stuck`: `(a + b) \ 2^N` — the arithmetic of `$iadd_` — reduces to no value at
  all, because `BIN-ctx2` never reduces the right operand `2^N`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives DPrem QuantsOk TypedV ValsOnly RuleBody otherwise)

set_option maxRecDepth 100000

/-! ## Rule lookup in the original -/

theorem headsO_bin : headIdx (rulesOf envO "Step_exp") "BIN" = [3, 4, 5, 6] := by decide
theorem headsO_cmp : headIdx (rulesOf envO "Step_exp") "CMP" = [7, 8, 9, 10, 11] := by decide
theorem headsO_nat : headIdx (rulesOf envO "Step_exp") "NAT" = [] := by decide

theorem headsO_all : ∀ (i : Nat) (r : Rule), (rulesOf envO "Step_exp")[i]? = some r →
    (lhsHead r).isSome := by
  intro i r h
  have hi : i < (rulesOf envO "Step_exp").length := (List.getElem?_eq_some_iff.1 h).1
  have hall : ∀ j < (rulesOf envO "Step_exp").length,
      (((rulesOf envO "Step_exp")[j]?).bind lhsHead).isSome := by decide
  have := hall i hi
  rwa [h] at this

theorem stepO_rule {S w x : Value} {c : MixopS} (h : MStep envO S (.case c w) x) :
    ∃ i r, (rulesOf envO "Step_exp")[i]? = some r ∧ i ∈ headIdx (rulesOf envO "Step_exp") c ∧
      RuleBody envO (DDerives envO (otherwise envO))
        (otherwise envO "Step_exp" [] i (.tuple [S, .case c w, x])) [] [] "%|-%~>%" r
        (.tuple [S, .case c w, x]) := by
  obtain ⟨ps, t, rules, i, r, hrel, hr, hb⟩ := Sim.dderives_iff.1 h
  rw [findRel_stepO] at hrel
  have e : [] = ps ∧ sxxT = t ∧ rulesOf envO "Step_exp" = rules := by simpa using hrel
  obtain ⟨rfl, rfl, rfl⟩ := e
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (headsO_all i r hr)
  have hc : c' = c := head_of_body hb hc'
  subst hc
  exact ⟨i, r, hr, mem_headIdx hr hc', hb⟩

theorem stepO_nat {S x : Value} {n : Nat} (h : MStep envO S (FExp.nat n).enc x) : False := by
  obtain ⟨i, r, -, hi, -⟩ := stepO_rule (c := "NAT") (w := .tuple [.num (.natN n)]) h
  rw [headsO_nat] at hi
  cases hi

/-- A term with no step reduces only to itself. -/
theorem reduceO_irreducible {S a c : Value} (h : MReduce envO S a c)
    (hno : ∀ b, MStep envO S a b → False) : c = a := by
  have key := reduce_rec findRel_reduceO rfl rfl
    (fun S a c => (∀ b, MStep envO S a b → False) → c = a)
    (fun _ _ _ => rfl) (fun _ _ _ _ hab _ hno => (hno _ hab).elim) h
  exact key hno

/-! ## The original's own rules, inverted -/

/-- `CMP-EQ-true` and `CMP-NE-false` of the original compare expressions. -/
theorem cmpExp_inv {env : Env} {D : Sim.Interp} {els : Prop} {nm : IL.Id} {C : MixopS} {r : Bool}
    {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" (.ruleD nm [.expP "S" (.varT "S" []),
      .expP "e_1" (.varT "exp" []), .expP "e_2" (.varT "exp" [])] "%|-%~>%"
      (.tupE [.varE "S", .caseE "CMP" (.tupE [.caseE C (.tupE []), .varE "e_1", .varE "e_2"]),
        .caseE "BOOL" (.tupE [.boolE r])])
      [.ifPr (.cmpE .eqOp .boolT (.varE "e_1") (.varE "e_2"))])
      (.tuple [S, con "CMP" [o, a, b], x])) :
    o = con C [] ∧ a = b := by
  obtain ⟨ρ, -, hq, he, hp⟩ := ruleBody_inv h
  obtain ⟨v₁, hv₁, -⟩ := quant_val hq "e_1" (t := .varT "exp" []) (by simp)
  obtain ⟨v₂, hv₂, -⟩ := quant_val hq "e_2" (t := .varT "exp" []) (by simp)
  obtain ⟨-, h₂, -⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_three (evalExp_con evalExps_nil)
    (evalExp_var hv₁) (evalExp_var hv₂)))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  have hk : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "e_1") (.varE "e_2")) (.bool true) := by
    cases hp _ (List.mem_singleton_self _) with | ifPr h => exact h
  have he' := hk.unique (evalExp_eq (evalExp_var hv₁) (evalExp_var hv₂))
  exact ⟨rfl, by simpa using he'⟩

/-- The original `BIN-ctx2`/`CMP-ctx2`: the right operand stays, the left one becomes any
expression. -/
theorem ctx2O_inv {env : Env} {D : Sim.Interp} {els : Prop} {C : MixopS} {T : Typ} {nm : IL.Id}
    {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" (.ruleD nm [.expP "S" (.varT "S" []), .expP "op" T,
      .expP "e_1" (.varT "exp" []), .expP "e_2" (.varT "exp" []), .expP "e_1'" (.varT "exp" []),
      .expP "e_2'" (.varT "exp" [])]
      "%|-%~>%" (.tupE [.varE "S", .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2"]),
        .caseE C (.tupE [.varE "op", .varE "e_1'", .varE "e_2"])])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e_2", .varE "e_2'"])])
      (.tuple [S, con C [o, a, b], x])) :
    ∃ w w', x = con C [o, w, b] ∧ D "Step_exp" "%|-%~>%" [] (.tuple [S, b, w']) := by
  obtain ⟨ρ, -, hq, he, hp⟩ := ruleBody_inv h
  obtain ⟨vS, hS, -⟩ := quant_val hq "S" (t := .varT "S" []) (by simp)
  obtain ⟨vo, ho, -⟩ := quant_val hq "op" (t := T) (by simp)
  obtain ⟨v₁, h₁, -⟩ := quant_val hq "e_1" (t := .varT "exp" []) (by simp)
  obtain ⟨v₂, h₂, -⟩ := quant_val hq "e_2" (t := .varT "exp" []) (by simp)
  obtain ⟨v₁', h₁', -⟩ := quant_val hq "e_1'" (t := .varT "exp" []) (by simp)
  obtain ⟨v₂', h₂', -⟩ := quant_val hq "e_2'" (t := .varT "exp" []) (by simp)
  have hv := he.unique (evalExp_tuple (evalExps_three (evalExp_var hS)
    (evalExp_con (evalExps_three (evalExp_var ho) (evalExp_var h₁) (evalExp_var h₂)))
    (evalExp_con (evalExps_three (evalExp_var ho) (evalExp_var h₁') (evalExp_var h₂)))))
  simp only [con, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hv
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hv
  exact ⟨v₁', v₂', rfl, premW_rule3 hS h₂ h₂' (hp _ (by simp))⟩

/-! ## The closed variant types of the original -/

/-- The cases of the closed variant type `x` in `original`. -/
noncomputable def casesO (x : IL.Id) : List TypCase :=
  match envO.findTyp? x with
  | some ([], [.instD [] [] (.variantT cs)]) => cs
  | _ => []

theorem variantO_num : VariantDef envO "num" (casesO "num") := rfl
theorem opsO_num : (casesO "num").map TypCase.op = ["NAT", "INT", "RAT", "REAL"] := rfl
theorem variantO_numcmpop : VariantDef envO "numcmpop" (casesO "numcmpop") := rfl
theorem opsO_numcmpop : (casesO "numcmpop").map TypCase.op = ["LT", "GT", "LE", "GE"] := rfl

/-- A value of type `num` in the original is not a `BIN`. -/
theorem not_num_BIN {w : Value} (h : TypedIn envO (.varT "num" []) (.case "BIN" w)) : False := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨c, w', he, hc⟩ := case_of_typed hρ variantO_num ht
  rw [opsO_num] at hc
  obtain ⟨rfl, -⟩ := Value.case.inj he
  simp at hc

/-- `NE` is not a `numcmpop`. -/
theorem not_numcmpop_NE (h : TypedIn envO (.varT "numcmpop" []) (con "NE" [])) : False := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨c, w', he, hc⟩ := case_of_typed hρ variantO_numcmpop ht
  rw [opsO_numcmpop] at hc
  obtain ⟨rfl, -⟩ := Value.case.inj he
  simp at hc

/-- The definition of `f` in `original` (a dummy if there is none). -/
noncomputable def fdefO (f : IL.Id) : DefDef := (envO.findDef? f).getD ([], .boolT, [])

theorem findDef_fdefO {f : IL.Id} (h : (envO.findDef? f).isSome = true) :
    envO.findDef? f = some (fdefO f) := by
  unfold fdefO
  cases e : envO.findDef? f with
  | none => rw [e] at h; cases h
  | some d => rfl

theorem builtins_envO (f : IL.Id) (ws : List ArgV) : envO.builtins.call f ws = none := rfl

/-! ## Negative witnesses -/

theorem ne_numcmp_undef {S x : Value} {k : Nat} {D : Sim.Interp} {els : Prop}
    (hb : RuleBody envO D els [] [] "%|-%~>%" Rules.O.cmpNum
      (.tuple [S, con "CMP" [encCmpOp .neOp, encNum (.natN k), encNum (.natN 0)], x])) : False := by
  obtain ⟨-, -, w, -, htc⟩ := cmpNum_inv (findDef_fdefO rfl) (builtins_envO _) hb
  exact TryUndef.not (⟨30, by with_unfolding_all rfl⟩ :
    TryUndef envO (fdefO "numcmp").2.2 (args3 (con "NE" []) (encNum (.natN k))
      (encNum (.natN 0)))) htc

theorem ne_eqTrue {S x : Value} {k : Nat} {D : Sim.Interp} {els : Prop}
    (hb : RuleBody envO D els [] [] "%|-%~>%" Rules.O.cmpEqTrue
      (.tuple [S, con "CMP" [encCmpOp .neOp, encNum (.natN k), encNum (.natN 0)], x])) : False := by
  obtain ⟨ho, -⟩ := cmpExp_inv hb
  simp [encCmpOp, con] at ho

theorem ne_neFalse {S x : Value} {k : Nat} (hk : k ≠ 0) {D : Sim.Interp} {els : Prop}
    (hb : RuleBody envO D els [] [] "%|-%~>%" Rules.O.cmpNeFalse
      (.tuple [S, con "CMP" [encCmpOp .neOp, encNum (.natN k), encNum (.natN 0)], x])) : False := by
  obtain ⟨-, he⟩ := cmpExp_inv hb
  exact hk (by simpa [encNum, con] using he)

/-- `k =/= 0` has no step in the original: `CMP-NE-true` is missing. -/
theorem stepO_ne_none {S x : Value} {t : OpTyp} {k : Nat} (hk : k ≠ 0)
    (h : MStep envO S (FExp.cmp .neOp t (.nat k) (.nat 0)).enc x) : False := by
  obtain ⟨i, r, hr, hi, hb⟩ := stepO_rule (c := "CMP")
    (w := .tuple [encCmpOp .neOp, (FExp.nat k).enc, (FExp.nat 0).enc]) h
  rw [headsO_cmp] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact stepO_nat (ctx1_inv (rule_at hr stepO_7 ▸ hb)).choose_spec.2
  · exact stepO_nat (ctx2O_inv (rule_at hr stepO_8 ▸ hb)).choose_spec.choose_spec.2
  · exact ne_eqTrue (rule_at hr stepO_9 ▸ hb)
  · exact ne_neFalse hk (rule_at hr stepO_10 ▸ hb)
  · exact ne_numcmp_undef (rule_at hr stepO_11 ▸ hb)

/-- **Missing `CMP-NE-true`**: in the original, `k =/= 0` never reduces to `true` for `k ≠ 0`,
although our evaluator gives it `true`. -/
theorem original_ne_stuck {S : Value} {t : OpTyp} {k : Nat} (hk : k ≠ 0) :
    ¬ MReduce envO S (FExp.cmp .neOp t (.nat k) (.nat 0)).enc (encVal (.bool true)) := by
  intro h
  have := reduceO_irreducible h fun _ hb => stepO_ne_none hk hb
  simp [FExp.enc, encVal, con] at this

/-- `(a + b) \ 2^N`, the arithmetic of the `$iadd_` clause of wasm-3.0 at `N`. -/
def modPow (a b N : Nat) : FExp :=
  .bin .modOp (.numT .natT) (.bin .addOp (.numT .natT) (.nat a) (.nat b))
    (.bin .powOp (.numT .natT) (.nat 2) (.nat N))

/-- The right operand `2^N` of `modPow`, encoded. -/
abbrev powEnc (N : Nat) : Value := (FExp.bin .powOp (.numT .natT) (.nat 2) (.nat N)).enc

theorem modPow_binBool {S x l : Value} {N : Nat} {D : Sim.Interp} {els : Prop}
    (hb : RuleBody envO D els [] [] "%|-%~>%" Rules.O.binBool
      (.tuple [S, con "BIN" [encBinOp .modOp, l, powEnc N], x])) : False := by
  obtain ⟨-, b₂, -, -, hb₂, -⟩ := binBool_inv (findDef_fdefO rfl) (builtins_envO _) hb
  simp [FExp.enc, con] at hb₂

theorem modPow_binNum {S x l : Value} {N : Nat} {D : Sim.Interp} {els : Prop}
    (hb : RuleBody envO D els [] [] "%|-%~>%" Rules.O.binNum
      (.tuple [S, con "BIN" [encBinOp .modOp, l, powEnc N], x])) : False := by
  obtain ⟨-, hb₂, -⟩ := binNum_inv (findDef_fdefO rfl) (builtins_envO _) hb
  exact not_num_BIN hb₂

/-- A step from `C (MOD, l, 2^N)` keeps the shape: only the left operand can change. -/
theorem stepO_modPow {S x l : Value} {N : Nat}
    (h : MStep envO S (con "BIN" [encBinOp .modOp, l, powEnc N]) x) :
    ∃ l', x = con "BIN" [encBinOp .modOp, l', powEnc N] := by
  obtain ⟨i, r, hr, hi, hb⟩ := stepO_rule (c := "BIN")
    (w := .tuple [encBinOp .modOp, l, powEnc N]) h
  rw [headsO_bin] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · obtain ⟨w, hw, -⟩ := ctx1_inv (rule_at hr stepO_3 ▸ hb)
    exact ⟨w, hw⟩
  · obtain ⟨w, -, hw, -⟩ := ctx2O_inv (rule_at hr stepO_4 ▸ hb)
    exact ⟨w, hw⟩
  · exact (modPow_binBool (rule_at hr stepO_5 ▸ hb)).elim
  · exact (modPow_binNum (rule_at hr stepO_6 ▸ hb)).elim

theorem encVal_ne_BIN (v : Value) (w : Value) : encVal v ≠ .case "BIN" w := by
  cases v with
  | num n => cases n <;> simp [encVal, encNum, con]
  | _ => simp [encVal, con]

/-- **`BIN-ctx2` never reduces the right operand**: in the original, `(a + b) \ 2^N` reduces
to no value at all, although our evaluator gives `(a + b) % 2^N`. -/
theorem original_modPow_stuck {S : Value} (a b N : Nat) (v : Value) :
    ¬ MReduce envO S (modPow a b N).enc (encVal v) := by
  intro h
  have key := reduce_rec findRel_reduceO rfl rfl
    (fun S a c => (∃ l, a = con "BIN" [encBinOp .modOp, l, powEnc N]) →
      ∃ l, c = con "BIN" [encBinOp .modOp, l, powEnc N])
    (fun _ _ ha => ha)
    (fun _ _ _ _ hab hbc ⟨l, hl⟩ => hbc (stepO_modPow (hl ▸ hab)))
    h ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := key
  exact encVal_ne_BIN v _ hl

/-! ## Positive witnesses, built concretely -/

/-- A closed value at a closed global type: decided by computing the instance check. -/
theorem typedV_closed {env : Env} {x : IL.Id} {td : TypDef} {v : Value}
    (hd : env.findTyp? x = some td) (h : HasTypInsts env td.2 [] v) :
    TypedV env (.varT x []) v :=
  fun _ hρ => (hasTyp_varT_global_iff (localTyp_none hρ x)).2 ⟨td, [], hd, evalArgs_nil _ _, h⟩

/-- `typedV_closed` at `envO`, by computation. -/
macro "typedO" : term => `(typedV_closed rfl ⟨60, by with_unfolding_all rfl⟩)

/-- A step by rule `k` of the original `Step_exp`, at an explicit instance. -/
theorem mstepO_mk {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hk : (rulesOf envO "Step_exp")[k]? = some (.ruleD nm qs "%|-%~>%" e prems))
    (σ : List (IL.Id × Value)) {S a b : Value} (hq : QuantsOk envO (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp envO (VarEnv.empty.bindVals σ) e (.tuple [S, a, b]))
    (hp : ∀ pr ∈ prems, DPrem envO (otherwise envO)
      (otherwise envO "Step_exp" [] k (.tuple [S, a, b])) (VarEnv.empty.bindVals σ) pr) :
    MStep envO S a b :=
  Sim.DDerives.rule findRel_stepO hk rfl hq he hp

theorem reduceO_refl {S a : Value} (hS : TypedV envO (.varT "S" []) S)
    (ha : TypedV envO (.varT "exp" []) a) : MReduce envO S a a := by
  let σ : List (IL.Id × Value) := [("S", S), ("e", a)]
  have hρ := ValsOnly.bindVals valsOnly_empty σ
  refine Sim.DDerives.rule (i := 0) findRel_reduceO (by rw [reduceO_rules]; rfl) rfl
    (σ := σ) ?_ ?_ (fun _ h => by simp at h)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ha _ hρ) Sim.QuantsOk.nil)
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))

theorem reduceO_step {S a b c : Value} (hS : TypedV envO (.varT "S" []) S)
    (ha : TypedV envO (.varT "exp" []) a) (hb : TypedV envO (.varT "exp" []) b)
    (hc : TypedV envO (.varT "exp" []) c) (h₁ : MStep envO S a b) (h₂ : MReduce envO S b c) :
    MReduce envO S a c := by
  let σ : List (IL.Id × Value) := [("S", S), ("e", a), ("e''", c), ("e'", b)]
  have hρ := ValsOnly.bindVals valsOnly_empty σ
  refine Sim.DDerives.rule (i := 1) findRel_reduceO (by rw [reduceO_rules]; rfl) rfl
    (σ := σ) ?_ ?_ (Sim.prems_two ?_ ?_)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ha _ hρ)
      (Sim.QuantsOk.cons rfl (hc _ hρ) (Sim.QuantsOk.cons rfl (hb _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
  · exact .rulePr Equiv.evalArgs_nil
      (evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))) h₁
  · exact .rulePr Equiv.evalArgs_nil
      (evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))) h₂

/-- `BIN-NUM` in the original at concrete numerals. -/
theorem stepO_binNum {S : Value} (hS : TypedV envO (.varT "S" []) S) (op : BinOp) (m₁ m₂ : Num)
    {w : Value} (hn : TypedV envO (.varT "numbinop" []) (encBinOp op))
    (h₁ : TypedV envO (.varT "num" []) (encNum m₁)) (h₂ : TypedV envO (.varT "num" []) (encNum m₂))
    (he : EvalExp envO (VarEnv.empty.bindVals [("S", S), ("numbinop", encBinOp op),
      ("num_1", encNum m₁), ("num_2", encNum m₂)])
      (.subE (.callE "numbin" [.expA (.varE "numbinop"), .expA (.varE "num_1"),
        .expA (.varE "num_2")]) (.varT "num" []) (.varT "exp" [])) w) :
    MStep envO S (con "BIN" [encBinOp op, encNum m₁, encNum m₂]) w := by
  let σ : List (IL.Id × Value) :=
    [("S", S), ("numbinop", encBinOp op), ("num_1", encNum m₁), ("num_2", encNum m₂)]
  have hρ := ValsOnly.bindVals valsOnly_empty σ
  refine mstepO_mk stepO_6 σ ?_ ?_ (fun _ h => by simp at h)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (hn _ hρ)
      (Sim.QuantsOk.cons rfl (h₁ _ hρ) (Sim.QuantsOk.cons rfl (h₂ _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl)
      (evalExp_con (evalExps_three (evalExp_sub (evalExp_var rfl)) (evalExp_sub (evalExp_var rfl))
        (evalExp_sub (evalExp_var rfl)))) he)

/-- **MOD divides**: in the original, `6 \ 3` reduces to `2`. -/
theorem original_mod :
    MReduce envO emptyS (FExp.bin .modOp (.numT .natT) (.nat 6) (.nat 3)).enc
      (encVal (.num (.natN 2))) :=
  reduceO_step typedO typedO typedO typedO
    (stepO_binNum typedO .modOp (.natN 6) (.natN 3) typedO typedO typedO
      ⟨30, by with_unfolding_all rfl⟩)
    (reduceO_refl typedO typedO)

/-- `1 = 1 + 1`. -/
def oneEqTwo : FExp :=
  .cmp .eqOp .boolT (.nat 1) (.bin .addOp (.numT .natT) (.nat 1) (.nat 1))

/-- `1 + 1`, encoded. -/
abbrev onePlusOne : Value := (FExp.bin .addOp (.numT .natT) (.nat 1) (.nat 1)).enc

/-- The original `CMP-ctx2` steps `1 = 1 + 1` to `1 + 1 = 1 + 1`, using `1 + 1 ~> 2` only as a
premise. -/
theorem stepO_ctx2_bogus :
    MStep envO emptyS oneEqTwo.enc (con "CMP" [encCmpOp .eqOp, onePlusOne, onePlusOne]) := by
  have s₀ : MStep envO emptyS onePlusOne (encNum (.natN 2)) :=
    stepO_binNum typedO .addOp (.natN 1) (.natN 1) typedO typedO typedO
      ⟨30, by with_unfolding_all rfl⟩
  let σ : List (IL.Id × Value) := [("S", emptyS), ("op", encCmpOp .eqOp),
    ("e_1", encNum (.natN 1)), ("e_2", onePlusOne), ("e_1'", onePlusOne),
    ("e_2'", encNum (.natN 2))]
  have hρ := ValsOnly.bindVals valsOnly_empty σ
  refine mstepO_mk stepO_8 σ ?_ ⟨20, by with_unfolding_all rfl⟩ (Sim.prems_one ?_)
  · exact Sim.QuantsOk.cons rfl (typedO _ hρ) (Sim.QuantsOk.cons rfl (typedO _ hρ)
      (Sim.QuantsOk.cons rfl (typedO _ hρ) (Sim.QuantsOk.cons rfl (typedO _ hρ)
        (Sim.QuantsOk.cons rfl (typedO _ hρ) (Sim.QuantsOk.cons rfl (typedO _ hρ)
          Sim.QuantsOk.nil)))))
  · exact .rulePr Equiv.evalArgs_nil ⟨20, by with_unfolding_all rfl⟩ s₀

/-- The original `CMP-EQ-true` steps `1 + 1 = 1 + 1` to `true`, comparing the expressions. -/
theorem stepO_eq_exp :
    MStep envO emptyS (con "CMP" [encCmpOp .eqOp, onePlusOne, onePlusOne])
      (con "BOOL" [.bool true]) := by
  let σ : List (IL.Id × Value) := [("S", emptyS), ("e_1", onePlusOne), ("e_2", onePlusOne)]
  have hρ := ValsOnly.bindVals valsOnly_empty σ
  refine mstepO_mk stepO_9 σ ?_ ⟨20, by with_unfolding_all rfl⟩
    (Sim.prems_one (.ifPr ⟨20, by with_unfolding_all rfl⟩))
  exact Sim.QuantsOk.cons rfl (typedO _ hρ) (Sim.QuantsOk.cons rfl (typedO _ hρ)
    (Sim.QuantsOk.cons rfl (typedO _ hρ) Sim.QuantsOk.nil))

/-- **The `CMP-ctx2` typo with expression equality**: in the original, `1 = 1 + 1` reduces to
`true`. -/
theorem original_one_eq_two : MReduce envO emptyS oneEqTwo.enc (encVal (.bool true)) :=
  reduceO_step typedO typedO typedO typedO stepO_ctx2_bogus
    (reduceO_step typedO typedO typedO typedO stepO_eq_exp (reduceO_refl typedO typedO))

/-- Ours: `1 = 1 + 1` is `false`. -/
theorem strict_oneEqTwo : oneEqTwo.strict = some (.bool false) := by
  simp [oneEqTwo, FExp.strict, binValues, cmpValues, Num.bin, Res.ofOption, FExp.resVal]

/-- Ours: `6 \ 3 = 0`. -/
theorem strict_mod : (FExp.bin .modOp (.numT .natT) (.nat 6) (.nat 3)).strict =
    some (.num (.natN 0)) := by
  simp [FExp.strict, binValues, Num.bin, Res.ofOption, FExp.resVal]

end Silmaril.Wasm.SpecTec.Meta
