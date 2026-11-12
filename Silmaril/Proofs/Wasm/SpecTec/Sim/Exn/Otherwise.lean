module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Invert

/-!
# Family X: the `otherwise` premise of `throw_ref-handler-next`

`throw_ref-handler-next` (rule 21 of `Step_read`) carries an `otherwise` premise. Under the
reading `Sim.otherwise` it may fire only if none of rules 0–20 fires on the same left-hand side.
`otherwiseAt_handlerNext` proves this for a handler whose first clause does not match the
exception (`¬ CatchMatches`), which is Core's condition:

* rules 0–8 and 10–15 have instruction patterns that cannot evaluate to a single `HANDLER`
  (`shape_*`);
* `return_call_ref-handler` (9) needs a `RETURN_CALL_REF` in the handler's body;
* `throw_ref-handler-empty` (16) needs an empty clause list;
* `-catch_all` and `-catch_all_ref` (19, 20) would make the clause match;
* `-catch` and `-catch_ref` (17, 18) would, through their tag premise, give `CatchMatches`
  (`tagMatch_of_prem`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV evalExp_iterPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
section Next
variable {H : Type} {env : Env} {hn : H → String}
open Silmaril.SpecTec.Equiv.ExecRead

/-- The image of `HANDLER_n{catch*} (REF.EXN_ADDR a) THROW_REF`. -/
abbrev handlerThrowV (n : Nat) (cs : List Catch) (a : Nat) : Value :=
  .case "HANDLER_%{%}%" (.tuple [.num (.natN n), .list (cs.map Encode.toValue),
    .list [.case "REF.EXN_ADDR" (.num (.natN a)), caseNilV "THROW_REF"]])

theorem rule_of_hasRuleAt {x : IL.Id} {op' op : MixopS} {j : Nat} {r₀ r : Rule}
    {ps : List Param} {t : Typ} {rules : List Rule} (hR : HasRuleAt env x op' j r₀)
    (hrel : env.findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r) : r = r₀ := by
  obtain ⟨ps', t', rules', hrel', -, hk⟩ := hR
  rw [hrel] at hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
  obtain ⟨-, -, -, rfl⟩ := hrel'
  rw [hr] at hk
  exact Option.some.inj hk

/-- The head of `[C e] ++ A`. -/
theorem catch_head {A e : Exp} {op : MixopS} {x : Value} {l : List Value} {ρ : VarEnv}
    (h : EvalExp env ρ (.catE (.listE [.caseE op e]) A) (.list (x :: l))) :
    ∃ w, x = .case op w ∧ EvalExp env ρ e w := by
  obtain ⟨a, b, ha, -, hab⟩ := evalExp_cat_inv h
  obtain ⟨y, rfl⟩ : ∃ y, a = [y] := List.length_eq_one_iff.1 (evalExp_list1_len ha)
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 (evalExp_list1_inv ha)
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hab
  exact ⟨w, hab.1, hw⟩

/-- A clause encoded with a `CATCH_ALL` or `CATCH_ALL_REF` head catches everything. -/
theorem catchMatches_of_all {s : Store H} {f : Frame} {a : Nat} {c : Catch} {op : MixopS}
    {w : Value} (h : Encode.toValue c = .case op w)
    (hop : op = "CATCH_ALL" ∨ op = "CATCH_ALL_REF") :
    CatchMatches s f a c := by
  cases c with
  | catch_ x l =>
      have : "CATCH" = op := (Value.case.inj h).1
      rcases hop with rfl | rfl <;> simp at this
  | catchRef x l =>
      have : "CATCH_REF" = op := (Value.case.inj h).1
      rcases hop with rfl | rfl <;> simp at this
  | catchAll l => trivial
  | catchAllRef l => trivial

/-- A clause encoded with a `CATCH` or `CATCH_REF` head carries its tag index. -/
theorem catch_of_tag {c : Catch} {op : MixopS} {w : Value}
    (h : Encode.toValue c = .case op w) (hop : op = "CATCH" ∨ op = "CATCH_REF") :
    ∃ (x : TagIdx) (l : LabelIdx), w = .tuple [Encode.toValue x, Encode.toValue l] ∧
      ∀ (s : Store H) f a, (∃ e ta, s.exns[a]? = some e ∧ f.module.tags[x.toNat]? = some ta ∧
        e.tag = ta) → CatchMatches s f a c := by
  cases c with
  | catch_ x l => exact ⟨x, l, (Value.case.inj h).2.symm, fun _ _ _ hm => hm⟩
  | catchRef x l => exact ⟨x, l, (Value.case.inj h).2.symm, fun _ _ _ hm => hm⟩
  | catchAll l =>
      have : "CATCH_ALL" = op := (Value.case.inj h).1
      rcases hop with rfl | rfl <;> simp at this
  | catchAllRef l =>
      have : "CATCH_ALL_REF" = op := (Value.case.inj h).1
      rcases hop with rfl | rfl <;> simp at this

/-- The tag premise of `throw_ref-handler-catch(_ref)`, inverted at an encoded state. -/
theorem tagMatch_of_prem (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Nat} {x : TagIdx}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd₁ : ρ.findDef? "exninst" = none) (hd₂ : ρ.findDef? "tagaddr" = none)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT
      (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "TAG")
      (.idxE (.callE "tagaddr" [.expA (.varE "z")]) (.projE (.uncaseE (.varE "x") "%") 0)))
      (.bool true)) :
    ∃ e ta, s.exns[a]? = some e ∧ f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
  have hargs : EvalArgs env ρ [.expA (.varE "z")] [.val (stateV hn s f)] :=
    Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil
  obtain ⟨t₁, t₂, ht₁, ht₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have heq : t₁ = t₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  obtain ⟨ei, hei, htag⟩ := evalExp_dotE_iff.1 ht₁
  obtain ⟨eis, j, heis, hj, hidxe⟩ := evalExp_idxE_iff.1 hei
  have hjv : ρ.findVal? "a" = some (.num (.natN j)) := evalExp_varE_iff.1 hj
  have hja : j = a := by
    rw [fa] at hjv
    simpa using hjv.symm
  have heis' : eis = .list (s.exns.map exnInstV) :=
    Equiv.ExecNumeric.Applies.unique
      ((Equiv.ExecNumeric.applies_iff_callDef hd₁ hargs).2 (evalExp_callE_iff.1 heis))
      (Hp.exninst s f)
  obtain ⟨tas, i, htas, hi, hidxt⟩ := evalExp_idxE_iff.1 ht₂
  have hix : i = x.toNat := by
    obtain ⟨vs, hvs, h0⟩ := (Equiv.ExecReadControl.evalExp_idxProj_iff fx).1 hi
    have hvs' : vs = [.num (.natN x.toNat)] := (Value.tuple.inj (Value.case.inj hvs).2).symm
    subst hvs'
    simpa using h0.symm
  have htas' : tas = .list (f.module.tags.map fun a => .num (.natN a)) :=
    Equiv.ExecNumeric.Applies.unique
      ((Equiv.ExecNumeric.applies_iff_callDef hd₂ hargs).2 (evalExp_callE_iff.1 htas))
      (Hp.tagaddr s f)
  subst heis' htas' hja hix heq
  simp only [Value.idx?, List.getElem?_map, Option.map_eq_some_iff] at hidxe hidxt
  obtain ⟨e, he, rfl⟩ := hidxe
  obtain ⟨ta, hta, hta'⟩ := hidxt
  refine ⟨e, ta, he, hta, ?_⟩
  have hf : (exnInstV e).field? "TAG" = some (.num (.natN e.tag)) := rfl
  rw [hf, ← hta'] at htag
  simpa using htag

/-- `throw_ref-handler-catch` does not fire on a clause that does not match. -/
theorem not_ruleBody_catch (Hp : HelpersInv env hn) {D : Interp} {els : Prop} {op : MixopS}
    {s : Store H} {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch} {c' : Value}
    (hnm : ¬ CatchMatches s f a c) :
    ¬ RuleBody env D els [] [] op throwRefHandlerCatchRule
      (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, hps, -, he, hp⟩
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, hthrow⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hcw, hw⟩ := catch_head hcs
  obtain ⟨x, l, rfl, hcm⟩ := catch_of_tag (H := H) hcw (.inl rfl)
  obtain ⟨hx, -⟩ := evalExp_tup2_inv hw
  obtain ⟨ha, -⟩ := evalExps_two_inv (evalExp_list_inv hthrow)
  obtain ⟨-, ha'⟩ := evalExp_case_inv ha
  cases hp _ (List.mem_cons_self ..) with
  | ifPr h =>
      exact hnm (hcm s f a (tagMatch_of_prem Hp (evalExp_varE_iff.1 hz) (evalExp_varE_iff.1 ha')
        (evalExp_varE_iff.1 hx) rfl rfl h))

/-- `throw_ref-handler-catch_ref` does not fire on a clause that does not match. -/
theorem not_ruleBody_catchRef (Hp : HelpersInv env hn) {D : Interp} {els : Prop} {op : MixopS}
    {s : Store H} {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch} {c' : Value}
    (hnm : ¬ CatchMatches s f a c) :
    ¬ RuleBody env D els [] [] op throwRefHandlerCatchRefRule
      (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, hps, -, he, hp⟩
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, hthrow⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hcw, hw⟩ := catch_head hcs
  obtain ⟨x, l, rfl, hcm⟩ := catch_of_tag (H := H) hcw (.inr rfl)
  obtain ⟨hx, -⟩ := evalExp_tup2_inv hw
  obtain ⟨ha, -⟩ := evalExps_two_inv (evalExp_list_inv hthrow)
  obtain ⟨-, ha'⟩ := evalExp_case_inv ha
  cases hp _ (List.mem_cons_self ..) with
  | ifPr h =>
      exact hnm (hcm s f a (tagMatch_of_prem Hp (evalExp_varE_iff.1 hz) (evalExp_varE_iff.1 ha')
        (evalExp_varE_iff.1 hx) rfl rfl h))

/-- `throw_ref-handler-catch_all(_ref)` do not fire on a clause that does not match (no clause
of either kind fails to match). -/
theorem not_ruleBody_catchAll {D : Interp} {els : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {op' cop : MixopS} {ze ne ae re ke rhs : Exp} {prems : List Prem}
    {s : Store H} {f : Frame} {z : Value} {n a : Nat} {c : Catch} {cs : List Catch} {c' : Value}
    (hop : cop = "CATCH_ALL" ∨ cop = "CATCH_ALL_REF") (hnm : ¬ CatchMatches s f a c) :
    ¬ RuleBody env D els [] [] op
      (.ruleD nm qs op' (.tupE [.caseE "%;%" (.tupE [ze, .listE [.caseE "HANDLER_%{%}%"
        (.tupE [ne, .catE (.listE [.caseE cop ke]) ae, re])]]), rhs]) prems)
      (.tuple [cfgV z [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  obtain ⟨-, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, -⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hcw, -⟩ := catch_head hcs
  exact hnm (catchMatches_of_all hcw hop)

/-- `throw_ref-handler-empty` does not fire on a non-empty handler. -/
theorem not_ruleBody_empty {D : Interp} {els : Prop} {op : MixopS} {z : Value} {n a : Nat}
    {c : Catch} {cs : List Catch} {c' : Value} :
    ¬ RuleBody env D els [] [] op throwRefHandlerEmptyRule
      (.tuple [cfgV z [handlerThrowV n (c :: cs) a], c']) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  obtain ⟨-, hce, -⟩ := evalExp_concl_inv he
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv hce)
  obtain ⟨-, hcs, -⟩ := evalExp_tup3_inv h3
  have := evalExps_nil_iff.1 (evalExp_list_inv hcs)
  simp at this

/-- `return_call_ref-handler` does not fire on a handler whose body is a thrown exception. -/
theorem not_ruleBody_returnCallRefHandler {D : Interp} {els : Prop} {op : MixopS} {z : Value}
    {n a : Nat} {cs : List Catch} {c' : Value} :
    ¬ RuleBody env D els [] [] op returnCallRefHandlerRule
      (.tuple [cfgV z [handlerThrowV n cs a], c']) := by
  refine not_ruleBody_of_code fun ρ h => ?_
  obtain ⟨-, h3⟩ := evalExp_case_inv (evalExp_list1_inv h)
  obtain ⟨-, -, hb⟩ := evalExp_tup3_inv h3
  obtain ⟨w, hw⟩ := shape_memCase hb
  simp [caseNilV] at hw

/-- **The `otherwise` premise of `throw_ref-handler-next`.** No earlier `Step_read` rule fires on
a handler whose first clause does not match the exception. -/
theorem otherwiseAt_handlerNext (R : HasReadRules env) (Hp : HelpersInv env hn) {s : Store H}
    {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch} {b : Value}
    (hnm : ¬ CatchMatches s f a c) :
    otherwiseAt env "Step_read" [] 21
      (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], b]) := by
  rw [otherwiseAt]
  intro j hj ps op t rules r hrel hr w hsame
  obtain ⟨u, b₁, c', hv, rfl⟩ := hsame
  obtain ⟨rfl, -⟩ : cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a] = u ∧ b = b₁ := by
    simpa using hv
  obtain rfl : ps = [] := by
    obtain ⟨ps', t', rules', hrel', hps', -⟩ := R.block
    rw [hrel] at hrel'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    rw [hrel'.1, hps']
  have code : ∀ {nm qs op' ze ce re prems},
      (∀ ρ : VarEnv, ¬ EvalExp env ρ ce (.list [handlerThrowV n (c :: cs) a])) →
      ¬ RuleBody env (DDerives env noElse) (otherwiseAt env "Step_read" [] j
        (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c'])) [] [] op
        (.ruleD nm qs op' (.tupE [.caseE "%;%" (.tupE [ze, ce]), re]) prems)
        (.tuple [cfgV (stateV hn s f) [handlerThrowV n (c :: cs) a], c']) := by
    intro nm qs op' ze ce re prems hce
    exact not_ruleBody_of_code hce
  match j, hj, hr with
  | 0, _, hr =>
    rw [rule_of_hasRuleAt R.block hrel hr]
    exact code fun _ h => absurd (shape_catCase h) (by decide)
  | 1, _, hr =>
    rw [rule_of_hasRuleAt R.loop hrel hr]
    exact code fun _ h => absurd (shape_catCase h) (by decide)
  | 2, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastSucceed hrel hr]
    exact code fun _ h => shape_list2 h
  | 3, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastFail hrel hr]
    exact code fun _ h => shape_list2 h
  | 4, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastFailSucceed hrel hr]
    exact code fun _ h => shape_list2 h
  | 5, _, hr =>
    rw [rule_of_hasRuleAt R.brOnCastFailFail hrel hr]
    exact code fun _ h => shape_list2 h
  | 6, _, hr =>
    rw [rule_of_hasRuleAt R.call hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 7, _, hr =>
    rw [rule_of_hasRuleAt R.returnCall hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 8, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefLabel hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 9, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefHandler hrel hr]
    exact not_ruleBody_returnCallRefHandler
  | 10, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefFrameNull hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 11, _, hr =>
    rw [rule_of_hasRuleAt R.returnCallRefFrameAddr hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 12, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefNull hrel hr]
    exact code fun _ h => shape_list2 h
  | 13, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefInstrs hrel hr]
    exact code fun _ h => shape_cat2 h
  | 14, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefLabel hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 15, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefFrame hrel hr]
    exact code fun _ h => absurd (shape_list1Case h) (by decide)
  | 16, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerEmpty hrel hr]
    exact not_ruleBody_empty
  | 17, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatch hrel hr]
    exact not_ruleBody_catch Hp hnm
  | 18, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatchRef hrel hr]
    exact not_ruleBody_catchRef Hp hnm
  | 19, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatchAll hrel hr]
    exact not_ruleBody_catchAll (.inl rfl) hnm
  | 20, _, hr =>
    rw [rule_of_hasRuleAt R.throwRefHandlerCatchAllRef hrel hr]
    exact not_ruleBody_catchAll (.inr rfl) hnm
  | k + 21, h, _ => omega

/-- `Step_read/throw_ref-handler-next`: a clause that does not match is dropped. -/
theorem sread_throwRefHandlerNext (R : HasReadRules env) (Hp : HelpersInv env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 21 throwRefHandlerNextRule)
    {s : Store H} {f : Frame} {n a : Nat} {c : Catch} {cs : List Catch}
    (hnm : ¬ CatchMatches s f a c) (hz : TypedV env stateT (stateV hn s f))
    (hn₀ : TypedV env nT (.num (.natN n))) (hc : TypedV env catchT (Encode.toValue c))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV (stateV hn s f) (adminsToV [.handler n (c :: cs) (throwing a)]))
      (adminsToV [.handler n cs (throwing a)]) := by
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN n)),
    ("catch", Encode.toValue c), ("catch'*", .list (cs.map Encode.toValue)),
    ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fc : ρ.findVal? "catch" = some (Encode.toValue c) := rfl
  have fcs : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have ecs : EvalExp env ρ (.iterE (.varE "catch'") (.mk .list [.mk "catch'" (.varE "catch'*")]))
      (.list (cs.map Encode.toValue)) := evalExp_iterPat (by decide) fcs
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn₀ ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fcs (hcs ρ hρ) (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_var fc)) ecs) (evalExp_throwExn fa))))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ecs (evalExp_throwExn fa)))))
    (prems_one (.elsePr (otherwiseAt_handlerNext R Hp hnm)))

end Next

end Silmaril.Wasm.SpecTec.Sim.Exn
