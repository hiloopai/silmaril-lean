module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Decode

/-!
# Family X, backward: SpecTec's exception steps are Core steps

For each `Step_read` rule of the family that has been done, a SpecTec step from the image of a
configuration is the image of a Core step. Each theorem has the type of `Backward.read i` for its
index `i` (`Typed` is not needed). The proofs invert the rule's conclusion
(`evalExp_concl_inv`, `handler_decode`), read the code back (`adminToV_case`), and, for
`-catch`/`-catch_ref`, invert the tag and fields premises through `Helpers` (`tagMatch_of_prem`,
`fields_of_prem`). `handler-vals` (rule 25 of `Step_pure`) reads its body back as values
through `Decoders.vals`. `throw_ref-handler-next` turns its `otherwise` premise into
`¬ CatchMatches` (`not_catchMatches_of_otherwise`): if the clause matched, the forward rule bodies
of rules 17–20 (`body_*`) would fire on the same configuration.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV evalExp_iterPat evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

section Helpers
variable {env : Env} {ρ : VarEnv}

/-- A rule that fires is the rule at that index. -/
theorem fires_body {x : IL.Id} {i : Nat} {r₀ : Rule} {v : Value}
    (hR : HasRuleAt env x "%~>%" i r₀) (hf : Fires env x i v) :
    RuleBody env (DDerives env (otherwise env)) (otherwise env x [] i v) [] [] "%~>%" r₀ v := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := hf
  rw [← rule_of_hasRuleAt hR hrel hr]
  exact hb

/-- `C` with no payload evaluates to `caseNilV C` only. -/
theorem evalExp_caseNil_inv {op : MixopS} {v : Value}
    (h : EvalExp env ρ (.caseE op (.tupE [])) v) : v = caseNilV op :=
  EvalExp.unique h (evalExp_caseNil op)

/-- A one-element list literal. -/
theorem evalExp_list1_inv' {e : Exp} {l : List Value}
    (h : EvalExp env ρ (.listE [e]) (.list l)) : ∃ v, l = [v] ∧ EvalExp env ρ e v := by
  obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 (evalExp_list_inv h)
  obtain rfl := evalExps_nil_iff.1 hws
  exact ⟨w, rfl, hw⟩

/-- A two-element list literal. -/
theorem evalExp_list2_inv {e₁ e₂ : Exp} {l : List Value}
    (h : EvalExp env ρ (.listE [e₁, e₂]) (.list l)) :
    ∃ v₁ v₂, l = [v₁, v₂] ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 (evalExp_list_inv h)
  obtain ⟨u, us, hu, hus, rfl⟩ := evalExps_cons_iff.1 hws
  obtain rfl := evalExps_nil_iff.1 hus
  exact ⟨w, u, rfl, hw, hu⟩

/-- `REF.EXN_ADDR a; THROW_REF`, inverted. -/
theorem evalExp_throwExn_inv {l : List Value}
    (h : EvalExp env ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])])
      (.list l)) :
    ∃ av, ρ.findVal? "a" = some av ∧ l = [.case "REF.EXN_ADDR" av, caseNilV "THROW_REF"] := by
  obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := evalExp_list2_inv h
  obtain ⟨av, hav, rfl⟩ := evalExp_caseE_iff.1 h₁
  exact ⟨av, evalExp_varE_iff.1 hav, by rw [evalExp_caseNil_inv h₂]⟩

/-- A thrown exception in a rule's instruction pattern: the code it matches is `throwing k`,
and the same pattern on the right-hand side is its image. -/
theorem throwExn_decode {body : List Admin} {w : Value}
    (h : EvalExp env ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])])
      (.list (adminsToV body)))
    (hw : EvalExp env ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])])
      w) :
    ∃ k, body = throwing k ∧ ρ.findVal? "a" = some (.num (.natN k)) ∧
      w = .list (adminsToV (throwing k)) := by
  obtain ⟨av, fa, hl⟩ := evalExp_throwExn_inv h
  obtain ⟨k, rfl, rfl⟩ := adminsToV_eq_throwing hl
  exact ⟨k, rfl, fa, EvalExp.unique hw (evalExp_throwExn fa)⟩

/-- A catch clause read back from its image. -/
theorem catch_decode {c : Catch} {op : MixopS} {w : Value} (h : Encode.toValue c = .case op w) :
    (op = "CATCH" → ∃ x l, c = .catch_ x l ∧ w = .tuple [Encode.toValue x, Encode.toValue l]) ∧
    (op = "CATCH_REF" → ∃ x l, c = .catchRef x l ∧
      w = .tuple [Encode.toValue x, Encode.toValue l]) ∧
    (op = "CATCH_ALL" → ∃ l, c = .catchAll l ∧ w = Encode.toValue l) ∧
    (op = "CATCH_ALL_REF" → ∃ l, c = .catchAllRef l ∧ w = Encode.toValue l) := by
  cases c <;> (obtain ⟨rfl, rfl⟩ := Value.case.inj h; simp [Equiv.catchView])

end Helpers

section Catches
variable {env : Env} {ρ : VarEnv}

/-- The head clause of a clause list matched by `[C e] ++ catch'*`. -/
theorem catch_head' {A e : Exp} {op : MixopS} {cs : List Catch}
    (h : EvalExp env ρ (.catE (.listE [.caseE op e]) A) (.list (cs.map Encode.toValue))) :
    ∃ c₀ cs₀ w, cs = c₀ :: cs₀ ∧ Encode.toValue c₀ = .case op w ∧ EvalExp env ρ e w := by
  cases cs with
  | nil =>
      obtain ⟨a, b, ha, -, hab⟩ := evalExp_cat_inv h
      have h1 := evalExp_list1_len ha
      have : 0 = a.length + b.length := by simpa using congrArg List.length hab
      omega
  | cons c₀ cs₀ =>
      obtain ⟨w, hw, he⟩ := catch_head h
      exact ⟨c₀, cs₀, w, rfl, hw, he⟩

end Catches

section Backward

variable {H : Type} {env : Env} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- The handler pattern `HANDLER_ne{ce} te` matched against the code of a configuration. -/
theorem handler_decode {ρ : VarEnv} {ne ce te : Exp} {code : List Admin}
    (h : EvalExp env ρ (.listE [.caseE "HANDLER_%{%}%" (.tupE [ne, ce, te])])
      (.list (adminsToV code))) :
    ∃ n cs body, code = [.handler n cs body] ∧ EvalExp env ρ ne (.num (.natN n)) ∧
      EvalExp env ρ ce (.list (cs.map Encode.toValue)) ∧
      EvalExp env ρ te (.list (adminsToV body)) := by
  obtain ⟨x, hx, hxe⟩ := evalExp_list1_inv' h
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨n, cs, body, rfl, rfl⟩ := (adminToV_case ha).2.2.2.2.2.1 rfl
  obtain ⟨h₁, h₂, h₃⟩ := evalExp_tup3_inv hu
  exact ⟨n, cs, body, rfl, h₁, h₂, h₃⟩

/-- `Step_read/throw_ref-null`, backward. -/
theorem bwd_read_throwRefNull (R : HasReadRules env) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 12 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := fires_body R.throwRefNull hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨v₁, v₂, hl, h₁, h₂⟩ := evalExp_list2_inv hce
  obtain ⟨a, b, rfl, ha, hb⟩ := adminsToV_eq_two hl
  rw [evalExp_caseNil_inv h₁] at ha
  rw [evalExp_caseNil_inv h₂] at hb
  rw [(adminToV_case ha).1 rfl, (adminToV_case hb).2.2.1 rfl]
  exact ⟨[.trap], EvalExp.unique hre (evalExp_list1 (evalExp_caseNil "TRAP")), .throwRefNull⟩

/-- `Step_read/throw_ref-label`, backward. -/
theorem bwd_read_throwRefLabel (R : HasReadRules env) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 14 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := fires_body R.throwRefLabel hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨x, hx, hxe⟩ := evalExp_list1_inv' hce
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨n, cont, body, rfl, rfl⟩ := (adminToV_case ha).2.2.2.2.2.2.1 rfl
  obtain ⟨-, -, hb⟩ := evalExp_tup3_inv hu
  obtain ⟨k, rfl, -, rfl⟩ := throwExn_decode hb hre
  exact ⟨_, rfl, .throwRefLabel⟩

/-- `Step_read/throw_ref-frame`, backward. -/
theorem bwd_read_throwRefFrame (R : HasReadRules env) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 15 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := fires_body R.throwRefFrame hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨x, hx, hxe⟩ := evalExp_list1_inv' hce
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_one hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨n, fr, body, rfl, rfl⟩ := (adminToV_case ha).2.2.2.2.2.2.2 rfl
  obtain ⟨-, -, hb⟩ := evalExp_tup3_inv hu
  obtain ⟨k, rfl, -, rfl⟩ := throwExn_decode hb hre
  exact ⟨_, rfl, .throwRefFrame⟩

/-- `Step_read/throw_ref-handler-empty`, backward. -/
theorem bwd_read_throwRefHandlerEmpty (R : HasReadRules env) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 16 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := fires_body R.throwRefHandlerEmpty hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨n, cs, body, rfl, -, hcs, hb⟩ := handler_decode hce
  obtain rfl : cs = [] := by
    have h0 := evalExps_nil_iff.1 (evalExp_list_inv hcs)
    simpa using h0
  obtain ⟨k, rfl, -, rfl⟩ := throwExn_decode hb hre
  exact ⟨_, rfl, .throwRefHandlerEmpty⟩

/-- `Step_read/throw_ref-handler-catch_all`, backward. -/
theorem bwd_read_throwRefHandlerCatchAll (R : HasReadRules env) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 19 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := fires_body R.throwRefHandlerCatchAll hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨n, cs, body, rfl, -, hcs, hb⟩ := handler_decode hce
  obtain ⟨c₀, cs₀, lw, rfl, hc₀, hlw⟩ := catch_head' hcs
  obtain ⟨l, rfl, rfl⟩ := (catch_decode hc₀).2.2.1 rfl
  obtain ⟨av, -, hl⟩ := evalExp_throwExn_inv hb
  obtain ⟨k, rfl, -⟩ := adminsToV_eq_throwing hl
  refine ⟨[.plain (.br l)], ?_, .throwRefHandlerCatchAll⟩
  exact EvalExp.unique hre (evalExp_list1 (evalExp_case hlw))

/-- `Step_read/throw_ref-handler-catch_all_ref`, backward. -/
theorem bwd_read_throwRefHandlerCatchAllRef (R : HasReadRules env) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 20 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := fires_body R.throwRefHandlerCatchAllRef hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨n, cs, body, rfl, -, hcs, hb⟩ := handler_decode hce
  obtain ⟨c₀, cs₀, lw, rfl, hc₀, hlw⟩ := catch_head' hcs
  obtain ⟨l, rfl, rfl⟩ := (catch_decode hc₀).2.2.2 rfl
  obtain ⟨av, fa, hl⟩ := evalExp_throwExn_inv hb
  obtain ⟨k, rfl, rfl⟩ := adminsToV_eq_throwing hl
  refine ⟨[.ref (.exn k), .plain (.br l)], ?_, .throwRefHandlerCatchAllRef⟩
  exact EvalExp.unique hre (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case hlw))

/-- What a typed `val*` quantifier evaluates to, as `valsPat` and as `iterPat`. -/
theorem vals_quant {ρ : VarEnv} {qs : List Param} (hq : QuantsOk env ρ qs)
    (hm : Param.expP "val*" valsT ∈ qs) :
    ∃ vs, EvalExp env ρ (Equiv.Execution.valsPat "val" "val*") (.list vs) ∧
      EvalExp env ρ (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")])) (.list vs) ∧
      HasTyp env ρ valsT (.list vs) := by
  obtain ⟨w₀, fv, ht⟩ := hq _ _ hm
  obtain ⟨vs, rfl, -⟩ := hasTyp_iterT_list_iff.1 ht
  exact ⟨vs, evalExp_valsPat (by decide) fv, evalExp_iterPat (by decide) fv, ht⟩

/-- The fields premise of `throw_ref-handler-catch(_ref)`: `val*` is the exception's fields. -/
theorem fields_of_prem (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat}
    {e : ExnInst} {vs : List Value} (he : s.exns[a]? = some e)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hd : ρ.findDef? "exninst" = none)
    (hvs : EvalExp env ρ (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")])) (.list vs))
    (h : EvalExp env ρ (.cmpE .eqOp .boolT
      (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
      (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")) (.bool true)) :
    vs = e.fields.map valV := by
  obtain ⟨t₁, t₂, ht₁, ht₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have heq : t₁ = t₂ := Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have h₁ : t₁ = .list vs := EvalExp.unique ht₁ hvs
  have h₂ : t₂ = .list (e.fields.map valV) :=
    EvalExp.unique ht₂ (evalExp_dotE_iff.2 ⟨_, evalExp_exninstAt Hp he fz fa hd, rfl⟩)
  rw [h₁, h₂] at heq
  exact Value.list.inj heq

/-- The left-hand side of `throw_ref-handler-catch`, read back. -/
theorem catchLhs_decode {ρ : VarEnv} {code : List Admin}
    (h : EvalExp env ρ (.listE [.caseE "HANDLER_%{%}%" (.tupE [.varE "n",
      .catE (.listE [.caseE "CATCH" (.tupE [.varE "x", .varE "l"])])
        (.iterE (.varE "catch'") (.mk .list [.mk "catch'" (.varE "catch'*")])),
      .listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]])])
      (.list (adminsToV code))) :
    ∃ n x l cs₀ k, code = [.handler n (.catch_ x l :: cs₀) (throwing k)] ∧
      ρ.findVal? "x" = some (Encode.toValue x) ∧ ρ.findVal? "l" = some (Encode.toValue l) ∧
      ρ.findVal? "a" = some (.num (.natN k)) := by
  obtain ⟨n, cs, body, rfl, -, hcs, hb⟩ := handler_decode h
  obtain ⟨c₀, cs₀, xw, rfl, hc₀, hxw⟩ := catch_head' hcs
  obtain ⟨x, l, rfl, rfl⟩ := (catch_decode hc₀).1 rfl
  obtain ⟨hx, hl⟩ := evalExp_tup2_inv hxw
  obtain ⟨av, fa, hbl⟩ := evalExp_throwExn_inv hb
  obtain ⟨k, rfl, rfl⟩ := adminsToV_eq_throwing hbl
  exact ⟨n, x, l, cs₀, k, rfl, evalExp_varE_iff.1 hx, evalExp_varE_iff.1 hl, fa⟩

/-- The left-hand side of `throw_ref-handler-catch_ref`, read back. -/
theorem catchRefLhs_decode {ρ : VarEnv} {code : List Admin}
    (h : EvalExp env ρ (.listE [.caseE "HANDLER_%{%}%" (.tupE [.varE "n",
      .catE (.listE [.caseE "CATCH_REF" (.tupE [.varE "x", .varE "l"])])
        (.iterE (.varE "catch'") (.mk .list [.mk "catch'" (.varE "catch'*")])),
      .listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]])])
      (.list (adminsToV code))) :
    ∃ n x l cs₀ k, code = [.handler n (.catchRef x l :: cs₀) (throwing k)] ∧
      ρ.findVal? "x" = some (Encode.toValue x) ∧ ρ.findVal? "l" = some (Encode.toValue l) ∧
      ρ.findVal? "a" = some (.num (.natN k)) := by
  obtain ⟨n, cs, body, rfl, -, hcs, hb⟩ := handler_decode h
  obtain ⟨c₀, cs₀, xw, rfl, hc₀, hxw⟩ := catch_head' hcs
  obtain ⟨x, l, rfl, rfl⟩ := (catch_decode hc₀).2.1 rfl
  obtain ⟨hx, hl⟩ := evalExp_tup2_inv hxw
  obtain ⟨av, fa, hbl⟩ := evalExp_throwExn_inv hb
  obtain ⟨k, rfl, rfl⟩ := adminsToV_eq_throwing hbl
  exact ⟨n, x, l, cs₀, k, rfl, evalExp_varE_iff.1 hx, evalExp_varE_iff.1 hl, fa⟩

/-- `Step_read/throw_ref-handler-catch`, backward. -/
theorem bwd_read_throwRefHandlerCatch (R : HasReadRules env) (Hp : HelpersInv env hn) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 17 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body R.throwRefHandlerCatch hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨n, x, l, cs₀, k, rfl, fx, fl, fa⟩ := catchLhs_decode hce
  obtain ⟨vs, hvs, hvs', -⟩ := vals_quant hq (by simp)
  have fz : _ = some (stateV hn s f) := evalExp_varE_iff.1 hz
  obtain ⟨e, ta, hek, hta, rfl⟩ : ∃ e ta, s.exns[k]? = some e ∧
      f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
    cases hp _ (List.mem_cons_self ..) with
    | ifPr h => exact tagMatch_of_prem Hp fz fa fx rfl rfl h
  have hfields : vs = e.fields.map valV := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
    | ifPr h => exact fields_of_prem Hp hek fz fa rfl hvs' h
  refine ⟨vals e.fields ++ [.plain (.br l)], ?_, .throwRefHandlerCatch hek hta⟩
  rw [adminsToV_append, adminsToV_vals, ← hfields]
  exact EvalExp.unique hre (evalExp_cat hvs (evalExp_list1 (evalExp_case (evalExp_var fl))))

/-- `Step_read/throw_ref-handler-catch_ref`, backward. -/
theorem bwd_read_throwRefHandlerCatchRef (R : HasReadRules env) (Hp : HelpersInv env hn) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 18 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body R.throwRefHandlerCatchRef hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hz, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨n, x, l, cs₀, k, rfl, fx, fl, fa⟩ := catchRefLhs_decode hce
  obtain ⟨vs, hvs, hvs', -⟩ := vals_quant hq (by simp)
  have fz : _ = some (stateV hn s f) := evalExp_varE_iff.1 hz
  obtain ⟨e, ta, hek, hta, rfl⟩ : ∃ e ta, s.exns[k]? = some e ∧
      f.module.tags[x.toNat]? = some ta ∧ e.tag = ta := by
    cases hp _ (List.mem_cons_self ..) with
    | ifPr h => exact tagMatch_of_prem Hp fz fa fx rfl rfl h
  have hfields : vs = e.fields.map valV := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
    | ifPr h => exact fields_of_prem Hp hek fz fa rfl hvs' h
  refine ⟨vals e.fields ++ [.ref (.exn k), .plain (.br l)], ?_, .throwRefHandlerCatchRef hek hta⟩
  rw [adminsToV_append, adminsToV_vals, ← hfields]
  exact EvalExp.unique hre
    (evalExp_cat hvs
      (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fl))))

end Backward


section Backward2

variable {H : Type} {env : Env} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- `Step_pure/handler-vals`, backward. -/
theorem bwd_pure_handlerVals (R : Equiv.Execution.HasStepRules env) (Dc : Decoders env hn) :
    ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), Typed env hn ⟨s, f, is⟩ →
      Fires env "Step_pure" 25 (.tuple [.list (adminsToV is), w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rintro s f is w - hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, -⟩ := fires_body R.handlerVals hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  obtain ⟨n, cs, body, rfl, -, -, hb⟩ := handler_decode hl
  obtain ⟨vs, hvs, -, ht⟩ := vals_quant hq (by simp)
  have hbody : adminsToV body = vs := Value.list.inj (EvalExp.unique hb hvs)
  obtain ⟨vs', rfl⟩ := Dc.vals _ ⟨rfl, rfl, rfl⟩ body (hbody ▸ ht)
  refine ⟨vals vs', ?_, .handlerVals⟩
  rw [hbody]
  exact EvalExp.unique hr hvs

/-- The clause list `catch catch'*` of `throw_ref-handler-next`, read back. -/
theorem catch_var_head {ρ : VarEnv} {A : Exp} {cs : List Catch}
    (h : EvalExp env ρ (.catE (.listE [.varE "catch"]) A) (.list (cs.map Encode.toValue))) :
    ∃ c₀ cs₀, cs = c₀ :: cs₀ ∧ ρ.findVal? "catch" = some (Encode.toValue c₀) ∧
      EvalExp env ρ A (.list (cs₀.map Encode.toValue)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := evalExp_cat_inv h
  obtain ⟨y, rfl, hy⟩ := evalExp_list1_inv' ha
  cases cs with
  | nil => simp at hab
  | cons c₀ cs₀ =>
      simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨c₀, cs₀, rfl, evalExp_varE_iff.1 hy, hb⟩

/-- An `otherwise` premise excludes every earlier rule on the same left-hand side. -/
theorem otherwiseAt_not_body {x : IL.Id} {op : MixopS} {i j : Nat} {r : Rule} {v w : Value}
    (h : otherwiseAt env x [] i v) (hj : j < i) (hR : HasRuleAt env x op j r)
    (hs : SameLhs v w) :
    ¬ RuleBody env (DDerives env noElse) (otherwiseAt env x [] j w) [] [] op r w := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := hR
  rw [otherwiseAt] at h
  exact h j hj [] op t rules r hrel hk w hs

/-- Under `otherwise`, `throw_ref-handler-next` fires only on a clause that does not match:
if the clause matched, one of rules 17–20 would fire on the same configuration. -/
theorem not_catchMatches_of_otherwise (R : HasReadRules env) (T : TypingFacts env hn)
    (X : Typing env) (Hp : HelpersInv env hn) (Dc : Decoders env hn) {s : Store H} {f : Frame}
    {n k : Nat} {c₀ : Catch} {cs₀ : List Catch} {w : Value}
    (hc : Typed env hn ⟨s, f, [.handler n (c₀ :: cs₀) (throwing k)]⟩)
    (h : otherwise env "Step_read" [] 21
      (.tuple [configV hn ⟨s, f, [.handler n (c₀ :: cs₀) (throwing k)]⟩, w])) :
    ¬ CatchMatches s f k c₀ := by
  have hz : TypedV env stateT (stateV hn s f) := ((T.config _).1 hc).1
  have hh := T.handler n (c₀ :: cs₀) (throwing k) ((T.config _).1 hc).2
  have hcs₀ : TypedV env catchesT (.list (cs₀.map Encode.toValue)) := (X.catch_ c₀ cs₀ hh.2.1).2
  intro hm
  cases c₀ with
  | catch_ x l =>
      obtain ⟨e, ta, he, hta, hte⟩ := hm
      exact otherwiseAt_not_body h (by decide) R.throwRefHandlerCatch ⟨_, _, _, rfl, rfl⟩
        (body_throwRefHandlerCatch Hp he (hte ▸ hta) hz hh.1 (X.idx x) (X.labelidx l) hcs₀
          (X.addr k) (Dc.exnFields s f hz k e he))
  | catchRef x l =>
      obtain ⟨e, ta, he, hta, hte⟩ := hm
      exact otherwiseAt_not_body h (by decide) R.throwRefHandlerCatchRef ⟨_, _, _, rfl, rfl⟩
        (body_throwRefHandlerCatchRef Hp he (hte ▸ hta) hz hh.1 (X.idx x) (X.labelidx l) hcs₀
          (X.addr k) (Dc.exnFields s f hz k e he))
  | catchAll l =>
      exact otherwiseAt_not_body h (by decide) R.throwRefHandlerCatchAll ⟨_, _, _, rfl, rfl⟩
        (body_throwRefHandlerCatchAll hz hh.1 (X.labelidx l) hcs₀ (X.addr k))
  | catchAllRef l =>
      exact otherwiseAt_not_body h (by decide) R.throwRefHandlerCatchAllRef ⟨_, _, _, rfl, rfl⟩
        (body_throwRefHandlerCatchAllRef hz hh.1 (X.labelidx l) hcs₀ (X.addr k))

/-- `Step_read/throw_ref-handler-next`, backward. -/
theorem bwd_read_throwRefHandlerNext (R : HasReadRules env) (T : TypingFacts env hn)
    (X : Typing env) (Hp : HelpersInv env hn) (Dc : Decoders env hn) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 21 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w hc hf
  obtain ⟨-, ρ₀, σ, -, -, he, hp⟩ := fires_body R.throwRefHandlerNext hf
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨n, cs, body, rfl, hnv, hcs, hb⟩ := handler_decode hce
  obtain ⟨c₀, cs₀, rfl, -, hrest⟩ := catch_var_head hcs
  obtain ⟨av, fa, hbl⟩ := evalExp_throwExn_inv hb
  obtain ⟨k, rfl, rfl⟩ := adminsToV_eq_throwing hbl
  have hnm : ¬ CatchMatches s f k c₀ := by
    cases hp _ (List.mem_singleton_self _) with
    | elsePr h => exact not_catchMatches_of_otherwise R T X Hp Dc hc h
  refine ⟨[.handler n cs₀ (throwing k)], ?_, .throwRefHandlerNext hnm⟩
  exact EvalExp.unique hre (evalExp_list1 (evalExp_case (evalExp_tup3 hnv hrest
    (evalExp_throwExn fa))))

end Backward2

section Backward3

variable {H : Type} {env : Env} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- An image that splits splits its preimage. -/
theorem adminsToV_eq_append {l : List Admin} {A B : List Value} (h : adminsToV l = A ++ B) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ adminsToV l₁ = A ∧ adminsToV l₂ = B := by
  rw [adminsToV_eq_map] at h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  exact ⟨l₁, l₂, rfl, by rw [adminsToV_eq_map, h₁], by rw [adminsToV_eq_map, h₂]⟩

/-- The left-hand side of `throw_ref-instrs`, read back. -/
theorem instrsLhs_decode {ρ : VarEnv} {code : List Admin}
    (h : EvalExp env ρ (.catE (Equiv.Execution.valsPat "val" "val*")
      (.catE (.listE [.caseE "REF.EXN_ADDR" (.varE "a")])
        (.catE (.listE [.caseE "THROW_REF" (.tupE [])])
          (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")])))))
      (.list (adminsToV code))) :
    ∃ l₁ k l₃, code = l₁ ++ throwing k ++ l₃ ∧ ρ.findVal? "a" = some (.num (.natN k)) ∧
      EvalExp env ρ (Equiv.Execution.valsPat "val" "val*") (.list (adminsToV l₁)) ∧
      EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
        (.list (adminsToV l₃)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := evalExp_cat_inv h
  obtain ⟨c, d, hc, hd, hcd⟩ := evalExp_cat_inv hb
  obtain ⟨g, r, hg, hr, hgr⟩ := evalExp_cat_inv hd
  obtain ⟨x, rfl, hx⟩ := evalExp_list1_inv' hc
  obtain ⟨y, rfl, hy⟩ := evalExp_list1_inv' hg
  obtain ⟨av, hav, rfl⟩ := evalExp_caseE_iff.1 hx
  obtain rfl := evalExp_caseNil_inv hy
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := adminsToV_eq_append (hab.trans (by rw [hcd, hgr]))
  obtain ⟨m, l₃, rfl, hm, h₃⟩ := adminsToV_eq_append (l := l₂) (A := [.case "REF.EXN_ADDR" av,
    caseNilV "THROW_REF"]) (B := r) (by rw [h₂]; rfl)
  obtain ⟨k, rfl, rfl⟩ := adminsToV_eq_throwing hm
  refine ⟨l₁, k, l₃, by simp, evalExp_varE_iff.1 hav, h₁ ▸ ha, h₃ ▸ hr⟩

/-- `Step_read/throw_ref-instrs`, backward. -/
theorem bwd_read_throwRefInstrs (R : HasReadRules env) (Dc : Decoders env hn) :
    ∀ (c : Config H) (w : Value), Typed env hn c →
      Fires env "Step_read" 13 (.tuple [configV hn c, w]) →
      ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := fires_body R.throwRefInstrs hf
  obtain rfl : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨-, hce, hre⟩ := evalExp_concl_inv he
  obtain ⟨l₁, k, l₃, rfl, fa, hv, hr⟩ := instrsLhs_decode hce
  obtain ⟨vs, hvs, hvs', ht⟩ := vals_quant hq (by simp)
  have e₁ : adminsToV l₁ = vs := Value.list.inj (EvalExp.unique hv hvs)
  obtain ⟨vs', rfl⟩ := Dc.vals _ ⟨rfl, rfl, rfl⟩ l₁ (e₁ ▸ ht)
  have hne : adminsToV (vals vs') ≠ [] ∨ adminsToV l₃ ≠ [] := by
    cases hp _ (List.mem_singleton_self _) with
    | ifPr h =>
        have hor := evalExp_or (t := .boolT) (evalExp_ne_nil (t := .boolT) (e₁ ▸ hvs'))
          (evalExp_ne_nil (t := .boolT) hr)
        exact of_decide_eq_true (Value.bool.inj (EvalExp.unique hor h))
  have hne' : vs' ≠ [] ∨ l₃ ≠ [] := by
    rcases hne with h | h
    · exact .inl fun h' => h (by simp [h', vals, adminsToV])
    · exact .inr fun h' => h (by simp [h', adminsToV])
  refine ⟨throwing k, EvalExp.unique hre (evalExp_throwExn fa), ?_⟩
  simpa only [List.append_assoc] using
    (Step.throwRefInstrs (P := P) (host := host) (s := s) (f := f) (a := k) hne')

end Backward3
end Silmaril.Wasm.SpecTec.Sim.Exn
