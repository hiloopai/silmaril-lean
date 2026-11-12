module

public import Silmaril.Wasm.SpecTec.Sim.Exn.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Family X, forward: Core's exception steps are SpecTec steps

Each Core constructor of the exception family (`throw`, `throwRef*`, `tryTable`, `handlerVals`)
is simulated by the SpecTec rule it transcribes, read declaratively. The `Step_read` rules are
lifted by `Step/read`, `handler-vals` by `Step/pure`, and `throw` is rule 10 of `Step` itself.
The per-rule lemmas are stated for an arbitrary environment containing the rule (`HasRuleAt`);
the `fwd_*` theorems instantiate them at `simEnv B`, with the types of the `Forward` fields.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat evalExp_valsPat caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation

/-! ## Provenance in `simEnv B` -/

/-- The 103 `Step_read` rules (`Equiv.ExecRead`), in `simEnv B`. -/
theorem hasReadRules_simEnv (B : Builtins) : HasReadRules (simEnv B) := by
  have h := hasReadRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- The `Step_pure` rules of `Equiv.Execution`, in `simEnv B`. -/
theorem hasPureRules_simEnv (B : Builtins) : Equiv.Execution.HasStepRules (simEnv B) := by
  have h := Equiv.Execution.hasStepRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-! ## Evaluation helpers -/

/-- `C` with no payload. -/
theorem evalExp_caseNil {env : Env} {ρ : VarEnv} (op : MixopS) :
    EvalExp env ρ (.caseE op (.tupE [])) (caseNilV op) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- The empty list. -/
theorem evalExp_nil {env : Env} {ρ : VarEnv} : EvalExp env ρ (.listE []) (.list []) :=
  evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩

/-- A two-element list. -/
theorem evalExp_list2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.listE [e₁, e₂]) (.list [v₁, v₂]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil), rfl⟩

/-- `REF.EXN_ADDR a; THROW_REF`, with `a` bound. -/
theorem evalExp_throwExn {env : Env} {ρ : VarEnv} {a : Nat}
    (ha : ρ.findVal? "a" = some (.num (.natN a))) :
    EvalExp env ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])])
      (.list (adminsToV (throwing a))) :=
  evalExp_list2 (evalExp_case (evalExp_var ha)) (evalExp_caseNil "THROW_REF")

/-- No premises. -/
theorem prems_nil {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} :
    ∀ p ∈ ([] : List Prem), DPrem env O els ρ p :=
  fun _ h => nomatch h

/-- A rule body, from an explicit assignment. -/
theorem ruleBody_of {env : Env} {D : Interp} {els : Prop} {nm : IL.Id} {qs : List Param}
    {op : MixopS} {e : Exp} {prems : List Prem} {v : Value} {σ : List (IL.Id × Value)}
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW env D els (VarEnv.empty.bindVals σ) pr) :
    RuleBody env D els [] [] op (.ruleD nm qs op e prems) v :=
  ⟨rfl, VarEnv.empty, σ, rfl, hq, he, hp⟩

/-- A rule body at a rule the environment contains is a derivation. -/
theorem dderives_of_body {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    {v : Value} (h : HasRuleAt env x op k r)
    (hb : RuleBody env (DDerives env O) (O x [] k v) [] [] op r v) : DDerives env O x op [] v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  exact dderives_iff.2 ⟨_, _, _, _, _, hrel, hk, hb⟩

/-- One round per element, each binding `x` to that element, evaluates a body that reads `x`
back. -/
theorem evalRounds_var {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {d : Nat}
    (hb : ∀ (σ : VarEnv) (w : Value), σ.findVal? x = some w →
      evalExp (d + 1) env σ b = .ok w)
    (hx : x ≠ "_") (vs : List Value) :
    (vs.map fun w => [(x, w)]).mapM (fun r => evalExp (d + 1) env (ρ.bindVals r) b) = .ok vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, List.mapM_cons, Res.bind_eq_ok]
      refine ⟨v, ?_, vs, ih, rfl⟩
      exact hb _ v (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx])

/-- `x^n` over a single domain `y`, with the counter `m` bound to the domain's length. -/
theorem evalExp_iterN_var {env : Env} {ρ : VarEnv} {b : Exp} {x y m : IL.Id} {d : Nat}
    (hb : ∀ (σ : VarEnv) (w : Value), σ.findVal? x = some w →
      evalExp (d + 1) env σ b = .ok w)
    (hx : x ≠ "_") {vs : List Value} (h : ρ.findVal? y = some (.list vs))
    (hm : ρ.findVal? m = some (.num (.natN vs.length))) :
    EvalExp env ρ (.iterE b (.mk (.listN (.varE m) none) [.mk x (.varE y)])) (.list vs) := by
  have hdoms : evalDoms (d + 3) env ρ [.mk x (.varE y)] = .ok [(x, Value.list vs)] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  have hmv : evalExp (d + 3) env ρ (.varE m) = .ok (.num (.natN vs.length)) := by
    simp [evalExp, hm, Res.ofOption]
  have hrounds : evalRounds (d + 2) env ρ b (iterRows [(x, vs)] none vs.length) = .ok vs := by
    rw [Equiv.Execution.iterRows_singleton, evalRounds]
    exact evalRounds_var hb hx vs
  have hlist :
      evalIterList (d + 3) env ρ b [(x, Value.list vs)] none vs.length = .ok (.list vs) := by
    rw [evalIterList]
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
      List.mapM_nil]
    exact ⟨[(x, vs)], by simp [Value.asList?], by simp, vs, hrounds, rfl⟩
  refine evalExp_iterE_iff.mpr ⟨d + 4, ?_⟩
  rw [evalIterE, hdoms, hmv]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asNat?]
  exact ⟨[(x, Value.list vs)], rfl, _, rfl, vs.length, rfl, hlist⟩

/-- `val^m` (`Equiv.Execution.valsNPat`), with `m` bound to the length of `val*`. -/
theorem evalExp_valsNPat {env : Env} {ρ : VarEnv} {x y m : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs))
    (hm : ρ.findVal? m = some (.num (.natN vs.length))) :
    EvalExp env ρ (Equiv.Execution.valsNPat x y m) (.list vs) :=
  evalExp_iterN_var (d := 1) (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h hm

/-- `x^m` with a plain variable body. -/
theorem evalExp_varN {env : Env} {ρ : VarEnv} {x y m : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs))
    (hm : ρ.findVal? m = some (.num (.natN vs.length))) :
    EvalExp env ρ (.iterE (.varE x) (.mk (.listN (.varE m) none) [.mk x (.varE y)])) (.list vs) :=
  evalExp_iterN_var (d := 0) (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h hm

/-- A two-field record. -/
theorem evalExpFields_two {env : Env} {ρ : VarEnv} {a₁ a₂ : AtomS} {e₁ e₂ : Exp}
    {v₁ v₂ : Value} (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExpFields env ρ [.mk a₁ e₁, .mk a₂ e₂] [(a₁, v₁), (a₂, v₂)] := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  refine ⟨max n₁ n₂ + 1, ?_⟩
  have e₁ := evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := evalExp_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  simp [evalExpFields, e₁, e₂]

/-! ## The encoding of value sequences -/

/-- A value instruction is encoded as its value. -/
theorem adminToV_toAdmin (v : Val) : adminToV v.toAdmin = valV v := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> rfl

/-- A value sequence is encoded elementwise as values. -/
theorem adminsToV_vals (vs : List Val) : adminsToV (vals vs) = vs.map valV := by
  simp [adminsToV_eq_map, vals, adminToV_toAdmin]

/-- `instrsToV` is `List.map instrToV`. -/
theorem instrsToV_eq_map : ∀ l : List Instr, instrsToV l = l.map instrToV
  | [] => by simp [instrsToV]
  | i :: l => by simp [instrsToV, instrsToV_eq_map l]

/-- An instruction sequence, run as administrative instructions, is encoded as itself. -/
theorem adminsToV_expression (body : List Instr) :
    adminsToV (expression body) = instrsToV body := by
  simp [adminsToV_eq_map, expression, instrsToV_eq_map, adminToV]

/-! ## Lifting a `Step_read` or `Step_pure` step -/

section Lift

variable {H : Type} {env : Env} {hn : H → String}

/-- A `Step_read` step between typed configurations with the same state is a `Step` step. -/
theorem fwd_of_read (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 1 Equiv.ExecStepRules.readRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : TypedV env stateT (stateV hn s f) → TypedV env instrsT (.list (adminsToV is)) →
      TypedV env instrsT (.list (adminsToV is')) →
      SRead env (cfgV (stateV hn s f) (adminsToV is)) (adminsToV is')) :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨-, his'⟩ := (T.config _).1 hc'
  exact sstep_read hr hz his his' (h hz his his')

/-- A `Step_pure` step between typed configurations with the same state is a `Step` step. -/
theorem fwd_of_pure (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : TypedV env instrsT (.list (adminsToV is)) → TypedV env instrsT (.list (adminsToV is')) →
      SPure env (adminsToV is) (adminsToV is')) :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨-, his'⟩ := (T.config _).1 hc'
  exact sstep_pure hr hz his his' (h his his')

end Lift

/-! ## The `throw_ref` rules without premises -/

section Rules

variable {env : Env}

/-- `Step_read/throw_ref-null`. -/
theorem sread_throwRefNull (hr : HasRuleAt env "Step_read" "%~>%" 12 throwRefNullRule)
    {z : Value} (hz : TypedV env stateT z) :
    SRead env (cfgV z (adminsToV [.ref .null, .plain .throwRef])) (adminsToV [.trap]) := by
  let ρ := VarEnv.empty.bindVals [("z", z)]
  have fz : ρ.findVal? "z" = some z := rfl
  exact dderives_of_ruleAt hr _ (QuantsOk.cons fz (hz ρ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list2 (evalExp_caseNil "REF.NULL_ADDR") (evalExp_caseNil "THROW_REF"))))
      (evalExp_list1 (evalExp_caseNil "TRAP")))
    prems_nil

/-- `Step_read/throw_ref-label`. -/
theorem sread_throwRefLabel (hr : HasRuleAt env "Step_read" "%~>%" 14 throwRefLabelRule)
    {z : Value} {n a : Nat} {cont : List Instr} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (hc : TypedV env instrsT (.list (instrsToV cont)))
    (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV z (adminsToV [.label n cont (throwing a)])) (adminsToV (throwing a)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", .num (.natN n)),
    ("instr'*", .list (instrsToV cont)), ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fc : ρ.findVal? "instr'*" = some (.list (instrsToV cont)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons fc (hc ρ hρ) (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_iterPat (by decide) fc) (evalExp_throwExn fa))))))
      (evalExp_throwExn fa))
    prems_nil

/-- `Step_read/throw_ref-frame`. -/
theorem sread_throwRefFrame (hr : HasRuleAt env "Step_read" "%~>%" 15 throwRefFrameRule)
    {z : Value} {n a : Nat} {fi : Frame} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (hf : TypedV env frameT (frameV fi))
    (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV z (adminsToV [.frame n fi (throwing a)])) (adminsToV (throwing a)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", .num (.natN n)), ("f", frameV fi),
    ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have ff : ρ.findVal? "f" = some (frameV fi) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons ff (hf ρ hρ) (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff)
          (evalExp_throwExn fa))))))
      (evalExp_throwExn fa))
    prems_nil

/-- `Step_read/throw_ref-handler-empty`. -/
theorem sread_throwRefHandlerEmpty
    (hr : HasRuleAt env "Step_read" "%~>%" 16 throwRefHandlerEmptyRule)
    {z : Value} {n a : Nat} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV z (adminsToV [.handler n [] (throwing a)])) (adminsToV (throwing a)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", .num (.natN n)), ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) evalExp_nil
          (evalExp_throwExn fa))))))
      (evalExp_throwExn fa))
    prems_nil

/-- `Step_read/throw_ref-handler-catch_all`, as a rule body,
under any reading of relations and `otherwise`. -/
theorem body_throwRefHandlerCatchAll {O : ElseI} {els : Prop}
    {z : Value} {n a : Nat} {l : LabelIdx} {cs : List Catch} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) :
    RuleBody env (DDerives env O) els [] [] "%~>%" throwRefHandlerCatchAllRule
      (.tuple [cfgV z (adminsToV [.handler n (.catchAll l :: cs) (throwing a)]),
        .list (adminsToV [.plain (.br l)])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", .num (.natN n)), ("l", Encode.toValue l),
    ("catch'*", .list (cs.map Encode.toValue)), ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fl : ρ.findVal? "l" = some (Encode.toValue l) := rfl
  have fc : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact ruleBody_of
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fl (hl ρ hρ)
      (QuantsOk.cons fc (hcs ρ hρ) (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_var fl)))
            (evalExp_iterPat (by decide) fc))
          (evalExp_throwExn fa))))))
      (evalExp_list1 (evalExp_case (evalExp_var fl))))
    fun pr hpr => dprem_toPremW (prems_nil pr hpr)

/-- `Step_read/throw_ref-handler-catch_all`, as a declarative derivation. -/
theorem sread_throwRefHandlerCatchAll
    (hr : HasRuleAt env "Step_read" "%~>%" 19 throwRefHandlerCatchAllRule)
    {z : Value} {n a : Nat} {l : LabelIdx} {cs : List Catch} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV z (adminsToV [.handler n (.catchAll l :: cs) (throwing a)]))
      (adminsToV [.plain (.br l)]) :=
  dderives_of_body hr (body_throwRefHandlerCatchAll hz hn hl hcs ha)

/-- `Step_read/throw_ref-handler-catch_all_ref`, as a rule body,
under any reading of relations and `otherwise`. -/
theorem body_throwRefHandlerCatchAllRef {O : ElseI} {els : Prop}
    {z : Value} {n a : Nat} {l : LabelIdx} {cs : List Catch} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) :
    RuleBody env (DDerives env O) els [] [] "%~>%" throwRefHandlerCatchAllRefRule
      (.tuple [cfgV z (adminsToV [.handler n (.catchAllRef l :: cs) (throwing a)]),
        .list (adminsToV [.ref (.exn a), .plain (.br l)])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", .num (.natN n)), ("l", Encode.toValue l),
    ("catch'*", .list (cs.map Encode.toValue)), ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fl : ρ.findVal? "l" = some (Encode.toValue l) := rfl
  have fc : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact ruleBody_of
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fl (hl ρ hρ)
      (QuantsOk.cons fc (hcs ρ hρ) (QuantsOk.cons fa (ha ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_var fl)))
            (evalExp_iterPat (by decide) fc))
          (evalExp_throwExn fa))))))
      (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fl))))
    fun pr hpr => dprem_toPremW (prems_nil pr hpr)

/-- `Step_read/throw_ref-handler-catch_all_ref`, as a declarative derivation. -/
theorem sread_throwRefHandlerCatchAllRef
    (hr : HasRuleAt env "Step_read" "%~>%" 20 throwRefHandlerCatchAllRefRule)
    {z : Value} {n a : Nat} {l : LabelIdx} {cs : List Catch} (hz : TypedV env stateT z)
    (hn : TypedV env nT (.num (.natN n))) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) :
    SRead env (cfgV z (adminsToV [.handler n (.catchAllRef l :: cs) (throwing a)]))
      (adminsToV [.ref (.exn a), .plain (.br l)]) :=
  dderives_of_body hr (body_throwRefHandlerCatchAllRef hz hn hl hcs ha)

/-- `Step_read/throw_ref-instrs`: an exception propagates out of an instruction sequence. -/
theorem sread_throwRefInstrs (hr : HasRuleAt env "Step_read" "%~>%" 13 throwRefInstrsRule)
    {z : Value} {vs rest : List Value} {a : Nat} (hz : TypedV env stateT z)
    (hvs : TypedV env valsT (.list vs)) (ha : TypedV env addrT (.num (.natN a)))
    (hrest : TypedV env instrsT (.list rest)) (hne : vs ≠ [] ∨ rest ≠ []) :
    SRead env (cfgV z (vs ++ adminsToV (throwing a) ++ rest)) (adminsToV (throwing a)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("a", .num (.natN a)),
    ("instr*", .list rest)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fr : ρ.findVal? "instr*" = some (.list rest) := rfl
  have ev : EvalExp env ρ (Equiv.Execution.valsPat "val" "val*") (.list vs) :=
    evalExp_valsPat (by decide) fv
  have ev' : EvalExp env ρ (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
      (.list vs) := evalExp_iterPat (by decide) fv
  have er : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list rest) := evalExp_iterPat (by decide) fr
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SRead env (cfgV z (vs ++ ([adminToV (.ref (.exn a))] ++
      ([adminToV (.plain .throwRef)] ++ rest)))) (adminsToV (throwing a)) :=
    dderives_of_ruleAt hr _
      (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fv (hvs ρ hρ)
        (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fr (hrest ρ hρ) QuantsOk.nil))))
      (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
          (evalExp_cat ev (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_var fa)))
            (evalExp_cat (evalExp_list1 (evalExp_caseNil "THROW_REF")) er)))))
        (evalExp_throwExn fa))
      (prems_one (.ifPr (hd ▸ evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er))))
  simpa [adminsToV, List.append_assoc] using hg

/-- `Step_pure/handler-vals`. -/
theorem spure_handlerVals
    (hr : HasRuleAt env "Step_pure" "%~>%" 25 Equiv.Execution.handlerValsRule)
    {n : Nat} {cs : List Catch} {vs : List Value}
    (hn : TypedV env nT (.num (.natN n)))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (hvs : TypedV env valsT (.list vs)) :
    SPure env [.case "HANDLER_%{%}%" (.tuple [.num (.natN n), .list (cs.map Encode.toValue),
      .list vs])] vs := by
  let ρ := VarEnv.empty.bindVals [("n", .num (.natN n)),
    ("catch*", .list (cs.map Encode.toValue)), ("val*", .list vs)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fc : ρ.findVal? "catch*" = some (.list (cs.map Encode.toValue)) := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have ev : EvalExp env ρ (Equiv.Execution.valsPat "val" "val*") (.list vs) :=
    evalExp_valsPat (by decide) fv
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc) ev))) ev)
    prems_nil

end Rules

/-! ## `throw_ref-handler-catch` and `-catch_ref`: the tag premises -/

section Catch

variable {H : Type} {env : Env} {hn : H → String}

/-- `$exninst(z)[a]`, at an encoded state whose store has the exception `e` at `a`. -/
theorem evalExp_exninstAt (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {a : Nat} {e : ExnInst} (he : s.exns[a]? = some e)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hd : ρ.findDef? "exninst" = none) :
    EvalExp env ρ (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) (exnInstV e) :=
  evalExp_idxE_iff.2 ⟨_, a,
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef hd
      (Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil)).mp (Hp.exninst s f)),
    evalExp_var fa, by simp [Value.idx?, he]⟩

/-- `$tagaddr(z)[x.0]`, at an encoded state whose frame has the tag address `ta` at `x`. -/
theorem evalExp_tagaddrAt (Hp : HelpersInv env hn) {ρ : VarEnv} {s : Store H} {f : Frame}
    {x : TagIdx} {ta : Nat} (ht : f.module.tags[x.toNat]? = some ta)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (hd : ρ.findDef? "tagaddr" = none) :
    EvalExp env ρ (.idxE (.callE "tagaddr" [.expA (.varE "z")])
      (.projE (.uncaseE (.varE "x") "%") 0)) (.num (.natN ta)) :=
  evalExp_idxE_iff.2 ⟨_, x.toNat,
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef hd
      (Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil)).mp (Hp.tagaddr s f)),
    (Equiv.ExecReadControl.evalExp_idxProj_iff fx).2 ⟨_, rfl, rfl⟩,
    by simp [Value.idx?, ht]⟩

/-- The two premises of `throw_ref-handler-catch` and `-catch_ref`: the exception's tag is the
clause's, and `val*` is the exception's fields. -/
theorem dprem_catchTag (Hp : HelpersInv env hn) {O : ElseI} {els : Prop} {ρ : VarEnv}
    {s : Store H} {f : Frame} {x : TagIdx} {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (fv : ρ.findVal? "val*" = some (.list (e.fields.map valV)))
    (hd₁ : ρ.findDef? "exninst" = none) (hd₂ : ρ.findDef? "tagaddr" = none) :
    ∀ p ∈ [Prem.ifPr (.cmpE .eqOp .boolT
         (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "TAG")
         (.idxE (.callE "tagaddr" [.expA (.varE "z")]) (.projE (.uncaseE (.varE "x") "%") 0))),
       Prem.ifPr (.cmpE .eqOp .boolT
         (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
         (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "FIELDS"))],
      DPrem env O els ρ p := by
  have hx := evalExp_exninstAt Hp he fz fa hd₁
  refine prems_two (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, ?_, evalExp_tagaddrAt Hp ht fz fx hd₂,
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩))
    (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_iterPat (by decide) fv, ?_,
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩))
  · exact evalExp_dotE_iff.2 ⟨_, hx, rfl⟩
  · exact evalExp_dotE_iff.2 ⟨_, hx, rfl⟩

/-- `Step_read/throw_ref-handler-catch`, as a rule body,
under any reading of relations and `otherwise`. -/
theorem body_throwRefHandlerCatch {O : ElseI} {els : Prop} (Hp : HelpersInv env hn)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    RuleBody env (DDerives env O) els [] [] "%~>%" throwRefHandlerCatchRule
      (.tuple [cfgV (stateV hn s f) (adminsToV [.handler n (.catch_ x l :: cs) (throwing a)]),
        .list (adminsToV (vals e.fields ++ [.plain (.br l)]))]) := by
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN n)),
    ("x", Encode.toValue x), ("l", Encode.toValue l), ("catch'*", .list (cs.map Encode.toValue)),
    ("a", .num (.natN a)), ("val*", .list (e.fields.map valV))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fx : ρ.findVal? "x" = some (Encode.toValue x) := rfl
  have fl : ρ.findVal? "l" = some (Encode.toValue l) := rfl
  have fc : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (e.fields.map valV)) := rfl
  rw [adminsToV_append, adminsToV_vals]
  exact ruleBody_of
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn₀ ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons fl (hl ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fv (hvs ρ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx)
              (evalExp_var fl))))
            (evalExp_iterPat (by decide) fc))
          (evalExp_throwExn fa))))))
      (evalExp_cat (evalExp_valsPat (by decide) fv)
        (evalExp_list1 (evalExp_case (evalExp_var fl)))))
    fun pr hpr => dprem_toPremW ((dprem_catchTag Hp he ht fz fx fa fv rfl rfl) pr hpr)

/-- `Step_read/throw_ref-handler-catch`, as a declarative derivation. -/
theorem sread_throwRefHandlerCatch (Hp : Helpers env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 17 throwRefHandlerCatchRule)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    SRead env (cfgV (stateV hn s f) (adminsToV [.handler n (.catch_ x l :: cs) (throwing a)]))
      (adminsToV (vals e.fields ++ [.plain (.br l)])) :=
  dderives_of_body hr (body_throwRefHandlerCatch Hp he ht hz hn₀ hx hl hcs ha hvs)

/-- `Step_read/throw_ref-handler-catch_ref`, as a rule body,
under any reading of relations and `otherwise`. -/
theorem body_throwRefHandlerCatchRef {O : ElseI} {els : Prop} (Hp : HelpersInv env hn)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    RuleBody env (DDerives env O) els [] [] "%~>%" throwRefHandlerCatchRefRule
      (.tuple [cfgV (stateV hn s f) (adminsToV [.handler n (.catchRef x l :: cs) (throwing a)]),
        .list (adminsToV (vals e.fields ++ [.ref (.exn a), .plain (.br l)]))]) := by
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN n)),
    ("x", Encode.toValue x), ("l", Encode.toValue l), ("catch'*", .list (cs.map Encode.toValue)),
    ("a", .num (.natN a)), ("val*", .list (e.fields.map valV))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN n)) := rfl
  have fx : ρ.findVal? "x" = some (Encode.toValue x) := rfl
  have fl : ρ.findVal? "l" = some (Encode.toValue l) := rfl
  have fc : ρ.findVal? "catch'*" = some (.list (cs.map Encode.toValue)) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (e.fields.map valV)) := rfl
  rw [adminsToV_append, adminsToV_vals]
  exact ruleBody_of
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn₀ ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons fl (hl ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fv (hvs ρ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
          (evalExp_cat (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx)
              (evalExp_var fl))))
            (evalExp_iterPat (by decide) fc))
          (evalExp_throwExn fa))))))
      (evalExp_cat (evalExp_valsPat (by decide) fv)
        (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fl)))))
    fun pr hpr => dprem_toPremW ((dprem_catchTag Hp he ht fz fx fa fv rfl rfl) pr hpr)

/-- `Step_read/throw_ref-handler-catch_ref`, as a declarative derivation. -/
theorem sread_throwRefHandlerCatchRef (Hp : Helpers env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 18 throwRefHandlerCatchRefRule)
    {s : Store H} {f : Frame} {n a : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {e : ExnInst} (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag)
    (hz : TypedV env stateT (stateV hn s f)) (hn₀ : TypedV env nT (.num (.natN n)))
    (hx : TypedV env idxT (Encode.toValue x)) (hl : TypedV env labelidxT (Encode.toValue l))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (ha : TypedV env addrT (.num (.natN a))) (hvs : TypedV env valsT (.list (e.fields.map valV))) :
    SRead env (cfgV (stateV hn s f) (adminsToV [.handler n (.catchRef x l :: cs) (throwing a)]))
      (adminsToV (vals e.fields ++ [.ref (.exn a), .plain (.br l)])) :=
  dderives_of_body hr (body_throwRefHandlerCatchRef Hp he ht hz hn₀ hx hl hcs ha hvs)

end Catch

/-! ## `try_table` and `throw` -/

section Block

variable {H : Type} {env : Env} {hn : H → String}

/-- `Step_read/try_table`: entering a `try_table` block installs its handler around a label. -/
theorem sread_tryTable (Hp : Helpers env hn)
    (hr : HasRuleAt env "Step_read" "%~>%" 22 tryTableRule)
    {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (hz : TypedV env stateT (stateV hn s f)) (hmT : TypedV env mT (.num (.natN vs.length)))
    (hvs : TypedV env valsT (.list (vs.map valV)))
    (hbtT : TypedV env blocktypeT (Encode.toValue bt))
    (hcs : TypedV env catchesT (.list (cs.map Encode.toValue)))
    (hbody : TypedV env instrsT (.list (instrsToV body)))
    (hnT : TypedV env nT (.num (.natN t₂.length))) :
    SRead env (cfgV (stateV hn s f) (vs.map valV ++ [instrToV (.tryTable bt cs body)]))
      [.case "HANDLER_%{%}%" (.tuple [.num (.natN t₂.length), .list (cs.map Encode.toValue),
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN t₂.length), .list [],
          .list (vs.map valV ++ instrsToV body)])]])] := by
  obtain ⟨v₁, v₂, hl₁, hl₂, hv₁, hv₂, happ⟩ := Hp.blocktype s f bt t₁ t₂ hbt
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("m", .num (.natN vs.length)),
    ("val*", .list (vs.map valV)), ("bt", Encode.toValue bt),
    ("catch*", .list (cs.map Encode.toValue)), ("instr*", .list (instrsToV body)),
    ("n", .num (.natN t₂.length)), ("t_1*", .list v₁), ("t_2*", .list v₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN vs.length)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (vs.map valV)) := rfl
  have fb : ρ.findVal? "bt" = some (Encode.toValue bt) := rfl
  have fc : ρ.findVal? "catch*" = some (.list (cs.map Encode.toValue)) := rfl
  have fi : ρ.findVal? "instr*" = some (.list (instrsToV body)) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN t₂.length)) := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list v₁) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list v₂) := rfl
  have fm' : ρ.findVal? "m" = some (.num (.natN (vs.map valV).length)) := by
    rw [List.length_map]; exact fm
  have fm₁ : ρ.findVal? "m" = some (.num (.natN v₁.length)) := by rw [hl₁, ← hm]; exact fm
  have fn₂ : ρ.findVal? "n" = some (.num (.natN v₂.length)) := by rw [hl₂]; exact fn
  have ev : EvalExp env ρ (Equiv.Execution.valsNPat "val" "val*" "m") (.list (vs.map valV)) :=
    evalExp_valsNPat (by decide) fv fm'
  have ec : EvalExp env ρ (.iterE (.varE "catch") (.mk .list [.mk "catch" (.varE "catch*")]))
      (.list (cs.map Encode.toValue)) := evalExp_iterPat (by decide) fc
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list (instrsToV body)) := evalExp_iterPat (by decide) fi
  have hcall : EvalExp env ρ (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")])
      (instrTypeV v₁ v₂) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fb)
        Equiv.evalArgs_nil))).mp happ)
  exact dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fm (hmT ρ hρ) (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fb (hbtT ρ hρ) (QuantsOk.cons fc (hcs ρ hρ)
      (QuantsOk.cons fi (hbody ρ hρ) (QuantsOk.cons fn (hnT ρ hρ)
      (QuantsOk.cons f₁ (hv₁ ρ hρ) (QuantsOk.cons f₂ (hv₂ ρ hρ) QuantsOk.nil)))))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_cat ev (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fb)
          (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons ec evalExps_nil, rfl⟩)) ei))))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) evalExp_nil
          (evalExp_cat ev ei))))))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, hcall,
      evalExp_case (evalExp_tup3
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_varN (by decide) f₁ fm₁)
          evalExps_nil, rfl⟩))
        evalExp_nil
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_varN (by decide) f₂ fn₂)
          evalExps_nil, rfl⟩))),
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)))

/-- `Store.tag?` finds the tag address in the frame's module. -/
theorem tags_of_tag? {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (h : s.tag? f x = some (ta, ti)) : f.module.tags[x.toNat]? = some ta := by
  unfold Store.tag? at h
  cases ht : f.module.tags[x.toNat]? with
  | none => simp [ht] at h
  | some a => cases hs : s.tags[a]? <;> simp_all

/-- `Step/throw`: a new exception instance is allocated and thrown. -/
theorem sstep_throw (Hp : Helpers env hn)
    (hr : HasRuleAt env "Step" "%~>%" 10 Equiv.ExecStepRules.throwRule)
    {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} (htag : s.tag? f x = some (ta, ti))
    (hex : Expand ti.type (.func ts .nil)) (hlen : vs.length = ts.length)
    (hz : TypedV env stateT (stateV hn s f)) (hnT : TypedV env nT (.num (.natN vs.length)))
    (hvs : TypedV env valsT (.list (vs.map valV))) (hx : TypedV env idxT (Encode.toValue x))
    (hexn : TypedV env exninstT (exnInstV ⟨ta, vs⟩))
    (ha : TypedV env addrT (.num (.natN s.exns.length))) :
    SStep env (cfgV (stateV hn s f) (vs.map valV ++ [instrToV (.throw x)]))
      (cfgV (stateV hn (s.addExn ⟨ta, vs⟩) f) (adminsToV (throwing s.exns.length))) := by
  obtain ⟨tvs, htl, htv, hexp⟩ := Hp.expand ti.type ts hex
  let ρ := VarEnv.empty.bindVals [("z", stateV hn s f), ("n", .num (.natN vs.length)),
    ("val*", .list (vs.map valV)), ("x", Encode.toValue x), ("exn", exnInstV ⟨ta, vs⟩),
    ("a", .num (.natN s.exns.length)), ("t*", .list tvs)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stateV hn s f) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN vs.length)) := rfl
  have fv : ρ.findVal? "val*" = some (.list (vs.map valV)) := rfl
  have fx : ρ.findVal? "x" = some (Encode.toValue x) := rfl
  have fe : ρ.findVal? "exn" = some (exnInstV ⟨ta, vs⟩) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN s.exns.length)) := rfl
  have ft : ρ.findVal? "t*" = some (.list tvs) := rfl
  have fn' : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)) := by
    rw [List.length_map]; exact fn
  have fnt : ρ.findVal? "n" = some (.num (.natN tvs.length)) := by rw [htl, ← hlen]; exact fn
  have hz₁ : EvalArgs env ρ [.expA (.varE "z")] [.val (stateV hn s f)] :=
    Equiv.evalArgs_cons (evalExp_var fz) Equiv.evalArgs_nil
  have htagE : EvalExp env ρ (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")])
      (Equiv.RuntimeBridge.tagInstToValue CT ti) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
        Equiv.evalArgs_nil))).mp (Hp.tag s f x ta ti htag))
  have hdt : EvalExp env ρ (.callE "as_deftype"
      [.expA (.dotE (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")])
      (CT.defType ti.type) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_dotE_iff.2 ⟨_, htagE, rfl⟩) Equiv.evalArgs_nil)).mp
      (Hp.asDeftype ti.type))
  have hexnE : EvalExp env ρ (.callE "exninst" [.expA (.varE "z")])
      (.list (s.exns.map exnInstV)) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl hz₁).mp (Hp.exninst s f))
  have haddE : EvalExp env ρ (.callE "add_exninst" [.expA (.varE "z"),
      .expA (.listE [.varE "exn"])]) (stateV hn (s.addExn ⟨ta, vs⟩) f) :=
    evalExp_callE_iff.2 ((Equiv.ExecNumeric.applies_iff_callDef rfl
      (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_list1 (evalExp_var fe))
        Equiv.evalArgs_nil))).mp (Hp.addExn s f ⟨ta, vs⟩))
  have hp₁ : DPrem env (otherwise env) (otherwise env "Step" [] 10
      (.tuple [cfgV (stateV hn s f) (vs.map valV ++ [instrToV (.throw x)]),
        cfgV (stateV hn (s.addExn ⟨ta, vs⟩) f) (adminsToV (throwing s.exns.length))])) ρ
      (.rulePr "Expand" [] "%~~%" (.tupE [.callE "as_deftype"
          [.expA (.dotE (.callE "tag" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")],
        .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t")
            (.mk (.listN (.varE "n") none) [.mk "t" (.varE "t*")])]),
          .caseE "%" (.tupE [.listE []])])])) :=
    .rulePr (evalArgs_nil _ _) (evalExp_tup2 hdt (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_varN (by decide) ft fnt)
        evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_nil evalExps_nil, rfl⟩)))))
      hexp
  refine dderives_of_ruleAt hr _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hnT ρ hρ) (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fx (hx ρ hρ) (QuantsOk.cons fe (hexn ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons ft (htv ρ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_cat (evalExp_valsNPat (by decide) fv fn')
          (evalExp_list1 (evalExp_case (evalExp_var fx))))))
      (evalExp_case (evalExp_tup2 haddE (evalExp_throwExn fa))))
    ?_
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact hp₁
  · exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fa,
      evalExp_lenE_iff.2 ⟨_, hexnE, by simp⟩, Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)
  · exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fe,
      evalExp_strE_iff.2 ⟨_, evalExpFields_two
        (evalExp_tagaddrAt Hp (tags_of_tag? htag) fz fx rfl)
        (evalExp_varN (by decide) fv fn'), rfl⟩,
      Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

end Block

end Silmaril.Wasm.SpecTec.Sim.Exn
