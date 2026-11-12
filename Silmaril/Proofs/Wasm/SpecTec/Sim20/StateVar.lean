module

public import Silmaril.Wasm.SpecTec.Sim20.State.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureConcat
public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Eval
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Basic

/-!
# References and variables: wasm-2.0 rules against V2, rule by rule

The rules of `Sim20.State.Defs`, each at the image of the V2 left-hand side of the constructor
that transcribes it, under the Round 6 backend reading `FiresB` on `simEnv20 B`:

* `Step_pure` 55 `local.tee` (`localTee_iff`) and 28 `ref.is_null-true` (`refIsNullTrue_iff`);
* `Step_read` 7 `local.get` (`localGet_iff`), 8 `global.get` (`globalGet_iff`) and 6 `ref.func`
  (`refFunc_iff`), at configurations where V2's lookup is defined;
* `Step` 4 `local.set` (`localSet_iff`), at an index in range (V2's `Step.localSet` premise).

The rules without premises are read through `firesB_noPrems_iff`, which needs no closedness of
their relation (`Step` is not closed: `Step/pure` and `Step/read` consult relations). The
state accessors `$local`, `$global`, `$funcaddr`, `$with_local` of the 2.0 script differ from
3.0's (2.0 matches `(s; f)` directly and has no `?(val)` locals), so they are evaluated here
afresh (`evalExp_local20`, …), with the generic call and path lemmas of `Sim.State.Eval`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly evalExp_tup2 evalExp_list1 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB ruleConcl hasOptNil ruleBodyB_iff_of_not)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathSet_idx pathSet_dot
  pathSet_root evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Pure (firesB20_inv firesB20_of quant_val prems_nil prems_one ifPrem
  evalExp_caseNil evalExp_list2 evalExp_list3 evalExp_tup2_inv adminToV_toAdmin)

variable (B : Builtins)

set_option maxRecDepth 100000

/-! ## Provenance -/

theorem hasRuleAt_refIsNullTrue :
    HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 28 refIsNullTrueRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_localTee : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 55 localTeeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_refFunc : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 6 refFuncRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_localGet : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 7 localGetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_globalGet : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 8 globalGetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_localSet : HasRuleAt (simEnv20 B) "Step" "%~>%" 4 localSetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Rules without premises, under the backend reading -/

/-- **A rule without premises fires under the backend reading exactly when some assignment of
its quantifiers evaluates its conclusion**, whatever the rest of its relation. -/
theorem firesB_noPrems_iff {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {e : Exp} (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e []))
    (hn : hasOptNil e = false) {v : Value} :
    FiresB env x k v ↔ ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  constructor
  · rintro ⟨t', rules', r, hrel', hr, hb⟩
    have e₁ : rules' = rules := by
      rw [hrel] at hrel'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
      exact hrel'.2.2.2.symm
    have e₂ : r = .ruleD nm qs "%~>%" e [] := by
      rw [e₁, hk] at hr
      exact (Option.some.inj hr).symm
    subst e₂
    obtain ⟨-, ρ₀, σ, hps, hq, he, -⟩ := (ruleBodyB_iff_of_not hn).1 hb
    cases hps
    exact ⟨σ, hq, he⟩
  · rintro ⟨σ, hq, he⟩
    exact ⟨t, rules, _, hrel, hk,
      (ruleBodyB_iff_of_not hn).2 ⟨rfl, VarEnv.empty, σ, rfl, hq, he, fun _ h => nomatch h⟩⟩

/-! ## `local.tee` (`Step_pure` 55) -/

/-- The conclusion of `local.tee`, evaluated. -/
theorem eval_localTee {env : Env} {ρ : VarEnv} {u X : Value} (fu : ρ.findVal? "val" = some u)
    (fx : ρ.findVal? "x" = some X) :
    EvalExp env ρ (ruleConcl localTeeRule) (.tuple [.list [u, .case "LOCAL.TEE" X],
      .list [u, u, .case "LOCAL.SET" X]]) :=
  evalExp_tup2 (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fu)) (evalExp_case (evalExp_var fx)))
    (evalExp_list3 (evalExp_subE_iff.2 (evalExp_var fu)) (evalExp_subE_iff.2 (evalExp_var fu))
      (evalExp_case (evalExp_var fx)))

/-- The image of `local.tee`'s two sides. -/
theorem adminsToV_localTee (v : Val) (x : LocalIdx) :
    adminsToV [v.toAdmin, .plain (.localTee x)] = [valV v, .case "LOCAL.TEE" (idxV x)] ∧
      adminsToV [v.toAdmin, v.toAdmin, .plain (.localSet x)] =
        [valV v, valV v, .case "LOCAL.SET" (idxV x)] := by
  constructor
  · show [adminToV v.toAdmin, instrToV (.localTee x)] = _
    rw [adminToV_toAdmin]; rfl
  · show [adminToV v.toAdmin, adminToV v.toAdmin, instrToV (.localSet x)] = _
    rw [adminToV_toAdmin]; rfl

/-- **`Step_pure/local.tee` is `PureStep.localTee`.** -/
theorem localTee_iff {v : Val} {x : LocalIdx} (hv : TypedV (simEnv20 B) (.varT "val" []) (valV v))
    (hx : TypedV (simEnv20 B) idxT (idxV x)) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 55 (.tuple [.list (adminsToV [v.toAdmin, .plain (.localTee x)]), w]) ↔
      w = .list (adminsToV [v.toAdmin, v.toAdmin, .plain (.localSet x)]) := by
  rw [(adminsToV_localTee v x).1, (adminsToV_localTee v x).2]
  constructor
  · intro hf
    obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_localTee B) hf
    obtain ⟨u, fu⟩ := quant_val (x := "val") (t := .varT "val" []) hq (by simp)
    obtain ⟨X, fx⟩ := quant_val (x := "x") (t := idxT) hq (by simp)
    have hu : Value.tuple [.list [valV v, .case "LOCAL.TEE" (idxV x)], w] =
        .tuple [.list [u, .case "LOCAL.TEE" X], .list [u, u, .case "LOCAL.SET" X]] :=
      EvalExp.unique he (eval_localTee fu fx)
    simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
      and_true] at hu
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hu
    rfl
  · rintro rfl
    exact firesB20_of (hasRuleAt_localTee B) [("val", valV v), ("x", idxV x)]
      (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hx _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil)) (eval_localTee rfl rfl) prems_nil

/-! ## `ref.is_null-true` (`Step_pure` 28) -/

/-- The conclusion of `ref.is_null-true`, evaluated. -/
theorem eval_refIsNullTrue {env : Env} {ρ : VarEnv} {R : Value} (fr : ρ.findVal? "ref" = some R) :
    EvalExp env ρ (ruleConcl refIsNullTrueRule) (.tuple [.list [R, caseNilV "REF.IS_NULL"],
      .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])]]) :=
  evalExp_tup2 (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fr)) evalExp_caseNil)
    (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_pct 1))))

/-- The image of `ref.is_null`'s left-hand side and of `CONST I32 1`. -/
theorem adminsToV_refIsNull (r : Ref) :
    adminsToV [aref r, .plain .refIsNull] = [refV r, caseNilV "REF.IS_NULL"] ∧
      adminsToV [constI32 1] = [.case "CONST" (.tuple [caseNilV "I32", pctV 1])] := by
  constructor
  · show [adminToV (Val.ref r).toAdmin, instrToV .refIsNull] = _
    rw [adminToV_toAdmin]; rfl
  · rfl

/-- `ref = REF.NULL rt`, read back. -/
theorem null_of_refV {r : Ref} {T : Value} (h : refV r = .case "REF.NULL" T) :
    ∃ t, r = .null t ∧ refTypeV t = T := by
  cases r with
  | null t => exact ⟨t, rfl, (Value.case.inj h).2⟩
  | funcAddr a => exact absurd (Value.case.inj h).1 (by decide)
  | hostAddr a => exact absurd (Value.case.inj h).1 (by decide)

/-- `ref.is_null-true`, read back. -/
theorem refIsNullTrue_inv {r : Ref} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 28 (.tuple [.list [refV r, caseNilV "REF.IS_NULL"], w])) :
    (∃ t, r = .null t) ∧ w = .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])] := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_refIsNullTrue B) hf
  obtain ⟨R, fr⟩ := quant_val (x := "ref") (t := refT) hq (by simp)
  obtain ⟨T, ft⟩ := quant_val (x := "rt") (t := reftypeT) hq (by simp)
  have hu : Value.tuple [.list [refV r, caseNilV "REF.IS_NULL"], w] =
      .tuple [.list [R, caseNilV "REF.IS_NULL"],
        .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])]] :=
    EvalExp.unique he (eval_refIsNullTrue fr)
  have hu' : refV r = R ∧ w = .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])] := by
    simpa only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, and_true] using hu
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ (List.mem_singleton_self _)))
  have e₁ : v₁ = refV r := EvalExp.unique h₁ (evalExp_var (hu'.1 ▸ fr))
  have e₂ : v₂ = .case "REF.NULL" T := EvalExp.unique h₂ (evalExp_case (evalExp_var ft))
  have heq : refV r = .case "REF.NULL" T := e₁ ▸ e₂ ▸ cmpValues_eq_true_iff.1 hc
  obtain ⟨t, ht, -⟩ := null_of_refV heq
  exact ⟨⟨t, ht⟩, hu'.2⟩

/-- `ref.is_null-true`, fired. -/
theorem refIsNullTrue_fires {t : V2.RefType} (hr : TypedV (simEnv20 B) refT (refV (.null t)))
    (ht : TypedV (simEnv20 B) reftypeT (refTypeV t)) :
    FiresB (simEnv20 B) "Step_pure" 28 (.tuple [.list [refV (.null t), caseNilV "REF.IS_NULL"],
      .list [.case "CONST" (.tuple [caseNilV "I32", pctV 1])]]) := by
  let σ : List (IL.Id × Value) := [("ref", refV (.null t)), ("rt", refTypeV t)]
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV (.null t)) := rfl
  have hc : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "ref") (.caseE "REF.NULL" (.varE "rt"))) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fr, evalExp_case (evalExp_var rfl),
      cmpValues_eq_true_iff.2 rfl⟩
  exact firesB20_of (hasRuleAt_refIsNullTrue B) σ
    (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (ht _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil)) (eval_refIsNullTrue fr) (prems_one (.ifPr hc))

/-- **`Step_pure/ref.is_null-true` is `PureStep.refIsNullTrue`.** -/
theorem refIsNullTrue_iff {r : Ref} (hr : TypedV (simEnv20 B) refT (refV r))
    (ht : ∀ t, r = .null t → TypedV (simEnv20 B) reftypeT (refTypeV t)) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 28 (.tuple [.list (adminsToV [aref r, .plain .refIsNull]), w]) ↔
      (∃ t, r = .null t) ∧ w = .list (adminsToV [constI32 1]) := by
  rw [(adminsToV_refIsNull r).1, (adminsToV_refIsNull r).2]
  refine ⟨refIsNullTrue_inv B, ?_⟩
  rintro ⟨⟨t, rfl⟩, rfl⟩
  exact refIsNullTrue_fires B hr (ht t rfl)

/-! ## The 2.0 state accessors -/

open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 idxPayload)

/-- `(s; f), x`, the argument pattern of the 2.0 accessors. -/
abbrev sfxPat : List Arg := [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"])), .expA (.varE "x")]

/-- `(s; f), x, v`, the argument pattern of `$with_local`. -/
abbrev sfxvPat : List Arg :=
  [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"])), .expA (.varE "x"), .expA (.varE "v")]

/-- `(s; f)`, the argument pattern of `$funcaddr`. -/
abbrev sfPat : List Arg := [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))]

theorem hasClause_local20 : HasClause1 (simEnv20 B) "local" sfxPat
    (.idxE (.dotE (.varE "f") "LOCALS") idxPayload) := ⟨_, _, _, rfl⟩

theorem hasClause_global20 : HasClause1 (simEnv20 B) "global" sfxPat
    (.idxE (.dotE (.varE "s") "GLOBALS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS")
      idxPayload)) := ⟨_, _, _, rfl⟩

theorem hasClause_funcaddr20 : HasClause1 (simEnv20 B) "funcaddr" sfPat
    (.dotE (.dotE (.varE "f") "MODULE") "FUNCS") := ⟨_, _, _, rfl⟩

theorem hasClause_withLocal20 : HasClause1 (simEnv20 B) "with_local" sfxvPat
    (.caseE "%;%" (.tupE [.varE "s", .updE (.varE "f") (.idxP (.dotP .rootP "LOCALS") idxPayload)
      (.varE "v")])) := ⟨_, _, _, rfl⟩

/-- `(s; f)` matches a state. -/
theorem matchExp_state {env : Env} {S F : Value} :
    MatchExp env VarEnv.empty (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))
      (.case "%;%" (.tuple [S, F])) ((VarEnv.empty.bindVal "s" S).bindVal "f" F) :=
  matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2 ⟨[S, F], rfl,
    Equiv.Execution.matchExps_two_iff.2 ⟨S, F, _, rfl, matchExp_varE rfl, matchExp_varE rfl⟩⟩)

/-- `(s; f), x` matches a state and an index. -/
theorem matchArgs_sfx {env : Env} {S F X : Value} :
    MatchArgs env VarEnv.empty sfxPat [.val (.case "%;%" (.tuple [S, F])), .val X]
      (((VarEnv.empty.bindVal "s" S).bindVal "f" F).bindVal "x" X) :=
  matchArgs_cons (matchArg_expA matchExp_state)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)

/-- `(s; f), x, v` matches a state, an index and a value. -/
theorem matchArgs_sfxv {env : Env} {S F X V : Value} :
    MatchArgs env VarEnv.empty sfxvPat [.val (.case "%;%" (.tuple [S, F])), .val X, .val V]
      ((((VarEnv.empty.bindVal "s" S).bindVal "f" F).bindVal "x" X).bindVal "v" V) :=
  matchArgs_cons (matchArg_expA matchExp_state)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))

/-- `(s; f)` matches a state, as an argument list. -/
theorem matchArgs_sf {env : Env} {S F : Value} :
    MatchArgs env VarEnv.empty sfPat [.val (.case "%;%" (.tuple [S, F]))]
      ((VarEnv.empty.bindVal "s" S).bindVal "f" F) :=
  matchArgs_cons (matchArg_expA matchExp_state) matchArgs_nil

variable {H : Type} (hn : H → String)

/-- The frame's locals. -/
theorem frameV_locals (f : Frame) :
    (frameV f).field? "LOCALS" = some (.list (f.locals.map valV)) := rfl

/-- The frame's module. -/
theorem frameV_module (f : Frame) : (frameV f).field? "MODULE" = some (moduleInstV f.module) := rfl

/-- **`$local(z, x)`**, at a 2.0 state and a local index in range. -/
theorem evalExp_local20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : LocalIdx}
    {v : Val} (hρ : ρ.findDef? "local" = none) (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f))
    (hx : EvalExp (simEnv20 B) ρ ex (idxV x)) (hv : f.locals[x.toNat]? = some v) :
    EvalExp (simEnv20 B) ρ (.callE "local" [.expA ez, .expA ex]) (valV v) :=
  evalExp_call1 (hasClause_local20 B) hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨frameV f,
      evalExp_var rfl, frameV_locals f⟩, evalExp_idxPayload rfl,
      by simp [Value.idx?, List.getElem?_map, hv]⟩)

/-- **`$global(z, x)`**, at a 2.0 state whose module lists global address `a` at `x`. -/
theorem evalExp_global20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : GlobalIdx}
    {a : Nat} {g : GlobalInst} (hρ : ρ.findDef? "global" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    EvalExp (simEnv20 B) ρ (.callE "global" [.expA ez, .expA ex]) (globalInstV g) :=
  evalExp_call1 (hasClause_global20 B) hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a, evalExp_dotE_iff.2 ⟨storeV hn s, evalExp_var rfl, rfl⟩,
      evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
        evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, frameV_module f⟩, rfl⟩,
        evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, hg]⟩)

/-- **`$funcaddr(z)`**, the frame's function addresses. -/
theorem evalExp_funcaddr20 {ρ : VarEnv} {ez : Exp} {s : Store H} {f : Frame}
    (hρ : ρ.findDef? "funcaddr" = none) (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) :
    EvalExp (simEnv20 B) ρ (.callE "funcaddr" [.expA ez]) (addrsV f.module.funcs) :=
  evalExp_call1 (hasClause_funcaddr20 B) hρ (evalArgs_cons hz evalArgs_nil) matchArgs_sf
    (evalExp_dotE_iff.2 ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl,
      frameV_module f⟩, rfl⟩)

/-- **`$with_local(z, x, v)`**, at a local index in range. -/
theorem evalExp_withLocal20 {ρ : VarEnv} {ez ex ev : Exp} {s : Store H} {f : Frame}
    {x : LocalIdx} {v : Val} (hρ : ρ.findDef? "with_local" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (hv : EvalExp (simEnv20 B) ρ ev (valV v)) (hlt : x.toNat < f.locals.length) :
    EvalExp (simEnv20 B) ρ (.callE "with_local" [.expA ez, .expA ex, .expA ev])
      (stateV hn s (f.setLocal x v)) := by
  refine evalExp_call1 (hasClause_withLocal20 B) hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hv evalArgs_nil))) matchArgs_sfxv ?_
  refine evalExp_case (evalExp_tup2 (evalExp_var rfl) ?_)
  refine evalExp_updE_iff.2 ⟨frameV f, valV v, evalExp_var rfl, evalExp_var rfl, ?_⟩
  have hs : Value.setIdx (.list (f.locals.map valV)) x.toNat (valV v) =
      some (.list ((f.locals.map valV).set x.toNat (valV v))) := by
    simp [Value.setIdx, hlt]
  have hf : (frameV f).setField "LOCALS" (.list ((f.locals.map valV).set x.toNat (valV v))) =
      some (frameV (f.setLocal x v)) := by
    simp [frameV, Value.setField, Frame.setLocal, List.map_set]
  exact pathSet_idx (pathGet_dot pathGet_root (frameV_locals f)) (evalExp_idxPayload rfl) hs
    (pathSet_dot pathGet_root hf pathSet_root)

/-! ## `Step_read` -/

/-- The image of a one-instruction configuration. -/
theorem configV_single (s : Store H) (f : Frame) (a : Admin) :
    configV hn ⟨s, f, [a]⟩ = .case "%;%" (.tuple [stateV hn s f, .list [adminToV a]]) := rfl

/-- The left-hand side `z; [OP x]` of a one-instruction `Step_read` rule, read back. -/
theorem read1_lhs {σ : List (IL.Id × Value)} {op : MixopS} {s : Store H} {f : Frame} {a : Admin}
    {Z X X' : Value} (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some Z)
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some X) (ha : adminToV a = .case op X')
    (h : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [.caseE op (.varE "x")]])) (configV hn ⟨s, f, [a]⟩)) :
    Z = stateV hn s f ∧ X = X' := by
  have hu : Value.case "%;%" (.tuple [Z, .list [.case op X]]) = configV hn ⟨s, f, [a]⟩ :=
    EvalExp.unique (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_var fx))))) h
  rw [configV_single, ha] at hu
  simp only [Value.case.injEq, Value.tuple.injEq, Value.list.injEq, List.cons.injEq, true_and,
    and_true] at hu
  exact ⟨hu.1, hu.2⟩

/-- **A one-instruction `Step_read` rule without premises**, `z; [OP x] ~> rhs`, at the image of
a V2 configuration `s; f; [a]` with `a`'s image `OP X`: it fires with `w` iff `w` is what `rhs`
evaluates to with `z, x` bound to the state and `X`. -/
theorem read1_iff {k : Nat} {nm : IL.Id} {op : MixopS} {rhs : Exp} {s : Store H} {f : Frame}
    {a : Admin} {X W : Value}
    (h : HasRuleAt (simEnv20 B) "Step_read" "%~>%" k (.ruleD nm [.expP "z" stateT, .expP "x" idxT]
      "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE op (.varE "x")]]), rhs]) []))
    (hno : hasOptNil (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE op (.varE "x")]]),
      rhs]) = false)
    (ha : adminToV a = .case op X)
    (hr : ∀ σ : List (IL.Id × Value), (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) →
      (VarEnv.empty.bindVals σ).findVal? "x" = some X → EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) rhs W)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hx : TypedV (simEnv20 B) idxT X) {w : Value} :
    FiresB (simEnv20 B) "Step_read" k (.tuple [configV hn ⟨s, f, [a]⟩, w]) ↔ w = W := by
  rw [firesB_noPrems_iff h hno]
  constructor
  · rintro ⟨σ, hq, he⟩
    obtain ⟨Z, fz⟩ := quant_val (x := "z") (t := stateT) hq (by simp)
    obtain ⟨X', fx⟩ := quant_val (x := "x") (t := idxT) hq (by simp)
    obtain ⟨hl, hrhs⟩ := evalExp_tup2_inv he
    obtain ⟨rfl, rfl⟩ := read1_lhs B hn fz fx ha hl
    exact EvalExp.unique hrhs (hr σ fz fx)
  · rintro rfl
    refine ⟨[("z", stateV hn s f), ("x", X)], QuantsOk.cons rfl (hz _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil), ?_⟩
    have hc : configV hn ⟨s, f, [a]⟩ = .case "%;%" (.tuple [stateV hn s f, .list [.case op X]]) := by
      rw [configV_single, ha]
    rw [hc]
    exact evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_var rfl))))) (hr _ rfl rfl)

/-- **`Step_read/local.get` is `ReadStep.localGet`**, where the local is defined. -/
theorem localGet_iff {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.locals[x.toNat]? = some v)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hx : TypedV (simEnv20 B) idxT (idxV x))
    {w : Value} :
    FiresB (simEnv20 B) "Step_read" 7 (.tuple [configV hn ⟨s, f, [.plain (.localGet x)]⟩, w]) ↔
      w = .list (adminsToV [v.toAdmin]) := by
  have hw : Value.list (adminsToV [v.toAdmin]) = .list [valV v] := by
    show Value.list [adminToV v.toAdmin] = _
    rw [adminToV_toAdmin]
  rw [hw]
  exact read1_iff B hn (hasRuleAt_localGet B) rfl rfl (fun σ fz fx => evalExp_list1
    (evalExp_subE_iff.2 (evalExp_local20 B hn rfl (evalExp_var fz) (evalExp_var fx) hv))) hz hx

/-- `ReadStep.localGet` at the same configuration. -/
theorem localGet_step {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.locals[x.toNat]? = some v) :
    ReadStep s f [.plain (.localGet x)] [v.toAdmin] :=
  .localGet hv

/-- **`Step_read/global.get` is `ReadStep.globalGet`**, where the global is defined. -/
theorem globalGet_iff {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hx : TypedV (simEnv20 B) idxT (idxV x))
    {w : Value} :
    FiresB (simEnv20 B) "Step_read" 8 (.tuple [configV hn ⟨s, f, [.plain (.globalGet x)]⟩, w]) ↔
      w = .list (adminsToV [g.value.toAdmin]) := by
  have hw : Value.list (adminsToV [g.value.toAdmin]) = .list [valV g.value] := by
    show Value.list [adminToV g.value.toAdmin] = _
    rw [adminToV_toAdmin]
  rw [hw]
  exact read1_iff B hn (hasRuleAt_globalGet B) rfl rfl (fun σ fz fx => evalExp_list1
    (evalExp_subE_iff.2 (evalExp_dotE_iff.2 ⟨globalInstV g,
      evalExp_global20 B hn rfl (evalExp_var fz) (evalExp_var fx) ha hg, rfl⟩))) hz hx

/-- `ReadStep.globalGet` at the same configuration. -/
theorem globalGet_step {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    ReadStep s f [.plain (.globalGet x)] [g.value.toAdmin] :=
  .globalGet (by simp [State.global?, ModuleInst.globalAddr?, Store.globalInst?, ha, hg])

/-- **`Step_read/ref.func` is `ReadStep.refFunc`**, where the function address is defined. -/
theorem refFunc_iff {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hx : TypedV (simEnv20 B) idxT (idxV x))
    {w : Value} :
    FiresB (simEnv20 B) "Step_read" 6 (.tuple [configV hn ⟨s, f, [.plain (.refFunc x)]⟩, w]) ↔
      w = .list (adminsToV [.refFuncAddr a]) :=
  read1_iff B hn (hasRuleAt_refFunc B) rfl rfl (fun σ fz fx => evalExp_list1 (evalExp_case
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_funcaddr20 B hn rfl (evalExp_var fz),
      evalExp_idxPayload fx, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩))) hz hx

/-- `ReadStep.refFunc` at the same configuration. -/
theorem refFunc_step {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a) :
    ReadStep s f [.plain (.refFunc x)] [.refFuncAddr a] :=
  .refFunc (by simpa [ModuleInst.funcAddr?] using ha)

/-! ## `Step` -/

/-- The conclusion of `local.set`, evaluated, at a local index in range. -/
theorem eval_localSet {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fv : (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x)) (hlt : x.toNat < f.locals.length) :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (ruleConcl localSetRule)
      (.tuple [.case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "LOCAL.SET" (idxV x)]]),
        configV hn ⟨s, f.setLocal x v, []⟩]) :=
  evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fv)) (evalExp_case (evalExp_var fx)))))
    (evalExp_case (evalExp_tup2 (evalExp_withLocal20 B hn rfl (evalExp_var fz) (evalExp_var fx)
      (evalExp_var fv) hlt) Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_list0))

/-- The image of `local.set`'s configuration. -/
theorem configV_localSet (s : Store H) (f : Frame) (x : LocalIdx) (v : Val) :
    configV hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "LOCAL.SET" (idxV x)]]) := by
  show Value.case "%;%" (.tuple [stateV hn s f, .list [adminToV v.toAdmin, instrToV (.localSet x)]]) = _
  rw [adminToV_toAdmin]
  rfl

/-- `local.set`, read back, at a local index in range. -/
theorem localSet_inv {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hlt : x.toNat < f.locals.length) {w : Value}
    (hf : FiresB (simEnv20 B) "Step" 4 (.tuple [.case "%;%" (.tuple [stateV hn s f,
      .list [valV v, .case "LOCAL.SET" (idxV x)]]), w])) :
    w = configV hn ⟨s, f.setLocal x v, []⟩ := by
  obtain ⟨σ, hq, he⟩ := (firesB_noPrems_iff (hasRuleAt_localSet B) rfl).1 hf
  obtain ⟨Z, fz⟩ := quant_val (x := "z") (t := stateT) hq (by simp)
  obtain ⟨U, fu⟩ := quant_val (x := "val") (t := .varT "val" []) hq (by simp)
  obtain ⟨X, fx⟩ := quant_val (x := "x") (t := idxT) hq (by simp)
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  have hu : Value.case "%;%" (.tuple [Z, .list [U, .case "LOCAL.SET" X]]) =
      .case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "LOCAL.SET" (idxV x)]]) :=
    EvalExp.unique (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fu)) (evalExp_case (evalExp_var fx))))) hl
  have hu' : Z = stateV hn s f ∧ U = valV v ∧ X = idxV x := by
    simpa only [Value.case.injEq, Value.tuple.injEq, Value.list.injEq, List.cons.injEq, true_and,
      and_true] using hu
  have hev := eval_localSet B hn (hu'.1 ▸ fz) (hu'.2.1 ▸ fu) (hu'.2.2 ▸ fx) hlt
  exact EvalExp.unique hr (evalExp_tup2_inv hev).2

/-- **`Step/local.set` is `Step.localSet`**, at a local index in range. -/
theorem localSet_iff {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hlt : x.toNat < f.locals.length)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hv : TypedV (simEnv20 B) (.varT "val" []) (valV v)) (hx : TypedV (simEnv20 B) idxT (idxV x))
    {w : Value} :
    FiresB (simEnv20 B) "Step" 4 (.tuple [configV hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩, w]) ↔
      w = configV hn ⟨s, f.setLocal x v, []⟩ := by
  rw [configV_localSet]
  refine ⟨localSet_inv B hn hlt, ?_⟩
  rintro rfl
  exact (firesB_noPrems_iff (hasRuleAt_localSet B) rfl).2
    ⟨[("z", stateV hn s f), ("val", valV v), ("x", idxV x)],
      QuantsOk.cons rfl (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons rfl (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)),
      eval_localSet B hn rfl rfl rfl hlt⟩

/-- `Step.localSet` at the same configuration. -/
theorem localSet_step (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} (hlt : x.toNat < f.locals.length) :
    Step P host ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩ :=
  .localSet hlt

end Silmaril.Wasm.SpecTec.Sim20.State
