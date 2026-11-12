module

public import Silmaril.Wasm.SpecTec.Sim.Control.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Family C: shared lemmas

* `typedV_list_cons_iff`, `typedV_list_iff`, `typedV_list_append`: the IL type `t*` is checked
  elementwise, so typing of a sequence splits and recombines;
* `adminToV_toAdmin`, `adminsToV_vals`, `adminToV_constI32`: the encoding of values as
  instructions;
* `evalExp_valsNPat`, `evalExp_listNil`, `evalExp_caseNil`, `evalExp_sub`: evaluation helpers
  for the conclusions of the control rules;
* `fwd_of_spure`, `fwd_of_sread`: a `Step_pure` (`Step_read`) derivation between the images of
  two code sequences is a forward step of the configurations, at any store and frame.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV valsNPat iterRows_singleton)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-! ## Sequences are typed elementwise -/

/-- `t*` at the empty list. -/
theorem hasTyp_list_nil {env : Env} {ρ : VarEnv} {t : Typ} :
    HasTyp env ρ (.iterT t .list) (.list []) :=
  ⟨2, by simp [hasTyp, hasTypList, Value.asList?]⟩

/-- One unfolding of `t*` at `v :: vs`. -/
theorem hasTyp_list_cons_unfold {j : Nat} {env : Env} {ρ : VarEnv} {t : Typ} {v : Value}
    {vs : List Value} :
    hasTyp (j + 2) env ρ (.iterT t .list) (.list (v :: vs)) =
      (hasTyp j env ρ t v >>= fun b => if b then hasTypList j env ρ t vs else .ok false) := by
  simp only [hasTyp, Value.asList?, hasTypList]

/-- `t*` at `v :: vs`, read off a definite answer. -/
theorem hasTyp_list_cons_of_ok {j : Nat} {env : Env} {ρ : VarEnv} {t : Typ} {v : Value}
    {vs : List Value} (h : hasTyp (j + 2) env ρ (.iterT t .list) (.list (v :: vs)) = .ok true) :
    HasTyp env ρ t v ∧ HasTyp env ρ (.iterT t .list) (.list vs) := by
  rw [hasTyp_list_cons_unfold, Res.bind_eq_ok] at h
  obtain ⟨b, hb, hrest⟩ := h
  cases b with
  | false => simp at hrest
  | true =>
    have hl : hasTypList j env ρ t vs = .ok true := by simpa using hrest
    exact ⟨⟨j, hb⟩, ⟨j + 1, by simpa [hasTyp, Value.asList?] using hl⟩⟩

/-- `t*` at `v :: vs` from its parts. -/
theorem hasTyp_list_cons_of {env : Env} {ρ : VarEnv} {t : Typ} {v : Value} {vs : List Value}
    {n₁ m : Nat} (h₁ : hasTyp n₁ env ρ t v = .ok true) (h₂ : hasTypList m env ρ t vs = .ok true) :
    HasTyp env ρ (.iterT t .list) (.list (v :: vs)) := by
  refine ⟨max n₁ m + 2, ?_⟩
  rw [hasTyp_list_cons_unfold, Res.bind_eq_ok]
  exact ⟨true, hasTyp_ok_of_le (by omega) h₁, by simpa using hasTypList_ok_of_le (by omega) h₂⟩

/-- `t*` at `v :: vs`: `v` is a `t` and `vs` a `t*`. -/
theorem hasTyp_list_cons_iff {env : Env} {ρ : VarEnv} {t : Typ} {v : Value} {vs : List Value} :
    HasTyp env ρ (.iterT t .list) (.list (v :: vs)) ↔
      HasTyp env ρ t v ∧ HasTyp env ρ (.iterT t .list) (.list vs) := by
  constructor
  · rintro ⟨n, h⟩
    match n, h with
    | 0, h => simp [hasTyp] at h
    | 1, h => simp [hasTyp, Value.asList?, hasTypList] at h
    | j + 2, h => exact hasTyp_list_cons_of_ok h
  · rintro ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    match n₂, h₂ with
    | 0, h₂ => simp [hasTyp] at h₂
    | m + 1, h₂ => exact hasTyp_list_cons_of h₁ (by simpa [hasTyp, Value.asList?] using h₂)

/-- `TypedV` at `t*` and the empty list. -/
theorem typedV_list_nil {env : Env} {t : Typ} : TypedV env (.iterT t .list) (.list []) :=
  fun _ _ => hasTyp_list_nil

/-- `TypedV` at `t*` and `v :: vs`. -/
theorem typedV_list_cons_iff {env : Env} {t : Typ} {v : Value} {vs : List Value} :
    TypedV env (.iterT t .list) (.list (v :: vs)) ↔
      TypedV env t v ∧ TypedV env (.iterT t .list) (.list vs) :=
  ⟨fun h => ⟨fun ρ hρ => (hasTyp_list_cons_iff.1 (h ρ hρ)).1,
      fun ρ hρ => (hasTyp_list_cons_iff.1 (h ρ hρ)).2⟩,
    fun ⟨h₁, h₂⟩ ρ hρ => hasTyp_list_cons_iff.2 ⟨h₁ ρ hρ, h₂ ρ hρ⟩⟩

/-- `TypedV` at `t*` is elementwise. -/
theorem typedV_list_iff {env : Env} {t : Typ} :
    ∀ {vs : List Value}, TypedV env (.iterT t .list) (.list vs) ↔ ∀ v ∈ vs, TypedV env t v
  | [] => by simpa using typedV_list_nil
  | v :: vs => by
      rw [typedV_list_cons_iff, typedV_list_iff]
      simp

/-- `TypedV` at `t*` splits over `++`. -/
theorem typedV_list_append {env : Env} {t : Typ} {a b : List Value} :
    TypedV env (.iterT t .list) (.list (a ++ b)) ↔
      TypedV env (.iterT t .list) (.list a) ∧ TypedV env (.iterT t .list) (.list b) := by
  simp only [typedV_list_iff, List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (.inl hv), fun v hv => h v (.inr hv)⟩,
    fun ⟨h₁, h₂⟩ v hv => hv.elim (h₁ v) (h₂ v)⟩

/-- A one-element sequence. -/
theorem typedV_list_single {env : Env} {t : Typ} {v : Value} :
    TypedV env (.iterT t .list) (.list [v]) ↔ TypedV env t v := by
  rw [typedV_list_cons_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, typedV_list_nil⟩⟩

/-! ## Values as instructions -/

/-- A value as an instruction is encoded as the value. -/
theorem adminToV_toAdmin (v : Val) : adminToV v.toAdmin = valV v := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

/-- `vals vs` is encoded as `vs.map valV`. -/
theorem adminsToV_vals (vs : List Val) : adminsToV (vals vs) = vs.map valV := by
  simp [adminsToV_eq_map, vals, adminToV_toAdmin]

/-- `CONST I32 c`. -/
theorem adminToV_constI32 (c : BitVec 32) :
    adminToV (constI32 c) = .case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]) := rfl

/-! ## Evaluation helpers -/

/-- The empty list literal. -/
theorem evalExp_listNil {env : Env} {ρ : VarEnv} : EvalExp env ρ (.listE []) (.list []) :=
  evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩

/-- A nullary case `OP`. -/
theorem evalExp_caseNil {env : Env} {ρ : VarEnv} {op : MixopS} :
    EvalExp env ρ (.caseE op (.tupE [])) (caseNilV op) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- A subsort coercion is transparent. -/
theorem evalExp_sub {env : Env} {ρ : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : EvalExp env ρ e v) : EvalExp env ρ (.subE e t₁ t₂) v :=
  evalExp_subE_iff.2 h

/-- A two-element list literal. -/
theorem evalExp_list2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.listE [e₁, e₂]) (.list [v₁, v₂]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil), rfl⟩

/-- A three-element list literal. -/
theorem evalExp_list3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.listE [e₁, e₂, e₃]) (.list [v₁, v₂, v₃]) :=
  evalExp_listE_iff.2
    ⟨_, evalExps_cons h₁ (evalExps_cons h₂ (evalExps_cons h₃ evalExps_nil)), rfl⟩

/-- One round per element, each evaluating the round's own variable. -/
theorem mapM_rounds_var {env : Env} {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_") :
    ∀ ws : List Value, (ws.map fun w => [(x, w)]).mapM
      (fun r => evalExp 2 env (ρ.bindVals r) (.subE (.varE x) (.varT "val" []) (.varT "instr" [])))
      = .ok ws
  | [] => rfl
  | w :: ws => by
      have hw : evalExp 2 env (ρ.bindVals [(x, w)])
          (.subE (.varE x) (.varT "val" []) (.varT "instr" [])) = .ok w := by
        simp [evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx, Res.ofOption]
      have ih := mapM_rounds_var (env := env) (ρ := ρ) hx ws
      simp only [List.map_cons, List.mapM_cons, hw, ih]
      rfl

/-- `val^n` with the counter bound to the domain's length denotes the domain. -/
theorem evalExp_valsNPat {env : Env} {ρ : VarEnv} {x d c : IL.Id} {ws : List Value}
    (hx : x ≠ "_") (hc : ρ.findVal? c = some (.num (.natN ws.length)))
    (hd : ρ.findVal? d = some (.list ws)) :
    EvalExp env ρ (valsNPat x d c) (.list ws) := by
  unfold valsNPat
  refine evalExp_iterE_iff.mpr ⟨5, ?_⟩
  have hdoms : evalDoms 4 env ρ [.mk x (.varE d)] = .ok [(x, Value.list ws)] := by
    simp [evalDoms, domVar, domSrc, evalExp, hd]
  have hcount : evalExp 4 env ρ (.varE c) = .ok (.num (.natN ws.length)) := by
    simp [evalExp, hc]
  have hlist : evalIterList 4 env ρ (.subE (.varE x) (.varT "val" []) (.varT "instr" []))
      [(x, Value.list ws)] none ws.length = .ok (.list ws) := by
    rw [evalIterList]
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
    refine ⟨[(x, ws)], by simp [Value.asList?], by simp, ws, ?_, rfl⟩
    rw [iterRows_singleton, evalRounds]
    exact mapM_rounds_var hx ws
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  exact ⟨_, rfl, _, rfl, ws.length, rfl, hlist⟩

/-! ## Lifting a `Step_pure` or `Step_read` derivation to a forward step -/

section Lift

variable {H : Type} {env : Env} {hn : H → String}

/-- A `Step_pure` derivation between the images of two code sequences is a forward step. -/
theorem fwd_of_spure (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : SPure env (adminsToV is) (adminsToV is')) : FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨-, his'⟩ := (T.config _).1 hc'
  exact sstep_pure hr hz his his' h

/-- A `Step_read` derivation from the image of `c` is a forward step that keeps the state. -/
theorem fwd_of_sread (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 1 Equiv.ExecStepRules.readRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : SRead env (configV hn ⟨s, f, is⟩) (adminsToV is')) :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨-, his'⟩ := (T.config _).1 hc'
  exact sstep_read hr hz his his' h

end Lift

end Silmaril.Wasm.SpecTec.Sim
