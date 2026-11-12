module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRead
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step_read`'s control rules, characterised

The control rules of `Step_read` — `block`, `loop`, `br_on_cast`, `call`,
`return_call`, `return_call_ref`, `throw_ref`, `try_table` and `ref.func` —
each characterised by an exact iff saying when `RuleFires` holds of it.

Every statement keeps the state **abstract**: `$blocktype_`, `$funcinst`,
`$moduleinst`, `$exninst`, `$tagaddr` and `$inst_reftype` appear only through
`ExecNumeric.Applies`, never unfolded into Silmaril's runtime structures.  The
bridge that connects them to `Silmaril/Wasm/Execution/Core/Runtime.lean` is a
separate workstream, and nothing here waits for it.

## What is proved

Twenty rules characterised exactly — `ref.func`, `call`, `return_call`, the
four `br_on_cast*`, the four administrative `throw_ref` rules (`-null`,
`-instrs`, `-label`, `-frame`), `-handler-empty`, the five dispatching
`throw_ref-handler-*` rules, and `return_call_ref-label`, `-handler` and
`-frame-null` — and four proved **unfireable**: `block`, `loop`, `try_table`
and `return_call_ref-frame-addr`.  Nothing in the family is left open.

## The findings

* **`block`, `loop` and `try_table` derive nothing.**  Their side condition
  `if $blocktype_(z, bt) = t_1^m -> t_2^n` mentions `t_1*` and `t_2*`, which
  occur nowhere else in the rule.  An `IfPr` *evaluates* its expression — the
  IL has a separate `LetPr` for the binding form — and an iteration over an
  unbound domain has no value, so the premise holds in no scope the conclusion
  can build.  `Step_read/return_call_ref-frame-addr` has the same shape with a
  `RulePr` (`Expand`) and the same consequence
  (`not_ruleFires_returnCallRefFrameAddr`) — there the conclusion *does*
  match, and the proof computes the scope it builds exactly to show `t_1*` is
  not in it.  This is an erasure: the source premise binds, the printed IL
  cannot.
* **`else` is vacuous, so three pairs overlap.**  `br_on_cast-fail` fires on
  references that `-succeed` also accepts (`ruleFires_brOnCastFail_onSucceeding`
  exhibits a configuration with two different results), `br_on_cast_fail-fail`
  likewise, and `throw_ref-handler-next` fires on *every* non-empty handler,
  including the ones the four dispatching rules fire on.
* **Narrowings.**  `call`, `return_call` and the two `throw_ref-handler-catch*`
  rules index a state accessor by a value the conclusion matched, and `IdxE`
  needs a `nat`: they fire only when the matched `addr` is a bare numeral.
* **Erasures.**  `throw_ref-handler-next` discards a clause matched by a bare
  variable — an *arbitrary* value, never inspected.  Every `val*` prefix is
  likewise unconstrained: `matchExp` is transparent to the `val <: instr`
  coercion, so nothing in the matcher requires those positions to be values.

## The `CatE` search, decided

Five of these rules — `throw_ref-instrs`, `return_call_ref-label`,
`-handler`, `-frame-null` and `-frame-addr` — concatenate two patterns
*neither* of which has a `patLen`: a `val*`-headed prefix against an
`instr*`-tailed suffix.  `matchExp` falls through to `Res.scan` and takes the
**first** split that matches, so an exact iff has to say which split that is.

It is **the first occurrence of the rule's marker**.  `val*` is fresh, so the
left operand matches every prefix and a split succeeds exactly when the marker
does; the search stops at the earliest position carrying it, and `val*` is
bound to everything before.  `throw_ref-instrs` and
`return_call_ref-frame-null` carry *two* markers in a row, so what they stop
at is the first adjacent *pair*; that is what the quantified side condition of
their iffs says, and `exists_first_mem`/`exists_first_adj` are what name it.

This is worth recording because `Step/ctxt-instrs`, the other rule of the
reduction relation with this shape, comes out the opposite way
(`Equiv/ExecStepRules.lean`'s `matchExp_ctxtInstrsLhs`): its right operand is
a *fresh iteration* rather than a marker, so it matches the empty list, the
search stops at split `0`, and the rule binds `val* = instr* = ε` however long
the sequence is.  A literal marker is what makes the search informative, and
all five rules here have one — so for them the search really does find the
prose rule's decomposition, up to the `val <: instr` erasure recorded above.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecReadControl

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.ExecDefault (matchDefault_iff matchExp_idxE_iff)
open Silmaril.SpecTec.Equiv.ExecRef (premsHold_else_iff)

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## Three matching principles the family needs

`Equiv/ExecDefault.lean` inverted `matchExp` at a `CallE` and an `IdxE`; the
control rules reach the same fall-through at a `DotE` (`$funcinst(z)[a].TYPE`
in `call`).  And they are the first rules whose conclusions *concatenate*:
`matchExp` at a `CatE` has three branches, of which this family uses the two
deterministic ones — the left operand has a length, or the left has none and
the right does.  `Equiv/Execution.lean` built both as *constructions*
(`matchExp_catE_ofLeft`, `matchExp_catE_ofRight`); the characterisations below
need them as **iffs**, which is what the two theorems here add. -/

/-- `matchExp` at a `DotE` is the default match: evaluate and compare. -/
theorem matchExp_dotE_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {a : AtomS} {v : Value} :
    MatchExp env ρ (.dotE e a) v ρ' ↔ EvalExp env ρ (.dotE e a) v ∧ ρ' = ρ := by
  rw [show MatchExp env ρ (.dotE e a) v ρ'
        ↔ ∃ n, matchDefault n env ρ (.dotE e a) v = .ok ρ' from ?_, matchDefault_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ m => exact ⟨m, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- **A concatenation whose left operand has a length, exactly.**  `patLen`
is monotone in the fuel, so a length found at *any* fuel is the one `matchExp`
uses, and the split is forced. -/
theorem matchExp_catE_leftLen_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value}
    {k m : Nat} (hj : patLen m env ρ e₁ = .ok k) :
    MatchExp env ρ (.catE e₁ e₂) v ρ' ↔
      ∃ vs σ, v = .list vs ∧ k ≤ vs.length ∧
        MatchExp env ρ e₁ (.list (vs.take k)) σ ∧
        MatchExp env σ e₂ (.list (vs.drop k)) ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    have hn' : matchExp (max n m + 1) env ρ (.catE e₁ e₂) v = .ok ρ' :=
      Validation.matchExp_ok_mono (by omega) hn
    have hp : patLen (max n m) env ρ e₁ = .ok k :=
      ((monoAt_of_le (show m ≤ max n m by omega)).patLen env ρ e₁).ok hj
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some,
      hp, Res.elimUndef_ok, Res.assert_eq_ok] at hn'
    obtain ⟨vs, rfl, hle, hm⟩ := hn'
    obtain ⟨σ, h₁, h₂⟩ := hm
    exact ⟨vs, σ, rfl, hle, ⟨_, h₁⟩, ⟨_, h₂⟩⟩
  · rintro ⟨vs, σ, rfl, hle, h₁, h₂⟩
    exact matchExp_catE_ofLeft hj hle h₁ h₂

/-- **A concatenation whose left operand has *no* length but whose right does,
exactly.**  This is the shape every `val* (BR l)`-style right-hand side has:
the marker is a literal list, so the split is forced from the end. -/
theorem matchExp_catE_rightLen_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value}
    {k m : Nat} (h₀ : NoPatLen env ρ e₁) (hj : patLen m env ρ e₂ = .ok k) :
    MatchExp env ρ (.catE e₁ e₂) v ρ' ↔
      ∃ vs σ, v = .list vs ∧ k ≤ vs.length ∧
        MatchExp env ρ e₁ (.list (vs.take (vs.length - k))) σ ∧
        MatchExp env σ e₂ (.list (vs.drop (vs.length - k))) ρ' := by
  obtain ⟨n₀, hn₀⟩ := h₀
  constructor
  · rintro ⟨n, hn⟩
    have hn' : matchExp (max (max n m) n₀ + 1) env ρ (.catE e₁ e₂) v = .ok ρ' :=
      Validation.matchExp_ok_mono (by omega) hn
    have hp₀ : patLen (max (max n m) n₀) env ρ e₁ = .error .undef :=
      patLen_undef_of_le (by omega) hn₀
    have hp : patLen (max (max n m) n₀) env ρ e₂ = .ok k :=
      ((monoAt_of_le (show m ≤ max (max n m) n₀ by omega)).patLen env ρ e₂).ok hj
    simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Value.asList?_eq_some,
      hp₀, Res.elimUndef_undef, hp, Res.elimUndef_ok, Res.assert_eq_ok] at hn'
    obtain ⟨vs, rfl, hle, hm⟩ := hn'
    obtain ⟨σ, h₁, h₂⟩ := hm
    exact ⟨vs, σ, rfl, hle, ⟨_, h₁⟩, ⟨_, h₂⟩⟩
  · rintro ⟨vs, σ, rfl, hle, h₁, h₂⟩
    exact matchExp_catE_ofRight ⟨n₀, hn₀⟩ hj hle h₁ h₂

/-- `Res.scan` answered, so one of its alternatives did. -/
theorem scan_ok_dest {α : Type} {f : Nat → Res α} :
    ∀ (k i : Nat) {a : α}, Res.scan f i k = .ok a → ∃ j, f j = .ok a
  | 0, i, _, h => ⟨i, h⟩
  | k + 1, i, a, h => by
      rw [Res.scan_succ] at h
      cases hfi : f i with
      | ok b => exact ⟨i, by rw [hfi, Res.elimUndef_ok] at h; rw [hfi]; exact h⟩
      | error er =>
          cases er with
          | outOfFuel => rw [hfi] at h; simp at h
          | undef => rw [hfi, Res.elimUndef_undef] at h; exact scan_ok_dest k (i + 1) h

/-- **A concatenation, destructured.**  All three of `matchExp`'s branches
agree on this much: the value is a list, and there is a split at which the two
operands match.  The two iffs above say *which* split, when the split is
forced; this says there is one even when the matcher had to search, and it is
what the negative results below need. -/
theorem matchExp_catE_dest {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : MatchExp env ρ (.catE e₁ e₂) v ρ') :
    ∃ vs k σ, v = .list vs ∧
      MatchExp env ρ e₁ (.list (vs.take k)) σ ∧
      MatchExp env σ e₂ (.list (vs.drop k)) ρ' := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [matchExp] at hn
  | succ n =>
      rw [matchExp] at hn
      obtain ⟨vs, hv, hm⟩ := Res.bind_eq_ok.1 hn
      rw [Res.ofOption_eq_ok, Value.asList?_eq_some] at hv
      subst hv
      have key : ∀ k, (matchExp n env ρ e₁ (.list (vs.take k)) >>= fun σ =>
          matchExp n env σ e₂ (.list (vs.drop k))) = .ok ρ' →
          ∃ vs' k σ, (Value.list vs : Value) = .list vs' ∧
            MatchExp env ρ e₁ (.list (vs'.take k)) σ ∧
            MatchExp env σ e₂ (.list (vs'.drop k)) ρ' := by
        intro k hk
        obtain ⟨σ, h₁, h₂⟩ := Res.bind_eq_ok.1 hk
        exact ⟨vs, k, σ, rfl, ⟨n, h₁⟩, ⟨n, h₂⟩⟩
      cases hp₁ : patLen n env ρ e₁ with
      | ok k =>
          rw [hp₁, Res.elimUndef_ok, Res.assert_eq_ok] at hm
          exact key k hm.2
      | error er₁ =>
          cases er₁ with
          | outOfFuel => rw [hp₁] at hm; simp at hm
          | undef =>
              rw [hp₁, Res.elimUndef_undef] at hm
              cases hp₂ : patLen n env ρ e₂ with
              | ok k =>
                  rw [hp₂, Res.elimUndef_ok, Res.assert_eq_ok] at hm
                  exact key _ hm.2
              | error er₂ =>
                  cases er₂ with
                  | outOfFuel => rw [hp₂] at hm; simp at hm
                  | undef =>
                      rw [hp₂, Res.elimUndef_undef] at hm
                      obtain ⟨j, hj⟩ := scan_ok_dest _ 0 hm
                      exact key j hj

/-- A `^n` iteration whose counter is an unbound variable has no `patLen`:
`patLen` falls back on evaluating the counter. -/
theorem noPatLen_iterE_listN_var {env : Env} {ρ : VarEnv} {e : Exp} {x y z : IL.Id}
    (hz : ρ.findVal? z = none) :
    NoPatLen env ρ (.iterE e (.mk (.listN (.varE z) none) [.mk x (.varE y)])) :=
  ⟨2, by simp [patLen, evalExp, hz, Res.ofOption, Bind.bind, Except.bind]⟩

/-- **An iteration over an unbound domain has no value.**  Every branch of
`evalIterE` evaluates the domains first, and an unbound variable has no value
at any fuel.  This is what makes the `$blocktype_` premises unsatisfiable. -/
theorem not_evalExp_iterE_of_unbound {env : Env} {ρ : VarEnv} {e : Exp} {it : Iter}
    {x y : IL.Id} {v : Value} (hy : ρ.findVal? y = none) :
    ¬ EvalExp env ρ (.iterE e (.mk it [.mk x (.varE y)])) v := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [evalExp] at hn
  | succ n =>
      simp only [evalExp] at hn
      cases n with
      | zero => cases it <;> simp [evalIterE] at hn
      | succ m =>
          have hd : ∀ xvs, evalDoms m env ρ [.mk x (.varE y)] ≠ .ok xvs := by
            intro xvs hc
            cases m with
            | zero => simp [evalDoms] at hc
            | succ m' =>
                rw [evalDoms] at hc
                simp only [List.mapM_cons, List.mapM_nil, domVar, domSrc] at hc
                cases hy' : evalExp m' env ρ (.varE y) with
                | ok u => exact evalExp_varE_ne_ok hy hy'
                | error er =>
                    rw [hy'] at hc
                    simp [Bind.bind, Except.bind, Functor.map, Except.map] at hc
          cases it <;>
            · simp only [evalIterE] at hn
              obtain ⟨xvs, h₁, -⟩ := Res.bind_eq_ok.1 hn
              exact hd xvs h₁

/-- An argument list headed by an expression, inverted. -/
theorem evalArgs_expA_cons_iff {env : Env} {ρ : VarEnv} {e : Exp} {args : List Arg}
    {ws : List ArgV} :
    EvalArgs env ρ (.expA e :: args) ws ↔
      ∃ u ws', EvalExp env ρ e u ∧ EvalArgs env ρ args ws' ∧ ws = .val u :: ws' := by
  constructor
  · rintro ⟨n, hn⟩
    match n, hn with
    | 0, hn => simp [evalArgs] at hn
    | 1, hn => simp [evalArgs, List.mapM_cons, evalArg] at hn
    | (m + 2), hn =>
        simp only [evalArgs, List.mapM_cons, Res.bind_eq_ok] at hn
        obtain ⟨w, hw, ws', hws, hres⟩ := hn
        simp only [evalArg, Res.map_eq_ok] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        exact ⟨u, ws', ⟨m, hu⟩, ⟨m + 2, by simpa only [evalArgs] using hws⟩,
          (Validation.okInj hres).symm⟩
  · rintro ⟨u, ws', hu, hws, rfl⟩
    exact evalArgs_cons hu hws

/-! ## The value shapes the family's conclusions use -/

/-- `s; f`, the `state` injection.  `br_on_cast` is the only part of this
family that destructures the state, and even it never looks inside `s` or
`f`. -/
def stateV (s f : Value) : Value := .case "%;%" (.tuple [s, f])

/-- `(REF.EXN_ADDR a) (THROW_REF)`, the two administrative instructions every
`throw_ref` rule propagates. -/
def throwExnV (a : Value) : List Value := [.case "REF.EXN_ADDR" a, caseNilV "THROW_REF"]

/-- What a rule requires of an index value: an injection by `%` whose tuple's
component `0` is the number.  The rules only ever project that component, so
this is exactly the requirement — the index is never destructured further. -/
def IdxIs (x : Value) (i : Nat) : Prop :=
  ∃ vs, x = .case "%" (.tuple vs) ∧ vs[0]? = some (.num (.natN i))

/-- The index projection `x!`%`.0`, as `IdxIs`. -/
theorem evalExp_idxProj_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {xv : Value} {i : Nat}
    (hx : ρ.findVal? x = some xv) :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) (.num (.natN i)) ↔ IdxIs xv i := by
  rw [evalExp_projE_iff]
  constructor
  · rintro ⟨vs, hv, -, hidx⟩
    rw [evalExp_uncaseE_iff, evalExp_varE_iff, hx] at hv
    exact ⟨vs, Option.some.inj hv, by simpa using hidx⟩
  · rintro ⟨vs, rfl, hidx⟩
    exact ⟨vs, evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 hx), by decide, by simpa using hidx⟩

/-- Every conclusion in this family reads `z; …` with `z` a fresh variable:
the state is carried, never inspected. -/
theorem matchExp_config_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (hz : ρ.findVal? "z" = none) :
    MatchExp env ρ (.caseE "%;%" (.tupE [.varE "z", e])) v ρ' ↔
      ∃ z w, v = .case "%;%" (.tuple [z, w]) ∧
        MatchExp env (ρ.bindVal "z" z) e w ρ' := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨vs, rfl, hvs⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨z, w, σ, rfl, hz', hw⟩ := matchExps_two_iff.1 hvs
    rw [matchExp_freshVar_iff hz] at hz'
    subst hz'
    exact ⟨z, w, rfl, hw⟩
  · rintro ⟨z, w, rfl, hw⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, (matchExp_freshVar_iff hz).2 rfl, hw⟩⟩⟩

/-- `[(REF.EXN_ADDR a) (THROW_REF)]`, binding the address. -/
theorem matchExp_throwExn_fresh {env : Env} {ρ ρ' : VarEnv} {v : Value}
    (ha : ρ.findVal? "a" = none) :
    MatchExp env ρ
      (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]) v ρ' ↔
      ∃ a, v = .list (throwExnV a) ∧ ρ' = ρ.bindVal "a" a := by
  rw [Validation.matchExp_list_iff]
  constructor
  · rintro ⟨vs, rfl, hvs⟩
    obtain ⟨p, q, σ, rfl, hp, hq⟩ := matchExps_two_iff.1 hvs
    obtain ⟨a, rfl, hav⟩ := Validation.matchExp_case_iff.1 hp
    rw [matchExp_freshVar_iff ha] at hav
    subst hav
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hq
    exact ⟨a, rfl, rfl⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨a, rfl, (matchExp_freshVar_iff ha).2 rfl⟩,
      matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩

/-- The same, with the address already bound: now it tests. -/
theorem matchExp_throwExn_bound {env : Env} {ρ ρ' : VarEnv} {v a : Value}
    (ha : ρ.findVal? "a" = some a) :
    MatchExp env ρ
      (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]) v ρ' ↔
      v = .list (throwExnV a) ∧ ρ' = ρ := by
  rw [Validation.matchExp_list_iff]
  constructor
  · rintro ⟨vs, rfl, hvs⟩
    obtain ⟨p, q, σ, rfl, hp, hq⟩ := matchExps_two_iff.1 hvs
    obtain ⟨a', rfl, hav⟩ := Validation.matchExp_case_iff.1 hp
    rw [matchExp_boundVar_iff ha] at hav
    obtain ⟨rfl, rfl⟩ := hav
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hq
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨a, rfl, (matchExp_boundVar_iff ha).2 ⟨rfl, rfl⟩⟩,
      matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩

/-! ## The administrative `throw_ref` rules

Four rules that propagate a thrown exception outwards.  None of them looks at
the state at all, and none has a premise: each is a pure rearrangement of the
configuration, characterised here for an **arbitrary** state value. -/

/-- **`Step_read/throw_ref-null`, characterised exactly.**  A null exception
reference traps, in every state. -/
theorem ruleFires_throwRefNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefNullRule ↔
      ∃ z, v = .tuple [ExecStep.configV z [caseNilV "REF.NULL_ADDR", caseNilV "THROW_REF"],
        .list [caseNilV "TRAP"]] := by
  unfold throwRefNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨is, rfl, his⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨i₁, i₂, τ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 his
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 h₁
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 h₂
    obtain ⟨js, rfl, hjs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨j, rfl, hj⟩ := matchExps_one_iff.1 hjs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hj
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/throw_ref-label`, characterised exactly.**  A thrown
exception escapes a label, discarding the label's continuation — for an
arbitrary arity value `n` and an arbitrary continuation. -/
theorem ruleFires_throwRefLabel_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefLabelRule ↔
      ∃ z n is a,
        v = .tuple [ExecStep.configV z
          [.case "LABEL_%{%}%" (.tuple [n, .list is, .list (throwExnV a)])],
          .list (throwExnV a)] := by
  unfold throwRefLabelRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨cs, rfl, hcs⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hcs
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨n, iv, tv, σ₁, σ₂, rfl, hn, hi, ht⟩ := matchExps_three_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)] at hi
    obtain ⟨is, rfl, his⟩ := hi
    rw [matchExp_freshVar_iff (by simp)] at his
    subst his
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    rw [matchExp_throwExn_bound (a := a) (by simp)] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ⟨z, n, is, a, rfl⟩
  · rintro ⟨z, n, is, a, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_iterE_list_iff (bindsVar_varE "instr'")
                    (by simp) (by simp)).2
                    ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
                  (matchExp_throwExn_fresh (by simp)).2 ⟨a, rfl, rfl⟩⟩⟩⟩⟩⟩⟩,
      (matchExp_throwExn_bound (a := a) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/throw_ref-frame`, characterised exactly.**  The same, out of
a frame: the frame value `f` is carried and never read. -/
theorem ruleFires_throwRefFrame_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefFrameRule ↔
      ∃ z n f a,
        v = .tuple [ExecStep.configV z
          [.case "FRAME_%{%}%" (.tuple [n, f, .list (throwExnV a)])],
          .list (throwExnV a)] := by
  unfold throwRefFrameRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨cs, rfl, hcs⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hcs
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨n, fv, tv, σ₁, σ₂, rfl, hn, hf, ht⟩ := matchExps_three_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_freshVar_iff (by simp)] at hf
    subst hf
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    rw [matchExp_throwExn_bound (a := a) (by simp)] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ⟨z, n, fv, a, rfl⟩
  · rintro ⟨z, n, f, a, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_throwExn_fresh (by simp)).2 ⟨a, rfl, rfl⟩⟩⟩⟩⟩⟩⟩,
      (matchExp_throwExn_bound (a := a) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/throw_ref-handler-empty`, characterised exactly.**  A handler
with no clauses left re-throws. -/
theorem ruleFires_throwRefHandlerEmpty_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefHandlerEmptyRule ↔
      ∃ z n a,
        v = .tuple [ExecStep.configV z
          [.case "HANDLER_%{%}%" (.tuple [n, .list [], .list (throwExnV a)])],
          .list (throwExnV a)] := by
  unfold throwRefHandlerEmptyRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨cs, rfl, hcs⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hcs
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨n, ev, tv, σ₁, σ₂, rfl, hn, he, ht⟩ := matchExps_three_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_listNil_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    rw [matchExp_throwExn_bound (a := a) (by simp)] at hr
    obtain ⟨rfl, -⟩ := hr
    exact ⟨z, n, a, rfl⟩
  · rintro ⟨z, n, a, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  matchExp_listNil_iff.2 ⟨rfl, rfl⟩,
                  (matchExp_throwExn_fresh (by simp)).2 ⟨a, rfl, rfl⟩⟩⟩⟩⟩⟩⟩,
      (matchExp_throwExn_bound (a := a) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-! ## `ref.func`, `call` and `return_call`

Three rules that read the module instance.  Each states exactly which
accessors it consults — `$moduleinst(z).FUNCS`, `$funcinst(z)` — through
`ExecNumeric.Applies`, and says nothing about what they compute.  Note the
**narrowing** each one records: `$funcinst(z)` is indexed by the value the
conclusion matched at `REF.FUNC_ADDR`, and `IdxE` needs a `nat`, so the rule
fires only when that value is a bare `nat` — which is what `syntax addr =
nat` makes it. -/

/-- **`Step_read/ref.func`, characterised exactly.**  `REF.FUNC x` becomes the
address `$moduleinst(z).FUNCS[x]`, in a state that is otherwise untouched. -/
theorem ruleFires_refFunc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refFuncRule ↔
      ∃ z x i mi fas fa,
        v = .tuple [ExecStep.configV z [.case "REF.FUNC" x],
          .list [.case "REF.FUNC_ADDR" fa]] ∧
        IdxIs x i ∧ ExecNumeric.Applies env "moduleinst" [.val z] mi ∧
        mi.field? "FUNCS" = some fas ∧ fas.idx? i = some fa := by
  unfold refFuncRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨is, rfl, his⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 his
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hc
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨js, rfl, hjs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨j, rfl, hj⟩ := matchExps_one_iff.1 hjs
    obtain ⟨fa, rfl, hfa⟩ := Validation.matchExp_case_iff.1 hj
    rw [matchExp_idxE_iff] at hfa
    obtain ⟨hev, -⟩ := hfa
    obtain ⟨fas, i, hfas, hi, hidx⟩ := evalExp_idxE_iff.1 hev
    obtain ⟨mi, hmi, hfield⟩ := evalExp_dotE_iff.1 hfas
    rw [evalExp_idxProj_iff (xv := x) (by simp)] at hi
    refine ⟨z, x, i, mi, fas, fa, rfl, hi, ?_, hfield, hidx⟩
    exact (ExecNumeric.applies_iff_callDef (ρ := (VarEnv.empty.bindVal "z" z).bindVal "x" x)
      rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mpr
      (evalExp_callE_iff.1 hmi)
  · rintro ⟨z, x, i, mi, fas, fa, rfl, hidxis, happ, hfield, hidx⟩
    refine ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            Validation.matchExp_case_iff.2 ⟨x, rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨fa, rfl, matchExp_idxE_iff.2 ⟨?_, rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_idxE_iff.2 ⟨fas, i, evalExp_dotE_iff.2 ⟨mi, ?_, hfield⟩,
      (evalExp_idxProj_iff (xv := x) (by simp)).2 hidxis, hidx⟩
    exact evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
      (ρ := (VarEnv.empty.bindVal "z" z).bindVal "x" x) rfl
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mp happ)

/-- **`Step_read/call`, characterised exactly.**  `CALL x` pushes the function
address and a `CALL_REF` at the function's own type.  The premise and the
conclusion read the state through two different accessors, and the
characterisation names both. -/
theorem ruleFires_call_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v callRule ↔
      ∃ z x i j mi fas fis fi ty,
        v = .tuple [ExecStep.configV z [.case "CALL" x],
          .list [.case "REF.FUNC_ADDR" (.num (.natN j)), .case "CALL_REF" ty]] ∧
        IdxIs x i ∧
        ExecNumeric.Applies env "moduleinst" [.val z] mi ∧ mi.field? "FUNCS" = some fas ∧
        fas.idx? i = some (.num (.natN j)) ∧
        ExecNumeric.Applies env "funcinst" [.val z] fis ∧ fis.idx? j = some fi ∧
        fi.field? "TYPE" = some ty := by
  unfold callRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨is, rfl, his⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 his
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hc
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨rs, rfl, hrs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r₁, r₂, τ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hrs
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 h₁
    rw [matchExp_freshVar_iff (by simp)] at hav
    subst hav
    obtain ⟨ty, rfl, hty⟩ := Validation.matchExp_case_iff.1 h₂
    rw [Validation.matchExp_sub_iff, matchExp_dotE_iff] at hty
    obtain ⟨hev, rfl⟩ := hty
    obtain ⟨fi, hfi, hfield⟩ := evalExp_dotE_iff.1 hev
    obtain ⟨fis, j, hfis, hj, hidx⟩ := evalExp_idxE_iff.1 hfi
    rw [evalExp_varE_iff] at hj
    simp only [Execution.findVal?_bindVal_lit (by decide : ("a" : IL.Id) ≠ "_")] at hj
    simp only [reduceIte, Option.some.injEq] at hj
    subst hj
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hcmp⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨c₁, c₂, hc₁, hc₂, hceq⟩ := evalExp_cmpE_iff.1 hcmp
    rw [evalExp_varE_iff] at hc₂
    simp at hc₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hceq
    subst hc₂
    obtain ⟨fas, i, hfas, hi, hidx'⟩ := evalExp_idxE_iff.1 hc₁
    obtain ⟨mi, hmi, hmfield⟩ := evalExp_dotE_iff.1 hfas
    rw [evalExp_idxProj_iff (xv := x) (by simp)] at hi
    refine ⟨z, x, i, j, mi, fas, fis, fi, ty, rfl, hi, ?_, hmfield, hidx', ?_, hidx, hfield⟩
    · exact (ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mpr
        (evalExp_callE_iff.1 hmi)
    · exact (ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mpr
        (evalExp_callE_iff.1 hfis)
  · rintro ⟨z, x, i, j, mi, fas, fis, fi, ty, rfl, hidxis, hmapp, hmfield, hmidx,
      hfapp, hfidx, hffield⟩
    refine ⟨((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)),
      ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)),
      matchExp_concl_iff.2 ⟨_, _, (VarEnv.empty.bindVal "z" z).bindVal "x" x, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            Validation.matchExp_case_iff.2 ⟨x, rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _,
          ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)), rfl,
          Validation.matchExp_case_iff.2 ⟨.num (.natN j), rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩,
          Validation.matchExp_case_iff.2 ⟨ty, rfl,
            Validation.matchExp_sub_iff.2 (matchExp_dotE_iff.2 ⟨?_, rfl⟩)⟩⟩⟩⟩, ?_⟩
    · refine evalExp_dotE_iff.2 ⟨fi, evalExp_idxE_iff.2 ⟨fis, j, ?_,
        evalExp_varE_iff.2 (by simp), hfidx⟩, hffield⟩
      exact evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mp hfapp)
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_cmpE_iff.2 ⟨.num (.natN j), .num (.natN j), ?_,
        evalExp_varE_iff.2 (by simp), ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
      refine evalExp_idxE_iff.2 ⟨fas, i, evalExp_dotE_iff.2 ⟨mi, ?_, hmfield⟩,
        (evalExp_idxProj_iff (xv := x) (by simp)).2 hidxis, hmidx⟩
      exact evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mp hmapp)

/-- **`Step_read/return_call`, characterised exactly.**  Word for word `call`,
with `RETURN_CALL_REF` in place of `CALL_REF`. -/
theorem ruleFires_returnCall_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v returnCallRule ↔
      ∃ z x i j mi fas fis fi ty,
        v = .tuple [ExecStep.configV z [.case "RETURN_CALL" x],
          .list [.case "REF.FUNC_ADDR" (.num (.natN j)), .case "RETURN_CALL_REF" ty]] ∧
        IdxIs x i ∧
        ExecNumeric.Applies env "moduleinst" [.val z] mi ∧ mi.field? "FUNCS" = some fas ∧
        fas.idx? i = some (.num (.natN j)) ∧
        ExecNumeric.Applies env "funcinst" [.val z] fis ∧ fis.idx? j = some fi ∧
        fi.field? "TYPE" = some ty := by
  unfold returnCallRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨is, rfl, his⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 his
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hc
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨rs, rfl, hrs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r₁, r₂, τ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hrs
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 h₁
    rw [matchExp_freshVar_iff (by simp)] at hav
    subst hav
    obtain ⟨ty, rfl, hty⟩ := Validation.matchExp_case_iff.1 h₂
    rw [Validation.matchExp_sub_iff, matchExp_dotE_iff] at hty
    obtain ⟨hev, rfl⟩ := hty
    obtain ⟨fi, hfi, hfield⟩ := evalExp_dotE_iff.1 hev
    obtain ⟨fis, j, hfis, hj, hidx⟩ := evalExp_idxE_iff.1 hfi
    rw [evalExp_varE_iff] at hj
    simp only [Execution.findVal?_bindVal_lit (by decide : ("a" : IL.Id) ≠ "_")] at hj
    simp only [reduceIte, Option.some.injEq] at hj
    subst hj
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hcmp⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨c₁, c₂, hc₁, hc₂, hceq⟩ := evalExp_cmpE_iff.1 hcmp
    rw [evalExp_varE_iff] at hc₂
    simp at hc₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hceq
    subst hc₂
    obtain ⟨fas, i, hfas, hi, hidx'⟩ := evalExp_idxE_iff.1 hc₁
    obtain ⟨mi, hmi, hmfield⟩ := evalExp_dotE_iff.1 hfas
    rw [evalExp_idxProj_iff (xv := x) (by simp)] at hi
    refine ⟨z, x, i, j, mi, fas, fis, fi, ty, rfl, hi, ?_, hmfield, hidx', ?_, hidx, hfield⟩
    · exact (ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mpr
        (evalExp_callE_iff.1 hmi)
    · exact (ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mpr
        (evalExp_callE_iff.1 hfis)
  · rintro ⟨z, x, i, j, mi, fas, fis, fi, ty, rfl, hidxis, hmapp, hmfield, hmidx,
      hfapp, hfidx, hffield⟩
    refine ⟨((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)),
      ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)),
      matchExp_concl_iff.2 ⟨_, _, (VarEnv.empty.bindVal "z" z).bindVal "x" x, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            Validation.matchExp_case_iff.2 ⟨x, rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _,
          ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)), rfl,
          Validation.matchExp_case_iff.2 ⟨.num (.natN j), rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩,
          Validation.matchExp_case_iff.2 ⟨ty, rfl,
            Validation.matchExp_sub_iff.2 (matchExp_dotE_iff.2 ⟨?_, rfl⟩)⟩⟩⟩⟩, ?_⟩
    · refine evalExp_dotE_iff.2 ⟨fi, evalExp_idxE_iff.2 ⟨fis, j, ?_,
        evalExp_varE_iff.2 (by simp), hfidx⟩, hffield⟩
      exact evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mp hfapp)
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_cmpE_iff.2 ⟨.num (.natN j), .num (.natN j), ?_,
        evalExp_varE_iff.2 (by simp), ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
      refine evalExp_idxE_iff.2 ⟨fas, i, evalExp_dotE_iff.2 ⟨mi, ?_, hmfield⟩,
        (evalExp_idxProj_iff (xv := x) (by simp)).2 hidxis, hmidx⟩
      exact evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
        (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "a" (.num (.natN j)))
        rfl (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mp hmapp)


/-! ## The four `br_on_cast` rules

`br_on_cast` and `br_on_cast_fail` are each given by a pair: a rule with a
`Ref_ok` premise and a rule whose only premise is `else`.  `else` is
**vacuous** in a `RelD` (`Equiv/ExecRef.lean`'s `premsHold_else_iff`), so the
two members of each pair genuinely *overlap*: the `-fail` rule fires on a
reference that does cast, too.  The characterisations say so, and
`ruleFires_brOnCastFail_onSucceeding` exhibits it. -/

/-- The conclusion's left half, shared by all four rules:
`(s; f); [ref (OP l rt_1 rt_2)]`.  The state is destructured into `s; f` but
neither half is looked inside. -/
theorem matchExp_brOnCastLhs_iff {env : Env} {ρ' : VarEnv} {op : MixopS} {v : Value} :
    MatchExp env VarEnv.empty
      (.caseE "%;%" (.tupE
        [.caseE "%;%" (.tupE [.varE "s", .varE "f"]),
         .listE [.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []),
           .caseE op (.tupE [.varE "l", .varE "rt_1", .varE "rt_2"])]]))
      v ρ' ↔
      ∃ s f r l rt₁ rt₂,
        v = .case "%;%" (.tuple [stateV s f,
          .list [r, .case op (.tuple [l, rt₁, rt₂])]]) ∧
        ρ' = (((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" r).bindVal
          "l" l).bindVal "rt_1" rt₁).bindVal "rt_2" rt₂ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨sf, iv, σ, rfl, hsf, hi⟩ := matchExps_two_iff.1 hus
    obtain ⟨sfv, rfl, hsfv⟩ := Validation.matchExp_case_iff.1 hsf
    obtain ⟨sfs, rfl, hsfs⟩ := Validation.matchExp_tup_iff.1 hsfv
    obtain ⟨s, f, τ, rfl, hs, hf⟩ := matchExps_two_iff.1 hsfs
    rw [matchExp_freshVar_iff (by simp)] at hs
    subst hs
    rw [matchExp_freshVar_iff (by simp)] at hf
    subst hf
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
    obtain ⟨r, br, υ, rfl, hr, hbr⟩ := matchExps_two_iff.1 hivs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hr
    subst hr
    obtain ⟨brv, rfl, hbrv⟩ := Validation.matchExp_case_iff.1 hbr
    obtain ⟨brvs, rfl, hbrvs⟩ := Validation.matchExp_tup_iff.1 hbrv
    obtain ⟨l, rt₁, rt₂, κ₁, κ₂, rfl, hl, hr₁, hr₂⟩ := matchExps_three_iff.1 hbrvs
    rw [matchExp_freshVar_iff (by simp)] at hl
    subst hl
    rw [matchExp_freshVar_iff (by simp)] at hr₁
    subst hr₁
    rw [matchExp_freshVar_iff (by simp)] at hr₂
    subst hr₂
    exact ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩
  · rintro ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩

/-- The scope all four rules build out of their conclusion's left half. -/
def brOnCastEnv (s f r l rt₁ rt₂ : Value) : VarEnv :=
  (((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" r).bindVal
    "l" l).bindVal "rt_1" rt₁).bindVal "rt_2" rt₂

theorem brOnCastEnv_s (s f r l rt₁ rt₂ : Value) :
    (brOnCastEnv s f r l rt₁ rt₂).findVal? "s" = some s := by simp [brOnCastEnv]

theorem brOnCastEnv_f (s f r l rt₁ rt₂ : Value) :
    (brOnCastEnv s f r l rt₁ rt₂).findVal? "f" = some f := by simp [brOnCastEnv]

theorem brOnCastEnv_ref (s f r l rt₁ rt₂ : Value) :
    (brOnCastEnv s f r l rt₁ rt₂).findVal? "ref" = some r := by simp [brOnCastEnv]

theorem brOnCastEnv_l (s f r l rt₁ rt₂ : Value) :
    (brOnCastEnv s f r l rt₁ rt₂).findVal? "l" = some l := by simp [brOnCastEnv]

theorem brOnCastEnv_rt₂ (s f r l rt₁ rt₂ : Value) :
    (brOnCastEnv s f r l rt₁ rt₂).findVal? "rt_2" = some rt₂ := by simp [brOnCastEnv]

theorem brOnCastEnv_def (s f r l rt₁ rt₂ : Value) :
    (brOnCastEnv s f r l rt₁ rt₂).findDef? "inst_reftype" = none := rfl

/-- The `Ref_ok` premise the two succeeding rules share: the reference is
well-typed at the *instantiated* target type `$inst_reftype(f.MODULE, rt_2)`.
`$inst_reftype` stays abstract. -/
theorem premsHold_refOk_iff {env : Env} {ρ ρ' : VarEnv} {s f r rt₂ : Value}
    (hs : ρ.findVal? "s" = some s) (hf : ρ.findVal? "f" = some f)
    (hr : ρ.findVal? "ref" = some r) (hrt : ρ.findVal? "rt_2" = some rt₂)
    (hd : ρ.findDef? "inst_reftype" = none) :
    PremsHold env ρ
      [.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref",
        .callE "inst_reftype"
          [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE "rt_2")]])] ρ' ↔
      ρ' = ρ ∧ ∃ mi rt, f.field? "MODULE" = some mi ∧
        ExecNumeric.Applies env "inst_reftype" [.val mi, .val rt₂] rt ∧
        Derives env "Ref_ok" "%|-%:%" [] (.tuple [s, r, rt]) := by
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨κ, hpr, hrest⟩
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨hκ, ws, u, hws, hu, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    subst hκ
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    obtain ⟨uvs, hus, rfl⟩ := evalExp_tupE_iff.1 hu
    obtain ⟨u₁, us₁, h₁, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
    obtain ⟨u₂, us₂, h₂, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
    obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
    obtain rfl := evalExps_nil_iff.1 hus₃
    rw [evalExp_varE_iff, hs] at h₁
    obtain rfl := Option.some.inj h₁
    rw [evalExp_varE_iff, hr] at h₂
    obtain rfl := Option.some.inj h₂
    obtain ⟨ws', ps, t, cs, hargs, -, -⟩ :=
      ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h₃)
    obtain ⟨miv, ws'', hmi, hws'', rfl⟩ := evalArgs_expA_cons_iff.1 hargs
    obtain ⟨rt2v, ws₃, hrt2, hws₃, rfl⟩ := evalArgs_expA_cons_iff.1 hws''
    obtain rfl := Validation.evalArgs_nil_iff.1 hws₃
    obtain ⟨fv, hfv, hfield⟩ := evalExp_dotE_iff.1 hmi
    rw [evalExp_varE_iff, hf] at hfv
    obtain rfl := Option.some.inj hfv
    rw [evalExp_varE_iff, hrt] at hrt2
    obtain rfl := Option.some.inj hrt2
    exact ⟨rfl, miv, u₃, hfield,
      (ExecNumeric.applies_iff_callDef hd hargs).mpr (evalExp_callE_iff.1 h₃), hder⟩
  · rintro ⟨rfl, mi, rt, hfield, happ, hder⟩
    refine ⟨ρ', Validation.premHolds_rule_iff.2 ⟨rfl, [], .tuple [s, r, rt],
      evalArgs_nil, ?_, hder⟩, Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_tupE_iff.2 ⟨[s, r, rt], ?_, rfl⟩
    refine evalExps_cons_iff.2 ⟨s, [r, rt], evalExp_varE_iff.2 hs, ?_, rfl⟩
    refine evalExps_cons_iff.2 ⟨r, [rt], evalExp_varE_iff.2 hr, ?_, rfl⟩
    refine evalExps_cons_iff.2 ⟨rt, [], ?_, evalExps_nil_iff.2 rfl, rfl⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef hd ?_).mp happ)
    exact evalArgs_cons (evalExp_dotE_iff.2 ⟨f, evalExp_varE_iff.2 hf, hfield⟩)
      (evalArgs_cons (evalExp_varE_iff.2 hrt) evalArgs_nil)

/-- **`Step_read/br_on_cast-succeed`, characterised exactly.** -/
theorem ruleFires_brOnCastSucceed_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnCastSucceedRule ↔
      ∃ s f r l rt₁ rt₂ mi rt,
        v = .tuple [ExecStep.configV (stateV s f)
            [r, .case "BR_ON_CAST" (.tuple [l, rt₁, rt₂])],
          .list [r, .case "BR" l]] ∧
        f.field? "MODULE" = some mi ∧
        ExecNumeric.Applies env "inst_reftype" [.val mi, .val rt₂] rt ∧
        Derives env "Ref_ok" "%|-%:%" [] (.tuple [s, r, rt]) := by
  unfold brOnCastSucceedRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩ := matchExp_brOnCastLhs_iff.1 hl
    obtain ⟨rs, rfl, hrs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r', b, υ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hrs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := r) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h₂
    rw [matchExp_boundVar_iff (w := l) (by simp)] at hlv
    obtain ⟨rfl, rfl⟩ := hlv
    rw [premsHold_refOk_iff (s := s) (f := f) (r := r') (rt₂ := rt₂)
      (by simp) (by simp) (by simp) (by simp) rfl] at hp
    obtain ⟨-, mi, rt, hfield, happ, hder⟩ := hp
    exact ⟨s, f, r', lv, rt₁, rt₂, mi, rt, rfl, hfield, happ, hder⟩
  · rintro ⟨s, f, r, l, rt₁, rt₂, mi, rt, rfl, hfield, happ, hder⟩
    refine ⟨brOnCastEnv s f r l rt₁ rt₂, brOnCastEnv s f r l rt₁ rt₂, ?_, ?_⟩
    · refine matchExp_concl_iff.2 ⟨_, _, brOnCastEnv s f r l rt₁ rt₂, rfl,
        matchExp_brOnCastLhs_iff.2 ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩, ?_⟩
      refine Validation.matchExp_list_iff.2 ⟨[r, .case "BR" l], rfl, ?_⟩
      refine matchExps_two_iff.2 ⟨r, .case "BR" l, brOnCastEnv s f r l rt₁ rt₂, rfl, ?_, ?_⟩
      · exact Validation.matchExp_sub_iff.2
          ((matchExp_boundVar_iff (brOnCastEnv_ref s f r l rt₁ rt₂)).2 ⟨rfl, rfl⟩)
      · exact Validation.matchExp_case_iff.2 ⟨l, rfl,
          (matchExp_boundVar_iff (brOnCastEnv_l s f r l rt₁ rt₂)).2 ⟨rfl, rfl⟩⟩
    · exact (premsHold_refOk_iff (brOnCastEnv_s s f r l rt₁ rt₂)
        (brOnCastEnv_f s f r l rt₁ rt₂) (brOnCastEnv_ref s f r l rt₁ rt₂)
        (brOnCastEnv_rt₂ s f r l rt₁ rt₂) (brOnCastEnv_def s f r l rt₁ rt₂)).2
        ⟨rfl, mi, rt, hfield, happ, hder⟩

/-- **`Step_read/br_on_cast_fail-succeed`, characterised exactly.**  Same
premise, opposite conclusion: the reference that *does* cast falls through. -/
theorem ruleFires_brOnCastFailSucceed_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnCastFailSucceedRule ↔
      ∃ s f r l rt₁ rt₂ mi rt,
        v = .tuple [ExecStep.configV (stateV s f)
            [r, .case "BR_ON_CAST_FAIL" (.tuple [l, rt₁, rt₂])],
          .list [r]] ∧
        f.field? "MODULE" = some mi ∧
        ExecNumeric.Applies env "inst_reftype" [.val mi, .val rt₂] rt ∧
        Derives env "Ref_ok" "%|-%:%" [] (.tuple [s, r, rt]) := by
  unfold brOnCastFailSucceedRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩ := matchExp_brOnCastLhs_iff.1 hl
    obtain ⟨rs, rfl, hrs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r', rfl, h₁⟩ := matchExps_one_iff.1 hrs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := r) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    rw [premsHold_refOk_iff (s := s) (f := f) (r := r') (rt₂ := rt₂)
      (by simp) (by simp) (by simp) (by simp) rfl] at hp
    obtain ⟨-, mi, rt, hfield, happ, hder⟩ := hp
    exact ⟨s, f, r', l, rt₁, rt₂, mi, rt, rfl, hfield, happ, hder⟩
  · rintro ⟨s, f, r, l, rt₁, rt₂, mi, rt, rfl, hfield, happ, hder⟩
    refine ⟨brOnCastEnv s f r l rt₁ rt₂, brOnCastEnv s f r l rt₁ rt₂, ?_, ?_⟩
    · refine matchExp_concl_iff.2 ⟨_, _, brOnCastEnv s f r l rt₁ rt₂, rfl,
        matchExp_brOnCastLhs_iff.2 ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩, ?_⟩
      refine Validation.matchExp_list_iff.2 ⟨[r], rfl, ?_⟩
      refine matchExps_one_iff.2 ⟨r, rfl, ?_⟩
      exact Validation.matchExp_sub_iff.2
        ((matchExp_boundVar_iff (brOnCastEnv_ref s f r l rt₁ rt₂)).2 ⟨rfl, rfl⟩)
    · exact (premsHold_refOk_iff (brOnCastEnv_s s f r l rt₁ rt₂)
        (brOnCastEnv_f s f r l rt₁ rt₂) (brOnCastEnv_ref s f r l rt₁ rt₂)
        (brOnCastEnv_rt₂ s f r l rt₁ rt₂) (brOnCastEnv_def s f r l rt₁ rt₂)).2
        ⟨rfl, mi, rt, hfield, happ, hder⟩

/-- **`Step_read/br_on_cast-fail`, characterised exactly.**  Its only premise
is `else`, which is vacuous, so it fires on **every** `BR_ON_CAST` — including
the ones `-succeed` also fires on. -/
theorem ruleFires_brOnCastFail_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnCastFailRule ↔
      ∃ s f r l rt₁ rt₂,
        v = .tuple [ExecStep.configV (stateV s f)
            [r, .case "BR_ON_CAST" (.tuple [l, rt₁, rt₂])],
          .list [r]] := by
  unfold brOnCastFailRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩ := matchExp_brOnCastLhs_iff.1 hl
    obtain ⟨rs, rfl, hrs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r', rfl, h₁⟩ := matchExps_one_iff.1 hrs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := r) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨s, f, r', l, rt₁, rt₂, rfl⟩
  · rintro ⟨s, f, r, l, rt₁, rt₂, rfl⟩
    refine ⟨brOnCastEnv s f r l rt₁ rt₂, brOnCastEnv s f r l rt₁ rt₂, ?_,
      premsHold_else_iff.2 rfl⟩
    refine matchExp_concl_iff.2 ⟨_, _, brOnCastEnv s f r l rt₁ rt₂, rfl,
      matchExp_brOnCastLhs_iff.2 ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩, ?_⟩
    refine Validation.matchExp_list_iff.2 ⟨[r], rfl, ?_⟩
    refine matchExps_one_iff.2 ⟨r, rfl, ?_⟩
    exact Validation.matchExp_sub_iff.2
      ((matchExp_boundVar_iff (brOnCastEnv_ref s f r l rt₁ rt₂)).2 ⟨rfl, rfl⟩)

/-- **`Step_read/br_on_cast_fail-fail`, characterised exactly.**  The same
vacuity, on the other instruction. -/
theorem ruleFires_brOnCastFailFail_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnCastFailFailRule ↔
      ∃ s f r l rt₁ rt₂,
        v = .tuple [ExecStep.configV (stateV s f)
            [r, .case "BR_ON_CAST_FAIL" (.tuple [l, rt₁, rt₂])],
          .list [r, .case "BR" l]] := by
  unfold brOnCastFailFailRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩ := matchExp_brOnCastLhs_iff.1 hl
    obtain ⟨rs, rfl, hrs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r', b, υ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hrs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := r) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h₂
    rw [matchExp_boundVar_iff (w := l) (by simp)] at hlv
    obtain ⟨rfl, rfl⟩ := hlv
    exact ⟨s, f, r', lv, rt₁, rt₂, rfl⟩
  · rintro ⟨s, f, r, l, rt₁, rt₂, rfl⟩
    refine ⟨brOnCastEnv s f r l rt₁ rt₂, brOnCastEnv s f r l rt₁ rt₂, ?_,
      premsHold_else_iff.2 rfl⟩
    refine matchExp_concl_iff.2 ⟨_, _, brOnCastEnv s f r l rt₁ rt₂, rfl,
      matchExp_brOnCastLhs_iff.2 ⟨s, f, r, l, rt₁, rt₂, rfl, rfl⟩, ?_⟩
    refine Validation.matchExp_list_iff.2 ⟨[r, .case "BR" l], rfl, ?_⟩
    refine matchExps_two_iff.2 ⟨r, .case "BR" l, brOnCastEnv s f r l rt₁ rt₂, rfl, ?_, ?_⟩
    · exact Validation.matchExp_sub_iff.2
        ((matchExp_boundVar_iff (brOnCastEnv_ref s f r l rt₁ rt₂)).2 ⟨rfl, rfl⟩)
    · exact Validation.matchExp_case_iff.2 ⟨l, rfl,
        (matchExp_boundVar_iff (brOnCastEnv_l s f r l rt₁ rt₂)).2 ⟨rfl, rfl⟩⟩

/-- **The overlap, exhibited.**  `br_on_cast-fail` fires on a reference the
`-succeed` rule also fires on, so `Step_read` relates one configuration to
*both* results.  This is the `else`-in-a-`RelD` finding, on this family. -/
theorem ruleFires_brOnCastFail_onSucceeding {env : Env} {s f r l rt₁ rt₂ mi rt : Value}
    (hfield : f.field? "MODULE" = some mi)
    (happ : ExecNumeric.Applies env "inst_reftype" [.val mi, .val rt₂] rt)
    (hder : Derives env "Ref_ok" "%|-%:%" [] (.tuple [s, r, rt])) :
    RuleFires env "%~>%" [] []
        (.tuple [ExecStep.configV (stateV s f)
          [r, .case "BR_ON_CAST" (.tuple [l, rt₁, rt₂])], .list [r]])
        brOnCastFailRule ∧
      RuleFires env "%~>%" [] []
        (.tuple [ExecStep.configV (stateV s f)
          [r, .case "BR_ON_CAST" (.tuple [l, rt₁, rt₂])], .list [r, .case "BR" l]])
        brOnCastSucceedRule :=
  ⟨ruleFires_brOnCastFail_iff.2 ⟨s, f, r, l, rt₁, rt₂, rfl⟩,
   ruleFires_brOnCastSucceed_iff.2 ⟨s, f, r, l, rt₁, rt₂, mi, rt, rfl, hfield, happ, hder⟩⟩

/-! ## The `throw_ref-handler-*` dispatch rules

Five more rules, which dispatch a thrown exception on the first clause of the
enclosing handler.  Their conclusions are the first in the family to
**concatenate**, and in every case the split is forced: the clause marker is a
literal list, so it has a `patLen`, and `matchExp` never searches. -/

/-- A concatenation whose left operand is a one-element literal list: it
matches exactly a non-empty list, head against the marker, tail against the
rest. -/
theorem matchExp_consMark_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value} :
    MatchExp env ρ (.catE (.listE [e₁]) e₂) v ρ' ↔
      ∃ w ws σ, v = .list (w :: ws) ∧ MatchExp env ρ e₁ w σ ∧
        MatchExp env σ e₂ (.list ws) ρ' := by
  rw [matchExp_catE_leftLen_iff (k := 1) (m := 1) (by simp [patLen])]
  constructor
  · rintro ⟨vs, σ, rfl, hle, h₁, h₂⟩
    cases vs with
    | nil => simp at hle
    | cons w ws =>
        have htake : (w :: ws).take 1 = [w] := rfl
        have hdrop : (w :: ws).drop 1 = ws := rfl
        rw [htake] at h₁
        rw [hdrop] at h₂
        obtain ⟨us, hus, hm⟩ := Validation.matchExp_list_iff.1 h₁
        obtain rfl := Value.list.inj hus
        obtain ⟨w', hw', hmw⟩ := matchExps_one_iff.1 hm
        obtain rfl : w = w' := by simpa using hw'
        exact ⟨_, ws, σ, rfl, hmw, h₂⟩
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    refine ⟨w :: ws, σ, rfl, by simp, ?_, h₂⟩
    exact Validation.matchExp_list_iff.2 ⟨[w], rfl, matchExps_one_iff.2 ⟨w, rfl, h₁⟩⟩

/-- `val* <markers>`: the markers are a literal list, so they fix the split
from the right, and the `val*` prefix is whatever is left.  Nothing requires
the prefix to consist of *values*: the body of the iteration is a subsorted
variable, and `matchExp` is transparent to subsorting — one more erasure. -/
theorem matchExp_valsMarks_iff {env : Env} {ρ ρ' : VarEnv} {x y : IL.Id} {es : List Exp}
    {v : Value} (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = none) :
    MatchExp env ρ (.catE
      (.iterE (.subE (.varE x) (.varT "val" []) (.varT "instr" []))
        (.mk .list [.mk x (.varE y)]))
      (.listE es)) v ρ' ↔
      ∃ ws us, v = .list (ws ++ us) ∧ us.length = es.length ∧
        MatchExps env (ρ.bindVal y (.list ws)) es us ρ' := by
  rw [matchExp_catE_rightLen_iff (k := es.length) (m := 1)
    (noPatLen_iterE_list (e := .subE (.varE x) (.varT "val" []) (.varT "instr" []))
      (x := x) hy) patLen_listE]
  constructor
  · rintro ⟨vs, σ, rfl, hle, h₁, h₂⟩
    rw [matchExp_iterE_list_iff (bindsVar_subVar x _ _) hx hx'] at h₁
    obtain ⟨ws, hws, hv⟩ := h₁
    obtain rfl := Value.list.inj hws
    rw [matchExp_freshVar_iff hy] at hv
    subst hv
    obtain ⟨us, hus, hm⟩ := Validation.matchExp_list_iff.1 h₂
    obtain rfl := Value.list.inj hus
    refine ⟨vs.take (vs.length - es.length), vs.drop (vs.length - es.length), ?_, ?_, hm⟩
    · rw [List.take_append_drop]
    · rw [List.length_drop]; omega
  · rintro ⟨ws, us, rfl, hlen, hm⟩
    have hl : (ws ++ us).length - es.length = ws.length := by rw [← hlen]; simp
    have h1 : (ws ++ us).take ws.length = ws := by simp
    have h2 : (ws ++ us).drop ws.length = us := by simp
    refine ⟨ws ++ us, ρ.bindVal y (.list ws), rfl, by rw [← hlen]; simp, ?_, ?_⟩
    · rw [hl, h1]
      exact (matchExp_iterE_list_iff (bindsVar_subVar x _ _) hx hx').2
        ⟨ws, rfl, (matchExp_freshVar_iff hy).2 rfl⟩
    · rw [hl, h2]
      exact Validation.matchExp_list_iff.2 ⟨us, rfl, hm⟩

/-- The left half of every `throw_ref-handler-*` conclusion:
`z; [HANDLER_n{catch*}[(REF.EXN_ADDR a) (THROW_REF)]]`, with the clause-list
pattern left as a parameter. -/
theorem matchExp_handlerLhs_iff {env : Env} {ρ' : VarEnv} {ce : Exp} {v : Value} :
    MatchExp env VarEnv.empty
      (.caseE "%;%" (.tupE
        [.varE "z",
         .listE [.caseE "HANDLER_%{%}%" (.tupE
           [.varE "n", ce,
            .listE [.caseE "REF.EXN_ADDR" (.varE "a"),
              .caseE "THROW_REF" (.tupE [])]])]])) v ρ' ↔
      ∃ z n cv tv σ,
        v = .case "%;%" (.tuple [z,
          .list [.case "HANDLER_%{%}%" (.tuple [n, cv, tv])]]) ∧
        MatchExp env ((VarEnv.empty.bindVal "z" z).bindVal "n" n) ce cv σ ∧
        MatchExp env σ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"),
          .caseE "THROW_REF" (.tupE [])]) tv ρ' := by
  rw [matchExp_config_iff (by simp)]
  constructor
  · rintro ⟨z, w, rfl, hw⟩
    obtain ⟨cs, rfl, hcs⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hcs
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨n, cval, tv, σ₁, σ, rfl, hn, hce, ht⟩ := matchExps_three_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    exact ⟨z, n, cval, tv, σ, rfl, hce, ht⟩
  · rintro ⟨z, n, cv, tv, σ, rfl, hce, ht⟩
    refine ⟨z, _, rfl, Validation.matchExp_list_iff.2 ⟨_, rfl,
      matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨n, cv, tv, _, σ, rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl, hce, ht⟩⟩⟩⟩⟩⟩

/-- **`Step_read/throw_ref-handler-catch_all`, characterised exactly.**  The
clause list is only required to *begin* with a `CATCH_ALL`; the rest is
discarded without being read. -/
theorem ruleFires_throwRefHandlerCatchAll_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefHandlerCatchAllRule ↔
      ∃ z n l cs a,
        v = .tuple [ExecStep.configV z
            [.case "HANDLER_%{%}%" (.tuple [n,
              .list (.case "CATCH_ALL" l :: cs), .list (throwExnV a)])],
          .list [.case "BR" l]] := by
  unfold throwRefHandlerCatchAllRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, n, cv, tv, σ₁, rfl, hce, ht⟩ := matchExp_handlerLhs_iff.1 hl
    obtain ⟨w, ws, σ₂, rfl, hw, hws⟩ := matchExp_consMark_iff.1 hce
    obtain ⟨l, rfl, hl'⟩ := Validation.matchExp_case_iff.1 hw
    rw [matchExp_freshVar_iff (by simp)] at hl'
    subst hl'
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)] at hws
    obtain ⟨cs, hcs, hcs'⟩ := hws
    obtain rfl := Value.list.inj hcs
    rw [matchExp_freshVar_iff (by simp)] at hcs'
    subst hcs'
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨b, rfl, hb⟩ := matchExps_one_iff.1 hbs
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hb
    rw [matchExp_boundVar_iff (w := l) (by simp)] at hlv
    obtain ⟨rfl, -⟩ := hlv
    exact ⟨z, n, _, _, a, rfl⟩
  · rintro ⟨z, n, l, cs, a, rfl⟩
    refine ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_handlerLhs_iff.2 ⟨z, n, _, _, _, rfl,
        matchExp_consMark_iff.2 ⟨_, cs, _, rfl,
          Validation.matchExp_case_iff.2 ⟨l, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩,
          (matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)).2
            ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩,
        (matchExp_throwExn_fresh (by simp)).2 ⟨a, rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨l, rfl,
            (matchExp_boundVar_iff (w := l) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/throw_ref-handler-catch_all_ref`, characterised exactly.**
The same, keeping the exception reference on the stack. -/
theorem ruleFires_throwRefHandlerCatchAllRef_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefHandlerCatchAllRefRule ↔
      ∃ z n l cs a,
        v = .tuple [ExecStep.configV z
            [.case "HANDLER_%{%}%" (.tuple [n,
              .list (.case "CATCH_ALL_REF" l :: cs), .list (throwExnV a)])],
          .list [.case "REF.EXN_ADDR" a, .case "BR" l]] := by
  unfold throwRefHandlerCatchAllRefRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, n, cv, tv, σ₁, rfl, hce, ht⟩ := matchExp_handlerLhs_iff.1 hl
    obtain ⟨w, ws, σ₂, rfl, hw, hws⟩ := matchExp_consMark_iff.1 hce
    obtain ⟨l, rfl, hl'⟩ := Validation.matchExp_case_iff.1 hw
    rw [matchExp_freshVar_iff (by simp)] at hl'
    subst hl'
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)] at hws
    obtain ⟨cs, hcs, hcs'⟩ := hws
    obtain rfl := Value.list.inj hcs
    rw [matchExp_freshVar_iff (by simp)] at hcs'
    subst hcs'
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨b₁, b₂, υ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hbs
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 h₁
    rw [matchExp_boundVar_iff (w := a) (by simp)] at hav
    obtain ⟨rfl, rfl⟩ := hav
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h₂
    rw [matchExp_boundVar_iff (w := l) (by simp)] at hlv
    obtain ⟨rfl, -⟩ := hlv
    exact ⟨z, n, _, _, _, rfl⟩
  · rintro ⟨z, n, l, cs, a, rfl⟩
    refine ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_handlerLhs_iff.2 ⟨z, n, _, _, _, rfl,
        matchExp_consMark_iff.2 ⟨_, cs, _, rfl,
          Validation.matchExp_case_iff.2 ⟨l, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩,
          (matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)).2
            ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩,
        (matchExp_throwExn_fresh (by simp)).2 ⟨a, rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨a, rfl,
            (matchExp_boundVar_iff (w := a) (by simp)).2 ⟨rfl, rfl⟩⟩,
          Validation.matchExp_case_iff.2 ⟨l, rfl,
            (matchExp_boundVar_iff (w := l) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/throw_ref-handler-next`, characterised exactly.**  The clause
it drops is matched by a bare variable, so it is an **arbitrary** value — the
rule never looks at it — and its only premise is `else`, which is vacuous.  So
`-next` fires on every non-empty handler, *including* the ones the four
dispatching rules fire on: the family overlaps. -/
theorem ruleFires_throwRefHandlerNext_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefHandlerNextRule ↔
      ∃ z n c cs a,
        v = .tuple [ExecStep.configV z
            [.case "HANDLER_%{%}%" (.tuple [n, .list (c :: cs), .list (throwExnV a)])],
          .list [.case "HANDLER_%{%}%"
            (.tuple [n, .list cs, .list (throwExnV a)])]] := by
  unfold throwRefHandlerNextRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, n, cv, tv, σ₁, rfl, hce, ht⟩ := matchExp_handlerLhs_iff.1 hl
    obtain ⟨c, ws, σ₂, rfl, hw, hws⟩ := matchExp_consMark_iff.1 hce
    rw [matchExp_freshVar_iff (by simp)] at hw
    subst hw
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)] at hws
    obtain ⟨cs, hcs, hcs'⟩ := hws
    obtain rfl := Value.list.inj hcs
    rw [matchExp_freshVar_iff (by simp)] at hcs'
    subst hcs'
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨b, rfl, hb⟩ := matchExps_one_iff.1 hbs
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨n', cs', tv', τ₁, τ₂, rfl, hn', hcs'', ht'⟩ := matchExps_three_iff.1 hbvs
    rw [matchExp_boundVar_iff (w := n) (by simp)] at hn'
    obtain ⟨rfl, rfl⟩ := hn'
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)] at hcs''
    obtain ⟨cs₂, rfl, hcs₂⟩ := hcs''
    rw [matchExp_boundVar_iff (w := Value.list ws) (by simp)] at hcs₂
    obtain ⟨heq, rfl⟩ := hcs₂
    obtain rfl := Value.list.inj heq
    rw [matchExp_throwExn_bound (a := a) (by simp)] at ht'
    obtain ⟨rfl, -⟩ := ht'
    exact ⟨z, _, c, _, a, rfl⟩
  · rintro ⟨z, n, c, cs, a, rfl⟩
    refine ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_handlerLhs_iff.2 ⟨z, n, _, _, _, rfl,
        matchExp_consMark_iff.2 ⟨c, cs, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          (matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)).2
            ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩,
        (matchExp_throwExn_fresh (by simp)).2 ⟨a, rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_three_iff.2 ⟨n, .list cs, .list (throwExnV a), _, _, rfl,
                (matchExp_boundVar_iff (w := n) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)).2
                  ⟨cs, rfl,
                    (matchExp_boundVar_iff (w := Value.list cs) (by simp)).2 ⟨rfl, rfl⟩⟩,
                (matchExp_throwExn_bound (a := a) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩


/-! ## `block`, `loop` and `try_table` cannot fire

The three block-structured instructions are the **finding** of this family.
Each has a side condition of the form

    if $blocktype_(z, bt) = t_1^m -> t_2^n

in which `t_1*` and `t_2*` occur **nowhere else in the rule** — not in the
conclusion, not in another premise.  SpecTec's algorithmic backend reads such
a premise as a destructuring assignment; the IL does not.  `IfPr`
*evaluates* its expression (`Sem/Eval.lean`'s `premHolds`, modelling
`il/eval.ml:688-693`; the IL has a separate `LetPr` for the binding form), and
an iteration over an unbound domain has no value at any fuel.  So the
right-hand side of the comparison is undefined in every scope the conclusion
can build, the premise holds in none of them, and each rule derives nothing at
all.

This is an **erasure**, not a mistake in the specification: the information
that the premise *binds* is present in the source and lost by the time the
rule is printed as IL.  It is recorded here as three theorems rather than as a
remark.  `Step_read/return_call_ref-frame-addr` has the same shape with a
`RulePr` (`Expand`) in place of the `IfPr`, and so the same consequence; it is
not proved here only because its conclusion needs the `CatE` *search*
inverted.
-/

/-- `val^m <one instruction>`, inverted: the marker is a literal one-element
list, so the split is forced from the right.  `m` binds to the length of the
prefix and `val*` to the prefix — and nothing requires the prefix to consist
of values, since `matchExp` is transparent to the `val <: instr` coercion. -/
theorem matchExp_valsNMark_iff {env : Env} {ρ ρ' : VarEnv} {ie : Exp} {v : Value}
    (hval : ρ.findVal? "val" = none) (hm : ρ.findVal? "m" = none)
    (hvs : ρ.findVal? "val*" = none) :
    MatchExp env ρ (.catE
      (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
        (.mk (.listN (.varE "m") none) [.mk "val" (.varE "val*")]))
      (.listE [ie])) v ρ' ↔
      ∃ ws iv, v = .list (ws ++ [iv]) ∧
        MatchExp env ((ρ.bindVal "m" (.num (.natN ws.length))).bindVal
          "val*" (.list ws)) ie iv ρ' := by
  rw [matchExp_catE_rightLen_iff (k := 1) (m := 1)
    (noPatLen_iterE_listN_var
      (e := .subE (.varE "val") (.varT "val" []) (.varT "instr" []))
      (x := "val") (y := "val*") hm) (by simp [patLen])]
  constructor
  · rintro ⟨vs, σ, rfl, hle, h₁, h₂⟩
    obtain ⟨ws, σ₀, hws, hcnt, hit⟩ := matchExp_iterE_listN_iff.1 h₁
    obtain rfl := Value.list.inj hws
    rw [matchExp_freshVar_iff hm] at hcnt
    subst hcnt
    rw [matchIterList_single_iff (bindsVar_subVar "val" _ _) (by simp [hval]) (by simp)] at hit
    rw [matchExp_freshVar_iff (by simp [hvs])] at hit
    subst hit
    obtain ⟨us, hus, hone⟩ := Validation.matchExp_list_iff.1 h₂
    obtain rfl := Value.list.inj hus
    obtain ⟨iv, hiv, hmiv⟩ := matchExps_one_iff.1 hone
    refine ⟨vs.take (vs.length - 1), iv, ?_, ?_⟩
    · rw [← hiv, List.take_append_drop]
    · exact hmiv
  · rintro ⟨ws, iv, rfl, hmiv⟩
    have hl : (ws ++ [iv]).length - 1 = ws.length := by simp
    have h1 : (ws ++ [iv]).take ws.length = ws := by simp
    have h2 : (ws ++ [iv]).drop ws.length = [iv] := by simp
    refine ⟨ws ++ [iv], (ρ.bindVal "m" (.num (.natN ws.length))).bindVal
      "val*" (.list ws), rfl, by simp, ?_, ?_⟩
    · rw [hl, h1]
      exact matchExp_iterE_listN_iff.2 ⟨ws, ρ.bindVal "m" (.num (.natN ws.length)), rfl,
        (matchExp_freshVar_iff hm).2 rfl,
        (matchIterList_single_iff (bindsVar_subVar "val" _ _)
          (by simp [hval]) (by simp)).2 ((matchExp_freshVar_iff (by simp [hvs])).2 rfl)⟩
    · rw [hl, h2]
      exact Validation.matchExp_list_iff.2 ⟨[iv], rfl, matchExps_one_iff.2 ⟨iv, rfl, hmiv⟩⟩

/-- `val^m instr*` with `m`, `val*` and `instr*` already bound: a test, which
extends nothing.  This is the shape the right-hand sides of `block`, `loop`
and `try_table` all carry. -/
theorem matchExp_valsNIterBound_eq {env : Env} {ρ ρ' : VarEnv} {ws is : List Value}
    {v : Value} (hval : ρ.findVal? "val" = none) (hinstr : ρ.findVal? "instr" = none)
    (hm : ρ.findVal? "m" = some (.num (.natN ws.length)))
    (hvs : ρ.findVal? "val*" = some (.list ws))
    (his : ρ.findVal? "instr*" = some (.list is))
    (h : MatchExp env ρ (.catE
      (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
        (.mk (.listN (.varE "m") none) [.mk "val" (.varE "val*")]))
      (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))) v ρ') :
    ρ' = ρ := by
  obtain ⟨vs, k, σ, rfl, h₁, h₂⟩ := matchExp_catE_dest h
  obtain ⟨ws', σ₀, hws, hcnt, hit⟩ := matchExp_iterE_listN_iff.1 h₁
  obtain rfl := Value.list.inj hws
  rw [matchExp_boundVar_iff hm] at hcnt
  obtain ⟨-, rfl⟩ := hcnt
  rw [matchIterList_single_iff (bindsVar_subVar "val" _ _) hval (by simp)] at hit
  rw [matchExp_boundVar_iff hvs] at hit
  obtain ⟨-, rfl⟩ := hit
  rw [matchExp_iterE_list_iff (bindsVar_varE "instr") hinstr (by simp)] at h₂
  obtain ⟨us, -, h₃⟩ := h₂
  rw [matchExp_boundVar_iff his] at h₃
  exact h₃.2

/-- The `$blocktype_` side condition, refuted: its right-hand side is a pair
of iterations over `t_1*` and `t_2*`, and if `t_1*` is unbound the whole
expression has no value. -/
theorem not_premsHold_blocktype {env : Env} {ρ ρ' : VarEnv} {ce : Exp}
    (ht : ρ.findVal? "t_1*" = none) :
    ¬ PremsHold env ρ
      [.ifPr (.cmpE .eqOp .boolT ce
        (.caseE "%->_%%" (.tupE
          [.caseE "%" (.tupE [.iterE (.varE "t_1")
             (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]),
           .listE [],
           .caseE "%" (.tupE [.iterE (.varE "t_2")
             (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])])))] ρ' := by
  intro hp
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hc⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨c₁, c₂, -, hc₂, -⟩ := evalExp_cmpE_iff.1 hc
  obtain ⟨cv, hcv, -⟩ := evalExp_caseE_iff.1 hc₂
  obtain ⟨cvs, hcvs, -⟩ := evalExp_tupE_iff.1 hcv
  obtain ⟨w₁, ws₁, hw₁, -, -⟩ := evalExps_cons_iff.1 hcvs
  obtain ⟨u, hu, -⟩ := evalExp_caseE_iff.1 hw₁
  obtain ⟨us, hus, -⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨t, ts, ht₁, -, -⟩ := evalExps_cons_iff.1 hus
  exact not_evalExp_iterE_of_unbound ht ht₁

/-- **`Step_read/block` fires at nothing.** -/
theorem not_ruleFires_block {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v blockRule := by
  unfold blockRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
  rw [matchExp_valsNMark_iff (by simp) (by simp) (by simp)] at hw
  obtain ⟨ws, iv, rfl, hiv⟩ := hw
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hiv
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨bt, ivv, τ, rfl, hbt, hiv'⟩ := matchExps_two_iff.1 hbvs
  rw [matchExp_freshVar_iff (by simp)] at hbt
  subst hbt
  rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hiv'
  obtain ⟨is, rfl, his⟩ := hiv'
  rw [matchExp_freshVar_iff (by simp)] at his
  subst his
  obtain ⟨ls, rfl, hls⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨lb, rfl, hlb⟩ := matchExps_one_iff.1 hls
  obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hlb
  obtain ⟨lvs, rfl, hlvs⟩ := Validation.matchExp_tup_iff.1 hlv
  obtain ⟨n, e0, cat, υ₁, υ₂, rfl, hn, he0, hcat⟩ := matchExps_three_iff.1 hlvs
  rw [matchExp_freshVar_iff (by simp)] at hn
  subst hn
  rw [matchExp_listNil_iff] at he0
  obtain ⟨rfl, rfl⟩ := he0
  obtain rfl := matchExp_valsNIterBound_eq (ws := ws) (is := is)
    (by simp) (by simp) (by simp) (by simp) (by simp) hcat
  exact not_premsHold_blocktype (by simp) hp

/-- **`Step_read/loop` fires at nothing**, for the same reason. -/
theorem not_ruleFires_loop {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v loopRule := by
  unfold loopRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
  rw [matchExp_valsNMark_iff (by simp) (by simp) (by simp)] at hw
  obtain ⟨ws, iv, rfl, hiv⟩ := hw
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hiv
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨bt, ivv, τ, rfl, hbt, hiv'⟩ := matchExps_two_iff.1 hbvs
  rw [matchExp_freshVar_iff (by simp)] at hbt
  subst hbt
  rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hiv'
  obtain ⟨is, rfl, his⟩ := hiv'
  rw [matchExp_freshVar_iff (by simp)] at his
  subst his
  obtain ⟨ls, rfl, hls⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨lb, rfl, hlb⟩ := matchExps_one_iff.1 hls
  obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hlb
  obtain ⟨lvs, rfl, hlvs⟩ := Validation.matchExp_tup_iff.1 hlv
  obtain ⟨mv, body, cat, υ₁, υ₂, rfl, hmv, hbody, hcat⟩ := matchExps_three_iff.1 hlvs
  rw [matchExp_boundVar_iff (w := Value.num (.natN ws.length)) (by simp)] at hmv
  obtain ⟨rfl, rfl⟩ := hmv
  obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hbody
  obtain ⟨b, rfl, hb⟩ := matchExps_one_iff.1 hbs
  obtain ⟨bv', rfl, hbv'⟩ := Validation.matchExp_case_iff.1 hb
  obtain ⟨bvs', rfl, hbvs'⟩ := Validation.matchExp_tup_iff.1 hbv'
  obtain ⟨bt', iv', τ', rfl, hbt', hiv''⟩ := matchExps_two_iff.1 hbvs'
  rw [matchExp_boundVar_iff (w := bt) (by simp)] at hbt'
  obtain ⟨rfl, rfl⟩ := hbt'
  rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hiv''
  obtain ⟨is', rfl, his'⟩ := hiv''
  rw [matchExp_boundVar_iff (w := Value.list is) (by simp)] at his'
  obtain ⟨-, rfl⟩ := his'
  obtain rfl := matchExp_valsNIterBound_eq (ws := ws) (is := is)
    (by simp) (by simp) (by simp) (by simp) (by simp) hcat
  exact not_premsHold_blocktype (by simp) hp

/-- **`Step_read/try_table` fires at nothing**, for the same reason. -/
theorem not_ruleFires_tryTable {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v tryTableRule := by
  unfold tryTableRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
  rw [matchExp_valsNMark_iff (by simp) (by simp) (by simp)] at hw
  obtain ⟨ws, iv, rfl, hiv⟩ := hw
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hiv
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨bt, cvv, ivv, τ₁, τ₂, rfl, hbt, hcvv, hivv⟩ := matchExps_three_iff.1 hbvs
  rw [matchExp_freshVar_iff (by simp)] at hbt
  subst hbt
  obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hcvv
  obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
  obtain ⟨cv, rfl, hcv⟩ := matchExps_one_iff.1 hcws
  rw [matchExp_iterE_list_iff (bindsVar_varE "catch") (by simp) (by simp)] at hcv
  obtain ⟨catches, rfl, hcatches⟩ := hcv
  rw [matchExp_freshVar_iff (by simp)] at hcatches
  subst hcatches
  rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hivv
  obtain ⟨is, rfl, his⟩ := hivv
  rw [matchExp_freshVar_iff (by simp)] at his
  subst his
  obtain ⟨hs, rfl, hhs⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨hb, rfl, hhb⟩ := matchExps_one_iff.1 hhs
  obtain ⟨hv, rfl, hhv⟩ := Validation.matchExp_case_iff.1 hhb
  obtain ⟨hvs, rfl, hhvs⟩ := Validation.matchExp_tup_iff.1 hhv
  obtain ⟨n, cs₂, inner, υ₁, υ₂, rfl, hn, hcs₂, hinner⟩ := matchExps_three_iff.1 hhvs
  rw [matchExp_freshVar_iff (by simp)] at hn
  subst hn
  rw [matchExp_iterE_list_iff (bindsVar_varE "catch") (by simp) (by simp)] at hcs₂
  obtain ⟨catches₂, rfl, hcatches₂⟩ := hcs₂
  rw [matchExp_boundVar_iff (w := Value.list catches) (by simp)] at hcatches₂
  obtain ⟨heq, rfl⟩ := hcatches₂
  obtain rfl := Value.list.inj heq
  obtain ⟨ls, rfl, hls⟩ := Validation.matchExp_list_iff.1 hinner
  obtain ⟨lb, rfl, hlb⟩ := matchExps_one_iff.1 hls
  obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hlb
  obtain ⟨lvs, rfl, hlvs⟩ := Validation.matchExp_tup_iff.1 hlv
  obtain ⟨n₂, e0, cat, κ₁, κ₂, rfl, hn₂, he0, hcat⟩ := matchExps_three_iff.1 hlvs
  rw [matchExp_boundVar_iff (w := n) (by simp)] at hn₂
  obtain ⟨rfl, rfl⟩ := hn₂
  rw [matchExp_listNil_iff] at he0
  obtain ⟨rfl, rfl⟩ := he0
  obtain rfl := matchExp_valsNIterBound_eq (ws := ws) (is := is)
    (by simp) (by simp) (by simp) (by simp) (by simp) hcat
  exact not_premsHold_blocktype (by simp) hp


/-- The two side conditions `throw_ref-handler-catch` and `-catch_ref` share:
the exception instance's tag is the clause's tag, and the exception's fields
are exactly the values the rule puts back on the stack.  `$exninst` and
`$tagaddr` stay abstract.

Note the **narrowing** this records: `$exninst(z)` is indexed by the value the
conclusion matched at `REF.EXN_ADDR`, and `IdxE` needs a `nat`, so the rules
fire only when that value is a bare `nat`. -/
theorem premsHold_catchTag_iff {env : Env} {ρ ρ' : VarEnv} {z xv av : Value}
    {vals : List Value}
    (hz : ρ.findVal? "z" = some z) (hx : ρ.findVal? "x" = some xv)
    (ha : ρ.findVal? "a" = some av)
    (hv : ρ.findVal? "val*" = some (.list vals))
    (hd₁ : ρ.findDef? "exninst" = none) (hd₂ : ρ.findDef? "tagaddr" = none) :
    PremsHold env ρ
      [.ifPr (.cmpE .eqOp .boolT
         (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "TAG")
         (.idxE (.callE "tagaddr" [.expA (.varE "z")])
           (.projE (.uncaseE (.varE "x") "%") 0))),
       .ifPr (.cmpE .eqOp .boolT
         (.iterE (.varE "val") (.mk .list [.mk "val" (.varE "val*")]))
         (.dotE (.idxE (.callE "exninst" [.expA (.varE "z")]) (.varE "a")) "FIELDS"))]
      ρ' ↔
      ρ' = ρ ∧ ∃ j eis ei tag i tas, av = .num (.natN j) ∧
        ExecNumeric.Applies env "exninst" [.val z] eis ∧ eis.idx? j = some ei ∧
        ei.field? "TAG" = some tag ∧
        IdxIs xv i ∧ ExecNumeric.Applies env "tagaddr" [.val z] tas ∧
        tas.idx? i = some tag ∧ ei.field? "FIELDS" = some (.list vals) := by
  have hargs : EvalArgs env ρ [.expA (.varE "z")] [.val z] :=
    evalArgs_cons (evalExp_varE_iff.2 hz) evalArgs_nil
  constructor
  · intro hp
    obtain ⟨κ, hpr₁, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain ⟨hκ₁, hc₁⟩ := Validation.premHolds_if_iff.1 hpr₁
    obtain ⟨κ₂, hpr₂, hnil⟩ := Validation.premsHold_cons_iff.1 hrest
    obtain rfl := Validation.premsHold_nil_iff.1 hnil
    obtain ⟨hκ₂, hc₂⟩ := Validation.premHolds_if_iff.1 hpr₂
    subst hκ₁
    refine ⟨hκ₂, ?_⟩
    obtain ⟨t₁, t₂, ht₁, ht₂, hcmp₁⟩ := evalExp_cmpE_iff.1 hc₁
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp₁
    obtain ⟨ei, hei, htag⟩ := evalExp_dotE_iff.1 ht₁
    obtain ⟨eis, j, heis, hj, hidxe⟩ := evalExp_idxE_iff.1 hei
    rw [evalExp_varE_iff, ha] at hj
    obtain rfl : av = .num (.natN j) := Option.some.inj hj
    obtain ⟨tas, i, htas, hi, hidxt⟩ := evalExp_idxE_iff.1 ht₂
    rw [evalExp_idxProj_iff (xv := xv) hx] at hi
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp₂⟩ := evalExp_cmpE_iff.1 hc₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp₂
    obtain rfl := EvalExp.unique hu₁ (evalExp_iterPat (by simp) hv)
    obtain ⟨ei₂, hei₂, hfields⟩ := evalExp_dotE_iff.1 hu₂
    obtain rfl := EvalExp.unique hei hei₂
    exact ⟨j, eis, ei, t₁, i, tas, rfl,
      (ExecNumeric.applies_iff_callDef hd₁ hargs).mpr (evalExp_callE_iff.1 heis),
      hidxe, htag, hi,
      (ExecNumeric.applies_iff_callDef hd₂ hargs).mpr (evalExp_callE_iff.1 htas),
      hidxt, hfields⟩
  · rintro ⟨rfl, j, eis, ei, tag, i, tas, rfl, happe, hidxe, htag, hidxis, happt,
      hidxt, hfields⟩
    have hcall : EvalExp env ρ' (.callE "exninst" [.expA (.varE "z")]) eis :=
      evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef hd₁ hargs).mp happe)
    have hidx : EvalExp env ρ' (.idxE (.callE "exninst" [.expA (.varE "z")])
        (.varE "a")) ei :=
      evalExp_idxE_iff.2 ⟨eis, j, hcall, evalExp_varE_iff.2 ha, hidxe⟩
    refine Validation.premsHold_cons_iff.2 ⟨ρ',
      Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_cons_iff.2 ⟨ρ',
        Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    · refine evalExp_cmpE_iff.2 ⟨tag, tag, evalExp_dotE_iff.2 ⟨ei, hidx, htag⟩, ?_,
        ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
      exact evalExp_idxE_iff.2 ⟨tas, i,
        evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef hd₂ hargs).mp happt),
        (evalExp_idxProj_iff (xv := xv) hx).2 hidxis, hidxt⟩
    · exact evalExp_cmpE_iff.2 ⟨.list vals, .list vals, evalExp_iterPat (by simp) hv,
        evalExp_dotE_iff.2 ⟨ei, hidx, hfields⟩,
        ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- The scope `throw_ref-handler-catch` and `-catch_ref` build. -/
def catchEnv (z n x l cs a vals : Value) : VarEnv :=
  ((((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
    "l" l).bindVal "catch'*" cs).bindVal "a" a).bindVal "val*" vals

theorem catchEnv_z (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findVal? "z" = some z := by simp [catchEnv]

theorem catchEnv_x (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findVal? "x" = some x := by simp [catchEnv]

theorem catchEnv_l (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findVal? "l" = some l := by simp [catchEnv]

theorem catchEnv_a (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findVal? "a" = some a := by simp [catchEnv]

theorem catchEnv_vals (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findVal? "val*" = some vals := by simp [catchEnv]

theorem catchEnv_exninst (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findDef? "exninst" = none := rfl

theorem catchEnv_tagaddr (z n x l cs a vals : Value) :
    (catchEnv z n x l cs a vals).findDef? "tagaddr" = none := rfl

/-- **`Step_read/throw_ref-handler-catch`, characterised exactly.**  The
handler's first clause catches the exception when their tags agree, and the
exception's fields are pushed before branching. -/
theorem ruleFires_throwRefHandlerCatch_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefHandlerCatchRule ↔
      ∃ z n x l cs j eis ei tag i tas vals,
        v = .tuple [ExecStep.configV z
            [.case "HANDLER_%{%}%" (.tuple [n,
              .list (.case "CATCH" (.tuple [x, l]) :: cs),
              .list (throwExnV (.num (.natN j)))])],
          .list (vals ++ [.case "BR" l])] ∧
        ExecNumeric.Applies env "exninst" [.val z] eis ∧ eis.idx? j = some ei ∧
        ei.field? "TAG" = some tag ∧
        IdxIs x i ∧ ExecNumeric.Applies env "tagaddr" [.val z] tas ∧
        tas.idx? i = some tag ∧ ei.field? "FIELDS" = some (.list vals) := by
  unfold throwRefHandlerCatchRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, n, cv, tv, σ₁, rfl, hce, ht⟩ := matchExp_handlerLhs_iff.1 hl
    obtain ⟨w, ws, σ₂, rfl, hw, hws⟩ := matchExp_consMark_iff.1 hce
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hw
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨x, l, τ, rfl, hx, hl'⟩ := matchExps_two_iff.1 hcws
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hl'
    subst hl'
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)] at hws
    obtain ⟨cs, hcs, hcs'⟩ := hws
    obtain rfl := Value.list.inj hcs
    rw [matchExp_freshVar_iff (by simp)] at hcs'
    subst hcs'
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    rw [matchExp_valsMarks_iff (by simp) (by simp) (by simp)] at hr
    obtain ⟨vals, us, rfl, hlen, hus⟩ := hr
    obtain ⟨b, rfl, hb⟩ := matchExps_one_iff.1 hus
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hb
    rw [matchExp_boundVar_iff (w := l) (by simp)] at hlv
    obtain ⟨rfl, rfl⟩ := hlv
    rw [premsHold_catchTag_iff (z := z) (xv := x) (av := a) (vals := vals)
      (by simp) (by simp) (by simp) (by simp) rfl rfl] at hp
    obtain ⟨-, j, eis, ei, tag, i, tas, rfl, happe, hidxe, htag, hidxis, happt,
      hidxt, hfields⟩ := hp
    exact ⟨z, n, x, _, _, j, eis, ei, tag, i, tas, vals, rfl, happe, hidxe, htag,
      hidxis, happt, hidxt, hfields⟩
  · rintro ⟨z, n, x, l, cs, j, eis, ei, tag, i, tas, vals, rfl, happe, hidxe, htag,
      hidxis, happt, hidxt, hfields⟩
    refine ⟨catchEnv z n x l (.list cs) (.num (.natN j)) (.list vals),
      catchEnv z n x l (.list cs) (.num (.natN j)) (.list vals), ?_, ?_⟩
    · refine matchExp_concl_iff.2 ⟨_, _,
        ((((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
          "l" l).bindVal "catch'*" (.list cs)).bindVal "a" (.num (.natN j))), rfl, ?_, ?_⟩
      · refine matchExp_handlerLhs_iff.2 ⟨z, n, _, _,
          (((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
            "l" l).bindVal "catch'*" (.list cs)), rfl, ?_, ?_⟩
        · refine matchExp_consMark_iff.2 ⟨_, cs,
            ((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
              "l" l), rfl, ?_, ?_⟩
          · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_two_iff.2 ⟨x, l, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
          · exact (matchExp_iterE_list_iff (bindsVar_varE "catch'")
              (by simp) (by simp)).2
              ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩
        · exact (matchExp_throwExn_fresh (by simp)).2 ⟨.num (.natN j), rfl, rfl⟩
      · refine (matchExp_valsMarks_iff (by simp) (by simp) (by simp)).2
          ⟨vals, [.case "BR" l], rfl, rfl, ?_⟩
        exact matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨l, rfl,
            (matchExp_boundVar_iff (w := l) (catchEnv_l z n x l (.list cs)
              (.num (.natN j)) (.list vals))).2 ⟨rfl, rfl⟩⟩⟩
    · exact (premsHold_catchTag_iff
        (catchEnv_z z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_x z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_a z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_vals z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_exninst z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_tagaddr z n x l (.list cs) (.num (.natN j)) (.list vals))).2
        ⟨rfl, j, eis, ei, tag, i, tas, rfl, happe, hidxe, htag, hidxis, happt,
          hidxt, hfields⟩

/-- **`Step_read/throw_ref-handler-catch_ref`, characterised exactly.**  The
same, keeping the exception reference on the stack above the fields. -/
theorem ruleFires_throwRefHandlerCatchRef_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefHandlerCatchRefRule ↔
      ∃ z n x l cs j eis ei tag i tas vals,
        v = .tuple [ExecStep.configV z
            [.case "HANDLER_%{%}%" (.tuple [n,
              .list (.case "CATCH_REF" (.tuple [x, l]) :: cs),
              .list (throwExnV (.num (.natN j)))])],
          .list (vals ++ [.case "REF.EXN_ADDR" (.num (.natN j)), .case "BR" l])] ∧
        ExecNumeric.Applies env "exninst" [.val z] eis ∧ eis.idx? j = some ei ∧
        ei.field? "TAG" = some tag ∧
        IdxIs x i ∧ ExecNumeric.Applies env "tagaddr" [.val z] tas ∧
        tas.idx? i = some tag ∧ ei.field? "FIELDS" = some (.list vals) := by
  unfold throwRefHandlerCatchRefRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, n, cv, tv, σ₁, rfl, hce, ht⟩ := matchExp_handlerLhs_iff.1 hl
    obtain ⟨w, ws, σ₂, rfl, hw, hws⟩ := matchExp_consMark_iff.1 hce
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hw
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨x, l, τ, rfl, hx, hl'⟩ := matchExps_two_iff.1 hcws
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hl'
    subst hl'
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch'") (by simp) (by simp)] at hws
    obtain ⟨cs, hcs, hcs'⟩ := hws
    obtain rfl := Value.list.inj hcs
    rw [matchExp_freshVar_iff (by simp)] at hcs'
    subst hcs'
    rw [matchExp_throwExn_fresh (by simp)] at ht
    obtain ⟨a, rfl, rfl⟩ := ht
    rw [matchExp_valsMarks_iff (by simp) (by simp) (by simp)] at hr
    obtain ⟨vals, us, rfl, hlen, hus⟩ := hr
    obtain ⟨b₁, b₂, υ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hus
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 h₁
    rw [matchExp_boundVar_iff (w := a) (by simp)] at hav
    obtain ⟨rfl, rfl⟩ := hav
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h₂
    rw [matchExp_boundVar_iff (w := l) (by simp)] at hlv
    obtain ⟨rfl, rfl⟩ := hlv
    rw [premsHold_catchTag_iff (z := z) (xv := x) (av := av) (vals := vals)
      (by simp) (by simp) (by simp) (by simp) rfl rfl] at hp
    obtain ⟨-, j, eis, ei, tag, i, tas, rfl, happe, hidxe, htag, hidxis, happt,
      hidxt, hfields⟩ := hp
    exact ⟨z, n, x, _, _, j, eis, ei, tag, i, tas, vals, rfl, happe, hidxe, htag,
      hidxis, happt, hidxt, hfields⟩
  · rintro ⟨z, n, x, l, cs, j, eis, ei, tag, i, tas, vals, rfl, happe, hidxe, htag,
      hidxis, happt, hidxt, hfields⟩
    refine ⟨catchEnv z n x l (.list cs) (.num (.natN j)) (.list vals),
      catchEnv z n x l (.list cs) (.num (.natN j)) (.list vals), ?_, ?_⟩
    · refine matchExp_concl_iff.2 ⟨_, _,
        ((((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
          "l" l).bindVal "catch'*" (.list cs)).bindVal "a" (.num (.natN j))), rfl, ?_, ?_⟩
      · refine matchExp_handlerLhs_iff.2 ⟨z, n, _, _,
          (((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
            "l" l).bindVal "catch'*" (.list cs)), rfl, ?_, ?_⟩
        · refine matchExp_consMark_iff.2 ⟨_, cs,
            ((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal "x" x).bindVal
              "l" l), rfl, ?_, ?_⟩
          · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_two_iff.2 ⟨x, l, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
          · exact (matchExp_iterE_list_iff (bindsVar_varE "catch'")
              (by simp) (by simp)).2
              ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩
        · exact (matchExp_throwExn_fresh (by simp)).2 ⟨.num (.natN j), rfl, rfl⟩
      · refine (matchExp_valsMarks_iff (by simp) (by simp) (by simp)).2
          ⟨vals, [.case "REF.EXN_ADDR" (.num (.natN j)), .case "BR" l], rfl, rfl, ?_⟩
        refine matchExps_two_iff.2 ⟨_, _,
          catchEnv z n x l (.list cs) (.num (.natN j)) (.list vals), rfl, ?_, ?_⟩
        · exact Validation.matchExp_case_iff.2 ⟨.num (.natN j), rfl,
            (matchExp_boundVar_iff (w := Value.num (.natN j))
              (catchEnv_a z n x l (.list cs) (.num (.natN j)) (.list vals))).2 ⟨rfl, rfl⟩⟩
        · exact Validation.matchExp_case_iff.2 ⟨l, rfl,
            (matchExp_boundVar_iff (w := l) (catchEnv_l z n x l (.list cs)
              (.num (.natN j)) (.list vals))).2 ⟨rfl, rfl⟩⟩
    · exact (premsHold_catchTag_iff
        (catchEnv_z z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_x z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_a z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_vals z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_exninst z n x l (.list cs) (.num (.natN j)) (.list vals))
        (catchEnv_tagaddr z n x l (.list cs) (.num (.natN j)) (.list vals))).2
        ⟨rfl, j, eis, ei, tag, i, tas, rfl, happe, hidxe, htag, hidxis, happt,
          hidxt, hfields⟩

/-! ## The five rules the `CatE` search decides

The five rules this file left open — `throw_ref-instrs`,
`return_call_ref-label`, `-handler`, `-frame-null` and `-frame-addr` — all
concatenate two patterns *neither* of which has a `patLen`: a `val*`-headed
prefix against an `instr*`-tailed suffix.  `matchExp` therefore falls through
to `Res.scan` and takes the **first** split that matches, and an exact iff has
to say which split that is.

It is **the first occurrence of the rule's marker**.  `val*` is fresh, so the
left operand matches every prefix and a split succeeds exactly when the marker
does; the search stops at the earliest position carrying it, and `val*` is
bound to everything before.  That is the opposite of `Step/ctxt-instrs`
(`Equiv/ExecStepRules.lean`'s `matchExp_ctxtInstrsLhs`), whose right operand is
a *fresh iteration* rather than a marker and so matches the empty list: there
the search stops at split `0` and the rule binds `val* = instr* = ε`.  A
literal marker is what makes the search informative, and all five of these
rules have one.

So the `val*` of these rules really is the prose rule's prefix — up to the
**erasure** already recorded above: nothing in the matcher requires those
positions to hold *values*, so `val*` is any marker-free sequence of
instructions.

The exception is `return_call_ref-frame-addr`, which cannot fire at all:
`not_ruleFires_returnCallRefFrameAddr` below completes the
`block`/`loop`/`try_table` finding.
-/

/-- **The first element of a list that satisfies `P`.**  This is the split the
`CatE` search finds, and naming it is what turns the constructions of
`Equiv/Execution.lean` into exact iffs. -/
theorem exists_first_mem {α : Type} {P : α → Prop} :
    ∀ {us : List α}, (∃ u ∈ us, P u) →
      ∃ ws u js, us = ws ++ u :: js ∧ P u ∧ ∀ w ∈ ws, ¬ P w := by
  intro us
  induction us with
  | nil => intro h; simp at h
  | cons a t ih =>
      intro h
      by_cases ha : P a
      · exact ⟨[], a, t, rfl, ha, by simp⟩
      · obtain ⟨u, hu, hpu⟩ := h
        have h' : ∃ u ∈ t, P u := by
          rcases List.mem_cons.1 hu with rfl | hu'
          · exact absurd hpu ha
          · exact ⟨u, hu', hpu⟩
        obtain ⟨ws, u', js, rfl, hpu', hws⟩ := ih h'
        refine ⟨a :: ws, u', js, rfl, hpu', fun w hw => ?_⟩
        rcases List.mem_cons.1 hw with rfl | hw'
        · exact ha
        · exact hws w hw'

/-- **A `val* M instr*` pattern matches only sequences that contain `M`.**
Whichever split the search found, the left half ends in the marker — so the
marker occurs, and `exists_first_mem` may then name the first one. -/
theorem mem_case_of_matchExp_shapeA {env : Env} {ρ ρ' : VarEnv} {x y : IL.Id}
    {op : MixopS} {me : Exp} {us : List Value} (hy : ρ.findVal? y = none)
    (h : MatchExp env ρ
      (.catE (.catE (valsPat x y) (.listE [.caseE op me])) (iterPat "instr" "instr*"))
      (.list us) ρ') :
    ∃ u ∈ us, ∃ q, u = .case op q := by
  obtain ⟨vs, k, σ, hvs, ha, -⟩ := matchExp_catE_dest h
  obtain rfl := Value.list.inj hvs
  obtain ⟨ps, τ, hps, -, -, h₂⟩ :=
    (matchExp_catE_rightLen_iff (k := 1) (m := 1) (noPatLen_valsPat hy)
      (by simp [patLen])).1 ha
  obtain rfl := Value.list.inj hps
  obtain ⟨ls, hls, hone⟩ := Validation.matchExp_list_iff.1 h₂
  obtain ⟨u, rfl, hu⟩ := matchExps_one_iff.1 hone
  obtain ⟨qq, rfl, -⟩ := Validation.matchExp_case_iff.1 hu
  refine ⟨.case op qq, ?_, qq, rfl⟩
  have h1 : (Value.case op qq) ∈ (us.take k).drop ((us.take k).length - 1) := by
    rw [Value.list.inj hls]; simp
  exact List.mem_of_mem_take (List.mem_of_mem_drop h1)

/-- **`val* M`, with `val*` and `M`'s immediate already bound, exactly.**  Now
the left operand *has* a `patLen`, so the split is forced and the pattern is a
test: this is the right-hand side the two `return_call_ref` escape rules
write. -/
theorem matchExp_valsMarkBound_iff {env : Env} {ρ ρ' : VarEnv} {x y l : IL.Id}
    {op : MixopS} {ws : List Value} {w v : Value}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_")
    (hy : ρ.findVal? y = some (.list ws)) (hl : ρ.findVal? l = some w) :
    MatchExp env ρ (.catE (valsPat x y) (.listE [.caseE op (.varE l)])) v ρ' ↔
      v = .list (ws ++ [.case op w]) ∧ ρ' = ρ := by
  obtain ⟨m, hm⟩ := patLen_valsPat_bound (env := env) hx' hy
  rw [matchExp_catE_leftLen_iff hm]
  constructor
  · rintro ⟨vs, τ, rfl, hle, h₁, h₂⟩
    rw [valsPat, matchExp_iterE_list_iff (bindsVar_subVar x _ _) hx hx'] at h₁
    obtain ⟨avs, has, h₁'⟩ := h₁
    rw [matchExp_boundVar_iff hy] at h₁'
    obtain ⟨heq, rfl⟩ := h₁'
    have htake : vs.take ws.length = ws := by
      rw [Value.list.inj has, Value.list.inj heq]
    obtain ⟨ls, hls, hone⟩ := Validation.matchExp_list_iff.1 h₂
    obtain ⟨u, rfl, hu⟩ := matchExps_one_iff.1 hone
    obtain ⟨uw, rfl, huw⟩ := Validation.matchExp_case_iff.1 hu
    rw [matchExp_boundVar_iff hl] at huw
    obtain ⟨rfl, rfl⟩ := huw
    have hdrop := Value.list.inj hls
    refine ⟨?_, rfl⟩
    conv_lhs => rw [← List.take_append_drop ws.length vs]
    rw [htake, hdrop]
  · rintro ⟨rfl, rfl⟩
    refine ⟨ws ++ [Value.case op w], ρ', rfl, by simp, ?_, ?_⟩
    · rw [show (ws ++ [Value.case op w]).take ws.length = ws by simp]
      exact matchExp_valsPat_bound hx hx' hy
    · rw [show (ws ++ [Value.case op w]).drop ws.length = [Value.case op w] by simp]
      exact Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨w, rfl, (matchExp_boundVar_iff hl).2 ⟨rfl, rfl⟩⟩⟩⟩

/-- **`Step_read/return_call_ref-label`, characterised exactly.**  A
`RETURN_CALL_REF` inside a label escapes it, carrying everything before it and
discarding the code after — and `val*` is the prefix before the **first**
`RETURN_CALL_REF`, which is the split the search picks.  The arity `k` and the
continuation `instr'*` are carried and never read. -/
theorem ruleFires_returnCallRefLabel_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v returnCallRefLabelRule ↔
      ∃ (z k : Value) (cont ws : List Value) (yy : Value) (js : List Value),
        (∀ u ∈ ws, ∀ q, u ≠ .case "RETURN_CALL_REF" q) ∧
        v = .tuple
          [ExecStep.configV z
            [.case "LABEL_%{%}%"
              (.tuple [k, .list cont, .list (ws ++ .case "RETURN_CALL_REF" yy :: js)])],
           .list (ws ++ [.case "RETURN_CALL_REF" yy])] := by
  unfold returnCallRefLabelRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨cs, rfl, hcs⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hcs
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨k, contv, bigv, τ₁, τ₂, rfl, hk, hcont, hbig⟩ := matchExps_three_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hk
    subst hk
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)] at hcont
    obtain ⟨cont, rfl, hcont'⟩ := hcont
    rw [matchExp_freshVar_iff (by simp)] at hcont'
    subst hcont'
    obtain ⟨us, rfl⟩ : ∃ us, bigv = .list us := by
      obtain ⟨us, -, -, hu, -, -⟩ := matchExp_catE_dest hbig
      exact ⟨us, hu⟩
    obtain ⟨u, hu, qq, rfl⟩ := mem_case_of_matchExp_shapeA (y := "val*") (by simp) hbig
    obtain ⟨ws, u', js, rfl, ⟨q₀, rfl⟩, hws⟩ :=
      exists_first_mem (P := fun u => ∃ p, u = Value.case "RETURN_CALL_REF" p)
        ⟨_, hu, qq, rfl⟩
    have hws' : ∀ u ∈ ws, ∀ p, u ≠ Value.case "RETURN_CALL_REF" p :=
      fun u hu' p hp => hws u hu' ⟨p, hp⟩
    have huniq : σ = _ :=
      MatchExp.unique hbig (matchExp_shapeA (x := "val") (y := "val*")
        (me := .varE "yy") (is := js) (w := Value.case "RETURN_CALL_REF" q₀)
        (by simp) (by decide) (by simp) (by simp) hws'
        (matchExp_markPat_var (l := "yy") (by simp) q₀) (by simp) (by simp))
    obtain ⟨rfl, -⟩ := (matchExp_valsMarkBound_iff (x := "val") (y := "val*") (l := "yy")
      (ws := ws) (w := q₀) (by rw [huniq]; simp) (by decide) (by rw [huniq]; simp)
      (by rw [huniq]; simp)).1 hr
    exact ⟨z, k, cont, ws, q₀, js, hws', rfl⟩
  · rintro ⟨z, k, cont, ws, yy, js, hws, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
          (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cont)
          (matchExp_shapeA (x := "val") (y := "val*") (me := .varE "yy")
            (by simp) (by decide) (by simp) (by simp) hws
            (matchExp_markPat_var (l := "yy") (by simp) yy) (by simp) (by simp))⟩,
      (matchExp_valsMarkBound_iff (x := "val") (y := "val*") (l := "yy")
        (by simp) (by decide) (by simp) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/return_call_ref-handler`, characterised exactly.**  The same,
out of an exception handler: the catch clauses are carried and never read. -/
theorem ruleFires_returnCallRefHandler_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v returnCallRefHandlerRule ↔
      ∃ (z k : Value) (cs ws : List Value) (yy : Value) (js : List Value),
        (∀ u ∈ ws, ∀ q, u ≠ .case "RETURN_CALL_REF" q) ∧
        v = .tuple
          [ExecStep.configV z
            [.case "HANDLER_%{%}%"
              (.tuple [k, .list cs, .list (ws ++ .case "RETURN_CALL_REF" yy :: js)])],
           .list (ws ++ [.case "RETURN_CALL_REF" yy])] := by
  unfold returnCallRefHandlerRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨ds, rfl, hds⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hds
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨k, csv, bigv, τ₁, τ₂, rfl, hk, hcsv, hbig⟩ := matchExps_three_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hk
    subst hk
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch") (by simp) (by simp)] at hcsv
    obtain ⟨cs, rfl, hcs'⟩ := hcsv
    rw [matchExp_freshVar_iff (by simp)] at hcs'
    subst hcs'
    obtain ⟨us, rfl⟩ : ∃ us, bigv = .list us := by
      obtain ⟨us, -, -, hu, -, -⟩ := matchExp_catE_dest hbig
      exact ⟨us, hu⟩
    obtain ⟨u, hu, qq, rfl⟩ := mem_case_of_matchExp_shapeA (y := "val*") (by simp) hbig
    obtain ⟨ws, u', js, rfl, ⟨q₀, rfl⟩, hws⟩ :=
      exists_first_mem (P := fun u => ∃ p, u = Value.case "RETURN_CALL_REF" p)
        ⟨_, hu, qq, rfl⟩
    have hws' : ∀ u ∈ ws, ∀ p, u ≠ Value.case "RETURN_CALL_REF" p :=
      fun u hu' p hp => hws u hu' ⟨p, hp⟩
    have huniq : σ = _ :=
      MatchExp.unique hbig (matchExp_shapeA (x := "val") (y := "val*")
        (me := .varE "yy") (is := js) (w := Value.case "RETURN_CALL_REF" q₀)
        (by simp) (by decide) (by simp) (by simp) hws'
        (matchExp_markPat_var (l := "yy") (by simp) q₀) (by simp) (by simp))
    obtain ⟨rfl, -⟩ := (matchExp_valsMarkBound_iff (x := "val") (y := "val*") (l := "yy")
      (ws := ws) (w := q₀) (by rw [huniq]; simp) (by decide) (by rw [huniq]; simp)
      (by rw [huniq]; simp)).1 hr
    exact ⟨z, k, cs, ws, q₀, js, hws', rfl⟩
  · rintro ⟨z, k, cs, ws, yy, js, hws, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
          (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cs)
          (matchExp_shapeA (x := "val") (y := "val*") (me := .varE "yy")
            (by simp) (by decide) (by simp) (by simp) hws
            (matchExp_markPat_var (l := "yy") (by simp) yy) (by simp) (by simp))⟩,
      (matchExp_valsMarkBound_iff (x := "val") (y := "val*") (l := "yy")
        (by simp) (by decide) (by simp) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/return_call_ref-frame-addr` fires at nothing.**  This is the
fourth instance of the `block`/`loop`/`try_table` erasure, and the one the
first pass could not reach.  The rule's only premise is

    Expand: $funcinst(z)[a].TYPE ~~ FUNC (t_1^n) -> (t_2^m)

and `t_1*`, `t_2*` and `m` occur nowhere else in it
(`scripts/spectec_unbound_vars.py Step_read`).  A `RulePr` *evaluates* the
instance it asserts, and an iteration over an unbound domain has no value, so
the premise holds in no scope the conclusion can build.

Unlike `block` and its siblings the conclusion here does match things — its
`val'* val^n (REF.FUNC_ADDR a) (RETURN_CALL_REF yy) instr*` is a `CatE`
search, and `matchExp_catE_dest` is enough to see what it binds without
deciding which split won.  The proof computes that scope exactly: every leaf
of the conclusion is a binder for `z`, `k`, `f`, `val'*`, `n`, `val*`, `a`,
`yy` and `instr*`, the right-hand side re-tests all of them and extends
nothing, and `t_1*` is in none of it. -/
theorem not_ruleFires_returnCallRefFrameAddr {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v returnCallRefFrameAddrRule := by
  unfold returnCallRefFrameAddrRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨p, q, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
  obtain ⟨fs, rfl, hfs⟩ := Validation.matchExp_list_iff.1 hw
  obtain ⟨fv, rfl, hfv⟩ := matchExps_one_iff.1 hfs
  obtain ⟨fw, rfl, hfw⟩ := Validation.matchExp_case_iff.1 hfv
  obtain ⟨fws, rfl, hfws⟩ := Validation.matchExp_tup_iff.1 hfw
  obtain ⟨k, f, bigv, τ₁, τ₂, rfl, hk, hf, hbig⟩ := matchExps_three_iff.1 hfws
  rw [matchExp_freshVar_iff (by simp)] at hk
  subst hk
  rw [matchExp_freshVar_iff (by simp)] at hf
  subst hf
  -- the body: four concatenations, each leaf a binder
  obtain ⟨us, k₁, σ₄, -, hA, hB⟩ := matchExp_catE_dest hbig
  obtain ⟨vs₃, k₂, σ₃, -, hA', hm₂⟩ := matchExp_catE_dest hA
  obtain ⟨vs₂, k₃, σ₂, -, hA'', hm₁⟩ := matchExp_catE_dest hA'
  obtain ⟨vs₁, k₄, σ₁, -, hvp, hvn⟩ := matchExp_catE_dest hA''
  rw [matchExp_iterE_list_iff (bindsVar_subVar "val'" _ _) (by simp) (by simp)] at hvp
  obtain ⟨avs, -, hvp'⟩ := hvp
  rw [matchExp_freshVar_iff (by simp)] at hvp'
  subst hvp'
  rw [matchExp_iterE_listN_iff] at hvn
  obtain ⟨bvs, σ', -, hcnt, hlist⟩ := hvn
  rw [matchExp_freshVar_iff (by simp)] at hcnt
  subst hcnt
  rw [matchIterList_single_iff (bindsVar_subVar "val" _ _) (by simp) (by simp)] at hlist
  rw [matchExp_freshVar_iff (by simp)] at hlist
  subst hlist
  obtain ⟨ls₁, -, hone₁⟩ := Validation.matchExp_list_iff.1 hm₁
  obtain ⟨av, rfl, hav⟩ := matchExps_one_iff.1 hone₁
  obtain ⟨a, rfl, ha⟩ := Validation.matchExp_case_iff.1 hav
  rw [matchExp_freshVar_iff (by simp)] at ha
  subst ha
  obtain ⟨ls₂, -, hone₂⟩ := Validation.matchExp_list_iff.1 hm₂
  obtain ⟨yv, rfl, hyv⟩ := matchExps_one_iff.1 hone₂
  obtain ⟨yy, rfl, hy⟩ := Validation.matchExp_case_iff.1 hyv
  rw [matchExp_freshVar_iff (by simp)] at hy
  subst hy
  rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hB
  obtain ⟨ivs, -, hB'⟩ := hB
  rw [matchExp_freshVar_iff (by simp)] at hB'
  subst hB'
  -- the right-hand side re-tests what the left bound, and extends nothing
  obtain ⟨rs, k₅, φ, -, hR₁, hR₂⟩ := matchExp_catE_dest hr
  rw [matchExp_iterE_listN_iff] at hR₁
  obtain ⟨cvs, φ', -, hcnt₂, hlist₂⟩ := hR₁
  rw [matchExp_boundVar_iff (w := Value.num (.natN bvs.length)) (by simp)] at hcnt₂
  obtain ⟨-, rfl⟩ := hcnt₂
  rw [matchIterList_single_iff (bindsVar_subVar "val" _ _) (by simp) (by simp)] at hlist₂
  rw [matchExp_boundVar_iff (w := Value.list bvs) (by simp)] at hlist₂
  obtain ⟨-, rfl⟩ := hlist₂
  obtain ⟨ls₃, -, htwo⟩ := Validation.matchExp_list_iff.1 hR₂
  obtain ⟨u₁, u₂, ψ, rfl, hu₁, hu₂⟩ := matchExps_two_iff.1 htwo
  obtain ⟨a', rfl, ha'⟩ := Validation.matchExp_case_iff.1 hu₁
  rw [matchExp_boundVar_iff (w := a) (by simp)] at ha'
  obtain ⟨-, rfl⟩ := ha'
  obtain ⟨y', rfl, hy'⟩ := Validation.matchExp_case_iff.1 hu₂
  rw [matchExp_boundVar_iff (w := yy) (by simp)] at hy'
  obtain ⟨-, rfl⟩ := hy'
  -- and `t_1*` is bound by none of it
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, args, pv, -, hev, -⟩ := Validation.premHolds_rule_iff.1 hpr
  obtain ⟨pvs, hpvs, -⟩ := evalExp_tupE_iff.1 hev
  obtain ⟨-, rest, -, hrest, -⟩ := evalExps_cons_iff.1 hpvs
  obtain ⟨fnv, -, hfnv, -, -⟩ := evalExps_cons_iff.1 hrest
  obtain ⟨cv, hcv, -⟩ := evalExp_caseE_iff.1 hfnv
  obtain ⟨cvs', hcvs', -⟩ := evalExp_tupE_iff.1 hcv
  obtain ⟨w₁, -, hw₁, -, -⟩ := evalExps_cons_iff.1 hcvs'
  obtain ⟨u, hu, -⟩ := evalExp_caseE_iff.1 hw₁
  obtain ⟨us', hus', -⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨t, -, ht, -, -⟩ := evalExps_cons_iff.1 hus'
  exact not_evalExp_iterE_of_unbound (y := "t_1*") (by simp) ht

/-! ### Two markers in a row

`throw_ref-instrs` separates its `val*` from its `instr*` by **two** literal
markers, `(REF.EXN_ADDR a)` and `(THROW_REF)`, and the split the search picks
is the first position carrying *both*.  `exists_first_adj` names it; the rest
of this section is the matching and definite-failure lemmas for the shape
`val* M₁ M₂ instr*`. -/

/-- A natural number satisfying `P` has a least one. -/
theorem exists_least {P : Nat → Prop} :
    ∀ (n k : Nat), k ≤ n → P k → ∃ m, P m ∧ ∀ j, j < m → ¬ P j := by
  intro n
  induction n with
  | zero =>
      intro k hk hpk
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact ⟨0, hpk, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
      intro k hk hpk
      by_cases hex : ∃ j, j < k ∧ P j
      · obtain ⟨j, hj, hpj⟩ := hex
        exact ih j (by omega) hpj
      · exact ⟨k, hpk, fun j hj hpj => hex ⟨j, hj, hpj⟩⟩

/-- **The first adjacent `P`-then-`Q` pair of a list.**  A two-marker split
succeeds exactly when the two elements there are the markers, so this names
the split the search picks. -/
theorem exists_first_adj {α : Type} {P Q : α → Prop} {us : List α}
    (h : ∃ bs c d es, us = bs ++ c :: d :: es ∧ P c ∧ Q d) :
    ∃ bs c d es, us = bs ++ c :: d :: es ∧ P c ∧ Q d ∧
      ∀ bs' c' d' es', us = bs' ++ c' :: d' :: es' → bs'.length < bs.length →
        ¬ (P c' ∧ Q d') := by
  obtain ⟨bs₀, c₀, d₀, es₀, h₀, hp₀, hq₀⟩ := h
  obtain ⟨m, ⟨bs, c, d, es, heq, hlen, hp, hq⟩, hmin⟩ :=
    exists_least
      (P := fun n => ∃ bs c d es, us = bs ++ c :: d :: es ∧ bs.length = n ∧ P c ∧ Q d)
      bs₀.length bs₀.length (Nat.le_refl _) ⟨bs₀, c₀, d₀, es₀, h₀, rfl, hp₀, hq₀⟩
  subst hlen
  exact ⟨bs, c, d, es, heq, hp, hq, fun bs' c' d' es' heq' hlt hpq =>
    hmin bs'.length hlt ⟨bs', c', d', es', heq', rfl, hpq.1, hpq.2⟩⟩

/-- **A nullary injection fails definitely on everything but itself.**
`.tupE []` matches no non-empty tuple — `matchExps` answers `undef` — and no
value that is not a tuple at all. -/
theorem matchFails_caseNilV {env : Env} {ρ : VarEnv} {op : MixopS} {w : Value}
    (h : w ≠ caseNilV op) : MatchFails env ρ (.caseE op (.tupE [])) w := by
  refine ⟨3, ?_⟩
  cases hw : w.asCase? with
  | none => simp [matchExp, hw, Res.ofOption, Bind.bind, Except.bind]
  | some pr =>
      obtain ⟨op', u⟩ := pr
      have hwe : w = .case op' u := Value.asCase?_eq_some.1 hw
      by_cases hop : op' = op
      · subst hop
        cases hut : u.asTuple? with
        | none =>
            simp [matchExp, hw, hut, Res.ofOption, Bind.bind, Except.bind, Res.assert]
        | some vs =>
            have heu : u = .tuple vs := Value.asTuple?_eq_some.1 hut
            cases vs with
            | nil => exact absurd (by rw [hwe, heu]; rfl) h
            | cons b bs =>
                simp [matchExp, hw, hut, matchExps, Res.ofOption, Bind.bind,
                  Except.bind, Res.assert]
      · simp [matchExp, hw, Res.ofOption, Bind.bind, Except.bind, Res.assert, hop]

/-- A nullary marker fails definitely on a one-element list that is not it. -/
theorem matchFails_markNil {env : Env} {ρ : VarEnv} {op : MixopS} {w : Value}
    (h : w ≠ caseNilV op) : MatchFails env ρ (.listE [.caseE op (.tupE [])]) (.list [w]) :=
  matchFails_listE_one (matchFails_caseNilV h)

/-- A one-element literal list binding an immediate, written without
`markPat` so that it matches the printed conclusions syntactically. -/
theorem matchExp_oneCaseVar {env : Env} {ρ : VarEnv} {op : MixopS} {l : IL.Id}
    (hl : ρ.findVal? l = none) (w : Value) :
    MatchExp env ρ (.listE [.caseE op (.varE l)]) (.list [.case op w]) (ρ.bindVal l w) :=
  Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
    Validation.matchExp_case_iff.2 ⟨w, rfl, (matchExp_freshVar_iff hl).2 rfl⟩⟩⟩

/-- The same for a nullary marker. -/
theorem matchExp_oneCaseNil {env : Env} {ρ : VarEnv} {op : MixopS} :
    MatchExp env ρ (.listE [.caseE op (.tupE [])]) (.list [caseNilV op]) ρ :=
  Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
    matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩

/-- …and the definite failure that goes with them. -/
theorem matchFails_oneCase {env : Env} {ρ : VarEnv} {op : MixopS} {me : Exp} {w : Value}
    (h : ∀ u, w ≠ .case op u) : MatchFails env ρ (.listE [.caseE op me]) (.list [w]) :=
  matchFails_listE_one (matchFails_caseE h)

/-- `(M₁ l) M₂ instr*` has no `patLen`: the trailing iteration has none, and
the two markers in front cannot supply one. -/
theorem noPatLen_markMarkIter {env : Env} {ρ : VarEnv} {op₁ op₂ : MixopS} {e₁ e₂ : Exp}
    (hinstrs : ρ.findVal? "instr*" = none) :
    NoPatLen env ρ (.catE (.listE [.caseE op₁ e₁])
      (.catE (.listE [.caseE op₂ e₂]) (iterPat "instr" "instr*"))) :=
  noPatLen_catE_right patLen_listE
    (noPatLen_catE_right patLen_listE (noPatLen_iterPat hinstrs))

/-- `(M₁ l) M₂ instr*`, matched.  Both markers are literal one-element lists,
so both splits are forced and nothing is searched. -/
theorem matchExp_markMarkIter {env : Env} {ρ : VarEnv} {op₁ op₂ : MixopS} {l : IL.Id}
    {p : Value} {js : List Value} (hl : ρ.findVal? l = none)
    (hi : (ρ.bindVal l p).findVal? "instr" = none)
    (his : (ρ.bindVal l p).findVal? "instr*" = none) :
    MatchExp env ρ (.catE (.listE [.caseE op₁ (.varE l)])
      (.catE (.listE [.caseE op₂ (.tupE [])]) (iterPat "instr" "instr*")))
      (.list (.case op₁ p :: caseNilV op₂ :: js))
      ((ρ.bindVal l p).bindVal "instr*" (.list js)) := by
  refine matchExp_catE_ofLeft (σ := ρ.bindVal l p) (j := 1) (m := 1)
    (by simp [patLen]) (by simp) ?_ ?_
  · simpa using matchExp_oneCaseVar (op := op₁) hl p
  · refine matchExp_catE_ofLeft (σ := ρ.bindVal l p) (j := 1) (m := 1)
      (by simp [patLen]) (by simp) ?_ ?_
    · simpa using matchExp_oneCaseNil (env := env) (ρ := ρ.bindVal l p) (op := op₂)
    · simpa using matchExp_iterPat_fresh hi (by decide) his js

/-- `(M₁ l) M₂ instr*` fails definitely on a sequence that does not begin with
the two markers — which is what makes the search pass over every earlier
split. -/
theorem matchFails_markMarkIter {env : Env} {ρ : VarEnv} {op₁ op₂ : MixopS} {l : IL.Id}
    {ls : List Value} (hl : ρ.findVal? l = none)
    (h : ∀ c d rest, ls = c :: d :: rest →
      ¬ ((∃ r, c = .case op₁ r) ∧ d = caseNilV op₂)) :
    MatchFails env ρ (.catE (.listE [.caseE op₁ (.varE l)])
      (.catE (.listE [.caseE op₂ (.tupE [])]) (iterPat "instr" "instr*"))) (.list ls) := by
  refine matchFails_catE_ofLeft (j := 1) (m := 1) (by simp [patLen]) ?_
  rcases ls with _ | ⟨c, rest⟩
  · exact Or.inl (by simp)
  · by_cases hc : ∃ r, c = Value.case op₁ r
    · obtain ⟨r, rfl⟩ := hc
      refine Or.inr (Or.inr ⟨ρ.bindVal l r, by simpa using matchExp_oneCaseVar hl r, ?_⟩)
      refine matchFails_catE_ofLeft (j := 1) (m := 1) (by simp [patLen]) ?_
      rcases rest with _ | ⟨d, rest'⟩
      · exact Or.inl (by simp)
      · refine Or.inr (Or.inl ?_)
        have hd : d ≠ caseNilV op₂ := fun hdd => h _ _ _ rfl ⟨⟨r, rfl⟩, hdd⟩
        simpa using matchFails_markNil (env := env) (ρ := ρ.bindVal l r) hd
    · refine Or.inr (Or.inl ?_)
      simpa using matchFails_oneCase (env := env) (ρ := ρ) (op := op₁) (me := .varE l)
        (w := c) (fun u hu => hc ⟨u, hu⟩)

/-- **`val* (REF.EXN_ADDR a) (THROW_REF) instr*` against
`ws (REF.EXN_ADDR a) (THROW_REF) js`.**  The search passes over every split
inside `ws`, because no two adjacent elements there are the two markers, and
stops at the first pair that is. -/
theorem matchExp_throwRefInstrsLhs {env : Env} {ρ : VarEnv} {ws js : List Value}
    {a : Value} (hval : ρ.findVal? "val" = none) (hvals : ρ.findVal? "val*" = none)
    (ha : ρ.findVal? "a" = none) (hinstr : ρ.findVal? "instr" = none)
    (hinstrs : ρ.findVal? "instr*" = none)
    (hno : ∀ bs c d es,
      ws ++ .case "REF.EXN_ADDR" a :: caseNilV "THROW_REF" :: js = bs ++ c :: d :: es →
      bs.length < ws.length →
      ¬ ((∃ r, c = .case "REF.EXN_ADDR" r) ∧ d = caseNilV "THROW_REF")) :
    MatchExp env ρ (.catE (valsPat "val" "val*")
      (.catE (.listE [.caseE "REF.EXN_ADDR" (.varE "a")])
        (.catE (.listE [.caseE "THROW_REF" (.tupE [])]) (iterPat "instr" "instr*"))))
      (.list (ws ++ .case "REF.EXN_ADDR" a :: caseNilV "THROW_REF" :: js))
      (((ρ.bindVal "val*" (.list ws)).bindVal "a" a).bindVal "instr*" (.list js)) := by
  refine matchExp_catE_ofSplit (k := ws.length) (σ := ρ.bindVal "val*" (.list ws))
    (noPatLen_valsPat hvals) (noPatLen_markMarkIter hinstrs) (by simp)
    (fun i hi => ?_) ?_ ?_
  · refine splitFails_right (matchExp_valsPat_fresh hval (by decide) hvals _) ?_
    refine matchFails_markMarkIter (by simp [ha]) (fun c d rest hcd => ?_)
    refine hno ((ws ++ .case "REF.EXN_ADDR" a :: caseNilV "THROW_REF" :: js).take i)
      c d rest ?_ ?_
    · conv_lhs =>
        rw [← List.take_append_drop i
          (ws ++ Value.case "REF.EXN_ADDR" a :: caseNilV "THROW_REF" :: js)]
      rw [hcd]
    · simp only [List.length_take, List.length_append, List.length_cons]
      omega
  · simpa using matchExp_valsPat_fresh hval (by decide) hvals ws
  · simpa using matchExp_markMarkIter (ρ := ρ.bindVal "val*" (.list ws)) (l := "a")
      (by simp [ha]) (by simp [hinstr]) (by simp [hinstrs])

/-- **The side condition `val* ≠ ε ∨ instr* ≠ ε`, exactly.**  `throw_ref-instrs`
shares it with `Step_pure/trap-instrs`: it is what stops the rule from
rewriting `(REF.EXN_ADDR a) (THROW_REF)` to itself forever. -/
theorem premsHold_neNil_iff {env : Env} {ρ ρ' : VarEnv} {ws js : List Value}
    (hvals : ρ.findVal? "val*" = some (.list ws))
    (hinstrs : ρ.findVal? "instr*" = some (.list js)) :
    PremsHold env ρ [.ifPr (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "instr" "instr*") (.listE [])))] ρ' ↔
      ρ' = ρ ∧ (ws ≠ [] ∨ js ≠ []) := by
  have hvalsE : EvalExp env ρ (iterPat "val" "val*") (.list ws) :=
    evalExp_iterPat (by decide) hvals
  have hinstrsE : EvalExp env ρ (iterPat "instr" "instr*") (.list js) :=
    evalExp_iterPat (by decide) hinstrs
  have hnil : EvalExp env ρ (.listE []) (.list []) :=
    evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨κ, hpr, hrest⟩
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨hκ, hev⟩ := Validation.premHolds_if_iff.1 hpr
    refine ⟨hκ, ?_⟩
    by_contra hcon
    have hw : ws = [] := by by_contra hc; exact hcon (Or.inl hc)
    have hj : js = [] := by by_contra hc; exact hcon (Or.inr hc)
    subst hw
    subst hj
    have hfalse : EvalExp env ρ (.binE .orOp .boolT
        (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
        (.cmpE .neOp .boolT (iterPat "instr" "instr*") (.listE []))) (.bool false) :=
      evalExp_binE_iff.2 ⟨.bool false,
        evalExp_cmpE_iff.2 ⟨.list [], .list [], hvalsE, hnil, by simp [cmpValues]⟩,
        Or.inr ⟨rfl, .bool false,
          evalExp_cmpE_iff.2 ⟨.list [], .list [], hinstrsE, hnil, by simp [cmpValues]⟩,
          by simp [binValues, boolBin]⟩⟩
    have hbad := EvalExp.unique hev hfalse
    simp at hbad
  · rintro ⟨rfl, hne⟩
    refine ⟨ρ', Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    by_cases hw : ws = []
    · subst hw
      have hj : js ≠ [] := by
        rcases hne with hc | hc
        · exact absurd rfl hc
        · exact hc
      exact evalExp_binE_iff.2 ⟨.bool false,
        evalExp_cmpE_iff.2 ⟨.list [], .list [], hvalsE, hnil, by simp [cmpValues]⟩,
        Or.inr ⟨rfl, .bool true,
          evalExp_cmpE_iff.2 ⟨.list js, .list [], hinstrsE, hnil,
            by simp [cmpValues, hj]⟩,
          by simp [binValues, boolBin]⟩⟩
    · exact evalExp_binE_iff.2 ⟨.bool true,
        evalExp_cmpE_iff.2 ⟨.list ws, .list [], hvalsE, hnil,
          by simp [cmpValues, hw]⟩, Or.inl rfl⟩

/-- **`Step_read/throw_ref-instrs`, characterised exactly.**  A thrown
exception reference discards the code around it, provided there *is* code
around it — and `val*` is the prefix before the **first** adjacent
`(REF.EXN_ADDR _) (THROW_REF)` pair, which is the split the search picks.  The
state is carried and never read. -/
theorem ruleFires_throwRefInstrs_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v throwRefInstrsRule ↔
      ∃ (z : Value) (ws : List Value) (a : Value) (js : List Value),
        (∀ bs c d es,
            ws ++ .case "REF.EXN_ADDR" a :: caseNilV "THROW_REF" :: js
              = bs ++ c :: d :: es →
            bs.length < ws.length →
            ¬ ((∃ r, c = .case "REF.EXN_ADDR" r) ∧ d = caseNilV "THROW_REF")) ∧
        (ws ≠ [] ∨ js ≠ []) ∧
        v = .tuple
          [ExecStep.configV z
            (ws ++ .case "REF.EXN_ADDR" a :: caseNilV "THROW_REF" :: js),
           .list (throwExnV a)] := by
  unfold throwRefInstrsRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨pv, qv, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨us, k, τ, rfl, -, hR⟩ := matchExp_catE_dest hw
    -- whatever split the search found, the two markers sit at it
    obtain ⟨ls, υ, hls, -, hM₁, hrest⟩ :=
      (matchExp_catE_leftLen_iff (k := 1) (m := 1) (by simp [patLen])).1 hR
    obtain ⟨xs, hxs, hone⟩ := Validation.matchExp_list_iff.1 hM₁
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hone
    obtain ⟨aa, rfl, -⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨tl₁, rfl⟩ : ∃ t, ls = Value.case "REF.EXN_ADDR" aa :: t := by
      refine ⟨ls.drop 1, ?_⟩
      conv_lhs => rw [← List.take_append_drop 1 ls]
      rw [Value.list.inj hxs]
      rfl
    obtain ⟨ls₂, υ₂, hls₂, -, hM₂, -⟩ :=
      (matchExp_catE_leftLen_iff (k := 1) (m := 1) (by simp [patLen])).1 hrest
    obtain rfl : tl₁ = ls₂ := Value.list.inj hls₂
    obtain ⟨ys, hys, hone₂⟩ := Validation.matchExp_list_iff.1 hM₂
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hone₂
    obtain ⟨rfl, -⟩ := matchExp_caseNil_iff.1 hd
    obtain ⟨tl₂, rfl⟩ : ∃ t, tl₁ = caseNilV "THROW_REF" :: t := by
      refine ⟨tl₁.drop 1, ?_⟩
      conv_lhs => rw [← List.take_append_drop 1 tl₁]
      rw [Value.list.inj hys]
      rfl
    have hdk : us.drop k =
        Value.case "REF.EXN_ADDR" aa :: caseNilV "THROW_REF" :: tl₂ := Value.list.inj hls
    have hus : us = us.take k ++ Value.case "REF.EXN_ADDR" aa ::
        caseNilV "THROW_REF" :: tl₂ := by
      conv_lhs => rw [← List.take_append_drop k us]
      rw [hdk]
    -- and so they sit at a *first* one
    obtain ⟨ws, c₀, d₀, js, rfl, ⟨r₀, rfl⟩, rfl, hno⟩ :=
      exists_first_adj (P := fun c => ∃ r, c = Value.case "REF.EXN_ADDR" r)
        (Q := fun d => d = caseNilV "THROW_REF")
        ⟨us.take k, _, _, _, hus, ⟨aa, rfl⟩, rfl⟩
    have huniq : σ = _ :=
      MatchExp.unique hw (matchExp_throwRefInstrsLhs (a := r₀) (js := js)
        (by simp) (by simp) (by simp) (by simp) (by simp) hno)
    obtain ⟨rfl, hρ₁⟩ := (matchExp_throwExn_bound (a := r₀) (by rw [huniq]; simp)).1 hr
    obtain ⟨-, hne⟩ := (premsHold_neNil_iff (ws := ws) (js := js)
      (by rw [hρ₁, huniq]; simp) (by rw [hρ₁, huniq]; simp)).1 hp
    exact ⟨z, ws, r₀, js, hno, hne, rfl⟩
  · rintro ⟨z, ws, a, js, hno, hne, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        matchExp_throwRefInstrsLhs (by simp) (by simp) (by simp) (by simp) (by simp)
          hno⟩,
      (matchExp_throwExn_bound (a := a) (by simp)).2 ⟨rfl, rfl⟩⟩,
      (premsHold_neNil_iff (ws := ws) (js := js) (by simp) (by simp)).2 ⟨rfl, hne⟩⟩

/-! ### Two markers at the end of the prefix

`return_call_ref-frame-null` parenthesises its two markers the other way:
`val* (REF.NULL_ADDR) (RETURN_CALL_REF yy)` is the **left** operand of the
outer concatenation, so each marker's split is forced from the right rather
than from the left.  The answer is the same — the search stops at the first
adjacent `(REF.NULL_ADDR) (RETURN_CALL_REF _)` pair — but the lemmas are
not. -/

/-- The last element of a list, as an append. -/
theorem eq_append_last {l : List Value} {w : Value}
    (h : l.drop (l.length - 1) = [w]) : l = l.take (l.length - 1) ++ [w] := by
  conv_lhs => rw [← List.take_append_drop (l.length - 1) l]
  rw [h]

/-- `val* M₁ M₂` is too long for a sequence of fewer than two elements. -/
theorem matchFails_valsMarkMark_short {env : Env} {ρ : VarEnv} {op₁ op₂ : MixopS}
    {me₂ : Exp} {ls : List Value} (hvals : ρ.findVal? "val*" = none)
    (h : ls.length < 2) :
    MatchFails env ρ (.catE (.catE (valsPat "val" "val*")
      (.listE [.caseE op₁ (.tupE [])])) (.listE [.caseE op₂ me₂])) (.list ls) := by
  refine matchFails_catE_ofRight (j := 1) (m := 1)
    (noPatLen_catE_left (noPatLen_valsPat hvals)) (by simp [patLen]) ?_
  rcases ls with _ | ⟨c, rest⟩
  · exact Or.inl (by simp)
  · rcases rest with _ | ⟨d, rest'⟩
    · exact Or.inr (Or.inl (matchFails_catE_ofRight (j := 1) (m := 1)
        (noPatLen_valsPat hvals) (by simp [patLen]) (Or.inl (by simp))))
    · exfalso
      simp only [List.length_cons] at h
      omega

/-- **`val* M₁ M₂` fails definitely on a prefix whose last two elements are not
the two markers** — which is what lets the search pass over every earlier
split. -/
theorem matchFails_valsMarkMark {env : Env} {ρ : VarEnv} {op₁ op₂ : MixopS}
    {l : IL.Id} {pre : List Value} {c d : Value}
    (hval : ρ.findVal? "val" = none) (hvals : ρ.findVal? "val*" = none)
    (h : ¬ (c = caseNilV op₁ ∧ ∃ r, d = .case op₂ r)) :
    MatchFails env ρ (.catE (.catE (valsPat "val" "val*")
      (.listE [.caseE op₁ (.tupE [])])) (.listE [.caseE op₂ (.varE l)]))
      (.list (pre ++ [c, d])) := by
  have e1 : (pre ++ [c, d]).length - 1 = pre.length + 1 := by simp
  have e2 : (pre ++ [c, d]).take (pre.length + 1) = pre ++ [c] := by
    simp [List.take_append]
  have e3 : (pre ++ [c, d]).drop (pre.length + 1) = [d] := by simp
  have f1 : (pre ++ [c]).length - 1 = pre.length := by simp
  have f2 : (pre ++ [c]).take pre.length = pre := by simp
  have f3 : (pre ++ [c]).drop pre.length = [c] := by simp
  refine matchFails_catE_ofRight (j := 1) (m := 1)
    (noPatLen_catE_left (noPatLen_valsPat hvals)) (by simp [patLen]) ?_
  rw [e1, e2, e3]
  by_cases hc : c = caseNilV op₁
  · subst hc
    refine Or.inr (Or.inr ⟨ρ.bindVal "val*" (.list pre), ?_, ?_⟩)
    · refine matchExp_catE_ofRight (j := 1) (m := 1)
        (σ := ρ.bindVal "val*" (.list pre)) (noPatLen_valsPat hvals)
        (by simp [patLen]) (by simp) ?_ ?_
      · rw [f1, f2]
        exact matchExp_valsPat_fresh hval (by decide) hvals pre
      · rw [f1, f3]
        exact matchExp_oneCaseNil
    · exact matchFails_oneCase (fun u hu => h ⟨rfl, u, hu⟩)
  · refine Or.inr (Or.inl ?_)
    refine matchFails_catE_ofRight (j := 1) (m := 1) (noPatLen_valsPat hvals)
      (by simp [patLen]) (Or.inr (Or.inr ⟨ρ.bindVal "val*" (.list pre), ?_, ?_⟩))
    · rw [f1, f2]
      exact matchExp_valsPat_fresh hval (by decide) hvals pre
    · rw [f1, f3]
      exact matchFails_markNil hc

/-- **`val* (REF.NULL_ADDR) (RETURN_CALL_REF yy) instr*` against
`ws (REF.NULL_ADDR) (RETURN_CALL_REF yy) js`.**  The search passes over every
split inside `ws` and stops at the first adjacent pair of markers. -/
theorem matchExp_returnCallRefFrameNullLhs {env : Env} {ρ : VarEnv}
    {ws js : List Value} {yy : Value}
    (hval : ρ.findVal? "val" = none) (hvals : ρ.findVal? "val*" = none)
    (hyy : ρ.findVal? "yy" = none) (hinstr : ρ.findVal? "instr" = none)
    (hinstrs : ρ.findVal? "instr*" = none)
    (hno : ∀ bs c d es,
      ws ++ caseNilV "REF.NULL_ADDR" :: Value.case "RETURN_CALL_REF" yy :: js
        = bs ++ c :: d :: es → bs.length < ws.length →
      ¬ (c = caseNilV "REF.NULL_ADDR" ∧ ∃ r, d = Value.case "RETURN_CALL_REF" r)) :
    MatchExp env ρ
      (.catE (.catE (.catE (valsPat "val" "val*")
          (.listE [.caseE "REF.NULL_ADDR" (.tupE [])]))
        (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")]))
        (iterPat "instr" "instr*"))
      (.list (ws ++ caseNilV "REF.NULL_ADDR" :: Value.case "RETURN_CALL_REF" yy :: js))
      (((ρ.bindVal "val*" (.list ws)).bindVal "yy" yy).bindVal "instr*" (.list js)) := by
  have g1 : (ws ++ caseNilV "REF.NULL_ADDR" ::
      Value.case "RETURN_CALL_REF" yy :: js).take (ws.length + 2)
      = ws ++ [caseNilV "REF.NULL_ADDR", Value.case "RETURN_CALL_REF" yy] := by
    simp [List.take_append]
  have g2 : (ws ++ caseNilV "REF.NULL_ADDR" ::
      Value.case "RETURN_CALL_REF" yy :: js).drop (ws.length + 2) = js := by simp
  have h1 : (ws ++ [caseNilV "REF.NULL_ADDR", Value.case "RETURN_CALL_REF" yy]).length - 1
      = ws.length + 1 := by simp
  have h2 : (ws ++ [caseNilV "REF.NULL_ADDR", Value.case "RETURN_CALL_REF" yy]).take
      (ws.length + 1) = ws ++ [caseNilV "REF.NULL_ADDR"] := by
    simp [List.take_append]
  have h3 : (ws ++ [caseNilV "REF.NULL_ADDR", Value.case "RETURN_CALL_REF" yy]).drop
      (ws.length + 1) = [Value.case "RETURN_CALL_REF" yy] := by simp
  have k1 : (ws ++ [caseNilV "REF.NULL_ADDR"]).length - 1 = ws.length := by simp
  have k2 : (ws ++ [caseNilV "REF.NULL_ADDR"]).take ws.length = ws := by simp
  have k3 : (ws ++ [caseNilV "REF.NULL_ADDR"]).drop ws.length
      = [caseNilV "REF.NULL_ADDR"] := by simp
  refine matchExp_catE_ofSplit (k := ws.length + 2)
    (σ := (ρ.bindVal "val*" (.list ws)).bindVal "yy" yy)
    (noPatLen_catE_left (noPatLen_catE_left (noPatLen_valsPat hvals)))
    (noPatLen_iterPat hinstrs)
    (by simp only [List.length_append, List.length_cons]; omega) (fun i hi => ?_) ?_ ?_
  · refine splitFails_left ?_
    by_cases hi2 : i < 2
    · refine matchFails_valsMarkMark_short hvals ?_
      simp only [List.length_take, List.length_append, List.length_cons]
      omega
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
      obtain ⟨c, d, es, hdrop⟩ : ∃ c d es,
          (ws ++ caseNilV "REF.NULL_ADDR" ::
            Value.case "RETURN_CALL_REF" yy :: js).drop m = c :: d :: es := by
        rcases hcases : (ws ++ caseNilV "REF.NULL_ADDR" ::
            Value.case "RETURN_CALL_REF" yy :: js).drop m with _ | ⟨c, _ | ⟨d, es⟩⟩
        · exfalso
          have hlen := congrArg List.length hcases
          simp only [List.length_drop, List.length_nil, List.length_append,
            List.length_cons] at hlen
          omega
        · exfalso
          have hlen := congrArg List.length hcases
          simp only [List.length_drop, List.length_cons, List.length_nil,
            List.length_append] at hlen
          omega
        · exact ⟨c, d, es, rfl⟩
      obtain ⟨pre, hpre, hsplit⟩ : ∃ pre, pre.length = m ∧
          ws ++ caseNilV "REF.NULL_ADDR" :: Value.case "RETURN_CALL_REF" yy :: js
            = pre ++ c :: d :: es := by
        refine ⟨(ws ++ caseNilV "REF.NULL_ADDR" ::
          Value.case "RETURN_CALL_REF" yy :: js).take m, ?_, ?_⟩
        · simp only [List.length_take, List.length_append, List.length_cons]
          omega
        · conv_lhs => rw [← List.take_append_drop m (ws ++ caseNilV "REF.NULL_ADDR" ::
            Value.case "RETURN_CALL_REF" yy :: js)]
          rw [hdrop]
      have htake : (ws ++ caseNilV "REF.NULL_ADDR" ::
          Value.case "RETURN_CALL_REF" yy :: js).take (m + 2) = pre ++ [c, d] := by
        rw [hsplit, ← hpre]
        simp [List.take_append]
      rw [htake]
      exact matchFails_valsMarkMark hval hvals (hno pre c d es hsplit (by omega))
  · rw [g1]
    refine matchExp_catE_ofRight (j := 1) (m := 1)
      (σ := ρ.bindVal "val*" (.list ws))
      (noPatLen_catE_left (noPatLen_valsPat hvals)) (by simp [patLen]) (by simp) ?_ ?_
    · rw [h1, h2]
      refine matchExp_catE_ofRight (j := 1) (m := 1)
        (σ := ρ.bindVal "val*" (.list ws)) (noPatLen_valsPat hvals)
        (by simp [patLen]) (by simp) ?_ ?_
      · rw [k1, k2]
        exact matchExp_valsPat_fresh hval (by decide) hvals ws
      · rw [k1, k3]
        exact matchExp_oneCaseNil
    · rw [h1, h3]
      exact matchExp_oneCaseVar (op := "RETURN_CALL_REF") (l := "yy") (by simp [hyy]) yy
  · rw [g2]
    exact matchExp_iterPat_fresh (by simp [hinstr]) (by decide) (by simp [hinstrs]) js

/-- **`Step_read/return_call_ref-frame-null`, characterised exactly.**  A
`RETURN_CALL_REF` on a null reference inside a frame traps, and the pair the
rule reads is the **first** adjacent `(REF.NULL_ADDR) (RETURN_CALL_REF _)` in
the frame's body — the split the search picks.  The arity `k` and the frame
`f` are carried and never read, and the result does not depend on the split,
so this is the one rule of the five whose iff needs no uniqueness argument. -/
theorem ruleFires_returnCallRefFrameNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v returnCallRefFrameNullRule ↔
      ∃ (z k f : Value) (ws : List Value) (yy : Value) (js : List Value),
        (∀ bs c d es,
            ws ++ caseNilV "REF.NULL_ADDR" :: Value.case "RETURN_CALL_REF" yy :: js
              = bs ++ c :: d :: es → bs.length < ws.length →
            ¬ (c = caseNilV "REF.NULL_ADDR" ∧
              ∃ r, d = Value.case "RETURN_CALL_REF" r)) ∧
        v = .tuple
          [ExecStep.configV z
            [.case "FRAME_%{%}%" (.tuple [k, f,
              .list (ws ++ caseNilV "REF.NULL_ADDR" ::
                Value.case "RETURN_CALL_REF" yy :: js)])],
           .list [caseNilV "TRAP"]] := by
  unfold returnCallRefFrameNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨pv, qv, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, w, rfl, hw⟩ := (matchExp_config_iff (by simp)).1 hl
    obtain ⟨fs, rfl, hfs⟩ := Validation.matchExp_list_iff.1 hw
    obtain ⟨fv, rfl, hfv⟩ := matchExps_one_iff.1 hfs
    obtain ⟨fw, rfl, hfw⟩ := Validation.matchExp_case_iff.1 hfv
    obtain ⟨fws, rfl, hfws⟩ := Validation.matchExp_tup_iff.1 hfw
    obtain ⟨k, f, bigv, τ₁, τ₂, rfl, hk, hf, hbig⟩ := matchExps_three_iff.1 hfws
    rw [matchExp_freshVar_iff (by simp)] at hk
    subst hk
    rw [matchExp_freshVar_iff (by simp)] at hf
    subst hf
    -- the right-hand side is a bare `TRAP`, independent of the split
    obtain ⟨ts, rfl, hts⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨tv, rfl, htv⟩ := matchExps_one_iff.1 hts
    obtain ⟨rfl, -⟩ := matchExp_caseNil_iff.1 htv
    -- whatever split the search found, the two markers end its prefix
    obtain ⟨us, k₁, σ₄, rfl, hLEFT, -⟩ := matchExp_catE_dest hbig
    obtain ⟨t, υ, ht, -, hinner, hM₂⟩ :=
      (matchExp_catE_rightLen_iff (k := 1) (m := 1)
        (noPatLen_catE_left (noPatLen_valsPat (by simp))) (by simp [patLen])).1 hLEFT
    obtain rfl := Value.list.inj ht
    obtain ⟨ys, hys, hone₂⟩ := Validation.matchExp_list_iff.1 hM₂
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hone₂
    obtain ⟨yy, rfl, -⟩ := Validation.matchExp_case_iff.1 hd
    obtain ⟨T', hT'eq, hT⟩ : ∃ T', T' = (us.take k₁).take ((us.take k₁).length - 1) ∧
        us.take k₁ = T' ++ [Value.case "RETURN_CALL_REF" yy] :=
      ⟨_, rfl, eq_append_last (Value.list.inj hys)⟩
    rw [← hT'eq] at hinner
    obtain ⟨t', υ', ht', -, -, hM₁⟩ :=
      (matchExp_catE_rightLen_iff (k := 1) (m := 1) (noPatLen_valsPat (by simp))
        (by simp [patLen])).1 hinner
    obtain rfl := Value.list.inj ht'
    obtain ⟨xs, hxs, hone₁⟩ := Validation.matchExp_list_iff.1 hM₁
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hone₁
    obtain ⟨rfl, -⟩ := matchExp_caseNil_iff.1 hc
    obtain ⟨pre, -, hpre⟩ : ∃ pre, pre = T'.take (T'.length - 1) ∧
        T' = pre ++ [caseNilV "REF.NULL_ADDR"] :=
      ⟨_, rfl, eq_append_last (Value.list.inj hxs)⟩
    have husplit : us = pre ++ caseNilV "REF.NULL_ADDR" ::
        Value.case "RETURN_CALL_REF" yy :: us.drop k₁ := by
      conv_lhs => rw [← List.take_append_drop k₁ us]
      rw [hT, hpre]
      simp
    -- and so they end a *first* one
    obtain ⟨ws, c₀, d₀, js, rfl, rfl, ⟨r₀, rfl⟩, hno⟩ :=
      exists_first_adj (P := fun c => c = caseNilV "REF.NULL_ADDR")
        (Q := fun d => ∃ r, d = Value.case "RETURN_CALL_REF" r)
        ⟨pre, _, _, _, husplit, rfl, ⟨yy, rfl⟩⟩
    exact ⟨z, k, f, ws, r₀, js, hno, rfl⟩
  · rintro ⟨z, k, f, ws, yy, js, hno, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      (matchExp_config_iff (by simp)).2 ⟨z, _, rfl,
        matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
          ((matchExp_freshVar_iff (by simp)).2 rfl)
          (matchExp_returnCallRefFrameNullLhs (by simp) (by simp) (by simp) (by simp)
            (by simp) hno)⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

end Silmaril.SpecTec.Equiv.ExecReadControl
