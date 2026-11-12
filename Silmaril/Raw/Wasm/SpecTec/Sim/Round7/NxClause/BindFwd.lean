module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Script

/-!
# Round 8, REH route 2: part (b) forward — every `if` premise of a rule instance survives erasure
(unrefined)

`ifPr_fwd`: in a rule instance of a reachable relation, every top-level `if` premise that holds
holds on the erased scope, the six binding sites included. Away from the binding sites this is
round 7's `NxErase.erase_ifPr`. At a binding site `if e₁ = e₂` or `if e₁ <- e₂`, each operand
commutes with erasure separately (`NxErase.erase_closed`; the site check gives both operands
`badE … = 0`), and equality and membership are preserved by any function, injective or not. So
part (b) needs no recomputation forward; only the backward direction does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT CallE erase_closed erase_ifPr ruleX ruleX_at premX
  auxX)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)

theorem varsIn_union {K : List IL.Id} {s₁ s₂ : Sets} (h : varsIn K (s₁.union s₂) = true) :
    varsIn K s₁ = true ∧ varsIn K s₂ = true := by
  simp only [varsIn, decide_eq_true_eq] at h ⊢
  exact ⟨fun x hx => h x (by simp [Sets.union, hx]), fun x hx => h x (by simp [Sets.union, hx])⟩

theorem beq_value_true {a b : Value} (h : (a == b) = true) : a = b := by
  simpa using h

theorem list_contains_map {ws : List Value} {a : Value} (h : ws.contains a = true) :
    (ws.map eraseV).contains (eraseV a) = true := by
  simp only [List.contains_iff_mem, List.mem_map] at h ⊢
  exact ⟨a, h, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **Every top-level `if` premise of a rule instance that holds, holds on the erased scope**,
binding sites included, given that clause bodies commute with erasure in the instance's
quantifier scope. -/
theorem ifPr_fwd {B : Builtins} {gr gd : String → Bool}
    (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m) (H : BIErase QT gd (utf8Env B))
    {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : reach 0 x = true) (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
    (hCE : ∀ k, CallE gd sigX tsigFixed ctx0 (utf8Env B) (qScope qs (VarEnv.empty.bindVals σ)) k)
    {c : Exp} (hpr : Prem.ifPr c ∈ prems) (hxc : xExp gr gd c = true)
    (h : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) c (.bool true)) :
    EvalExp (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) c (.bool true) := by
  obtain ⟨n, hn⟩ := h
  cases hbs : bindSite sigX (quantsΓ qs) (.ifPr c) with
  | false =>
    refine ⟨n, ?_⟩
    rw [erase_ifPr hD H hx hrel hrule hq hCE hpr hbs hxc n, hn]
    rfl
  | true =>
    have hF := rFacts hx hrel hrule
    obtain ⟨ht, ha, hc⟩ := hF.premsOk _ hpr
    have hX := ruleX_at hx hrel (List.mem_of_getElem? hrule)
    simp only [ruleX, Bool.and_eq_true, List.all_eq_true] at hX
    have hXc := hX.2 _ hpr
    simp only [premX] at hXc
    simp only [premTy] at ht
    simp only [premAuxR] at ha
    simp only [freePrem] at hc
    -- the operands
    have hop : ∀ {e₁ e₂ : Exp}, tyOk sigX tsigFixed (quantsΓ qs) e₁ = true →
        tyOk sigX tsigFixed (quantsΓ qs) e₂ = true → auxE ctx0 e₁ = true → auxE ctx0 e₂ = true →
        auxX ctx0 e₁ = true → auxX ctx0 e₂ = true →
        badE sigX (quantsΓ qs) e₁ = 0 → badE sigX (quantsΓ qs) e₂ = 0 →
        varsIn (Determ.quantNames qs) ((freeExp e₁).union (freeExp e₂)) = true →
        xExp gr gd e₁ = true → xExp gr gd e₂ = true → ∀ m,
        (evalExp m (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e₁ =
          eraseV <$> evalExp m (utf8Env B) (VarEnv.empty.bindVals σ) e₁) ∧
        (evalExp m (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e₂ =
          eraseV <$> evalExp m (utf8Env B) (VarEnv.empty.bindVals σ) e₂) := by
      intro e₁ e₂ ht₁ ht₂ ha₁ ha₂ hX₁ hX₂ hb₁ hb₂ hc₁₂ hx₁ hx₂ m
      obtain ⟨hc₁, hc₂⟩ := varsIn_union hc₁₂
      exact ⟨erase_closed hD H hq hF.wild hCE hc₁ ht₁ ha₁ hX₁ hb₁ hx₁ m,
        erase_closed hD H hq hF.wild hCE hc₂ ht₂ ha₂ hX₂ hb₂ hx₂ m⟩
    cases c with
    | cmpE cop ty e₁ e₂ =>
      cases cop with
      | eqOp =>
        simp only [bindSite, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
          Nat.add_eq_zero_iff] at hbs
        simp only [tyOk, Bool.and_eq_true] at ht
        simp only [auxE, Bool.and_eq_true] at ha
        simp only [auxX, Bool.and_eq_true] at hXc
        simp only [freeExp] at hc
        simp only [xExp, Bool.and_eq_true] at hxc
        cases n with
        | zero => simp [evalExp] at hn
        | succ m =>
          obtain ⟨h₁, h₂⟩ := hop ht.1 ht.2 ha.1 ha.2 hXc.1 hXc.2 hbs.2.1 hbs.2.2 hc hxc.1 hxc.2 m
          simp only [evalExp] at hn ⊢
          cases ha₁ : evalExp m (utf8Env B) (VarEnv.empty.bindVals σ) e₁ with
          | error => rw [ha₁] at hn; cases hn
          | ok a =>
            cases hb₁ : evalExp m (utf8Env B) (VarEnv.empty.bindVals σ) e₂ with
            | error => rw [ha₁, hb₁] at hn; cases hn
            | ok b =>
              rw [ha₁, hb₁] at hn
              simp only [bind, Except.bind, cmpValues, Except.ok.injEq, Value.bool.injEq] at hn
              have hab := beq_value_true hn
              subst hab
              refine ⟨m + 1, ?_⟩
              simp only [evalExp, h₁, h₂, ha₁, hb₁]
              simp [Functor.map, Except.map, bind, Except.bind, cmpValues]
      | _ => simp [bindSite] at hbs
    | memE e₁ e₂ =>
      simp only [bindSite, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
        Nat.add_eq_zero_iff] at hbs
      simp only [tyOk, Bool.and_eq_true] at ht
      simp only [auxE, Bool.and_eq_true] at ha
      simp only [auxX, Bool.and_eq_true] at hXc
      simp only [freeExp] at hc
      simp only [xExp, Bool.and_eq_true] at hxc
      cases n with
      | zero => simp [evalExp] at hn
      | succ m =>
        obtain ⟨h₁, h₂⟩ := hop ht.1 ht.2 ha.1 ha.2 hXc.1 hXc.2 hbs.2.1 hbs.2.2 hc hxc.1 hxc.2 m
        simp only [evalExp] at hn ⊢
        cases ha₁ : evalExp m (utf8Env B) (VarEnv.empty.bindVals σ) e₁ with
        | error => rw [ha₁] at hn; cases hn
        | ok a =>
          cases hb₁ : evalExp m (utf8Env B) (VarEnv.empty.bindVals σ) e₂ with
          | error => rw [ha₁, hb₁] at hn; cases hn
          | ok b =>
            rw [ha₁, hb₁] at hn
            simp only [bind, Except.bind] at hn
            refine ⟨m + 1, ?_⟩
            simp only [evalExp, h₁, h₂, ha₁, hb₁]
            simp only [Functor.map, Except.map, bind, Except.bind]
            rcases b with _ | _ | _ | _ | _ | _ | ws | (_ | w) <;>
              simp only [memValue, Except.ok.injEq, Value.bool.injEq, reduceCtorEq] at hn
            · simp only [Swap.eraseV_list', memValue, list_contains_map hn]
            · have := beq_value_true hn
              subst this
              simp [memValue]
    | _ => simp [bindSite] at hbs

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
