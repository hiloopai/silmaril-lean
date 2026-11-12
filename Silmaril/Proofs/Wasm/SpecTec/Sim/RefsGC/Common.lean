module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Eval

/-!
# Family R: shared lemmas

Constructor tags of encoded values (for `otherwise` by opcode), `otherwise_of_ruleAt` (the
opcode criterion against a relation given by one of its rules), inversion of rule bodies, and the
reduction of a forward obligation to a `Step_pure` or `Step_read` step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-! ## Tags of encoded values -/

/-- The scope of a rule of a parameterless relation does not rebind any definition name. -/
theorem findDef_bindVals_of_bindParams {ρ₀ : VarEnv} {σ : List (IL.Id × Value)} {x : IL.Id}
    (h : bindParams VarEnv.empty [] [] = some ρ₀) : (ρ₀.bindVals σ).findDef? x = none := by
  simp only [bindParams, Option.some.injEq] at h
  subst h
  rfl

/-- No top-level injection in the empty list. -/
theorem tagsIn_nil {S : List MixopS} : TagsIn S [] := by
  intro x hx
  cases hx

/-- `TagsIn`, element by element. -/
theorem tagsIn_cons {S : List MixopS} {x : Value} {l : List Value}
    (h : ∀ op w, x = .case op w → op ∈ S) (t : TagsIn S l) : TagsIn S (x :: l) := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact h
  · exact t y hy

/-- A literal injection with a constructor in `S`. -/
theorem tag_case {S : List MixopS} {op : MixopS} {w : Value} (h : op ∈ S) :
    ∀ op' w', Value.case op w = .case op' w' → op' ∈ S := by
  intro op' w' he
  cases he
  exact h

/-- The constructor of an encoded reference. -/
theorem tag_ref {S : List MixopS} (hS : ∀ o ∈ refTags, o ∈ S) (r : Ref) :
    ∀ op w, refToValue r = .case op w → op ∈ S := by
  intro op w he
  apply hS
  cases r <;> simp only [refToValue, Value.case.injEq] at he <;> rw [← he.1] <;> decide

/-- The constructor of an encoded value. -/
theorem tag_val {S : List MixopS} (hS : ∀ o ∈ valTags, o ∈ S) (v : Val) :
    ∀ op w, valV v = .case op w → op ∈ S := by
  intro op w he
  rcases v with ⟨t, b⟩ | b | r
  · cases t <;> simp only [valV, Value.case.injEq] at he <;> rw [← he.1] <;> exact hS _ (by decide)
  · simp only [valV, Value.case.injEq] at he
    rw [← he.1]
    exact hS _ (by decide)
  · exact tag_ref (fun o ho => hS o (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho))) r op w he

/-- `Val.toAdmin` is encoded as `valV`. -/
theorem adminToV_toAdmin (v : Val) : adminToV v.toAdmin = valV v := by
  rcases v with ⟨t, b⟩ | b | r
  · cases t <;> rfl
  · rfl
  · rfl

/-- `refTags ⊆ op :: valTags`. -/
theorem refTags_sub (extra : List MixopS) : ∀ o ∈ refTags, o ∈ extra ++ valTags := by
  intro o ho
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho))

/-- `valTags ⊆ extra ++ valTags`. -/
theorem valTags_sub (extra : List MixopS) : ∀ o ∈ valTags, o ∈ extra ++ valTags :=
  fun _ ho => List.mem_append_right _ ho

/-! ## `otherwise`, against a relation given by one of its rules -/

/-- The `j`-th rule of a relation, as `relRules` reads it, is the one a `HasRuleAt` fact names. -/
theorem relRules_of_ruleAt {env : Env} {x : IL.Id} {op : MixopS} {j : Nat} {r r' : Rule}
    (h : HasRuleAt env x op j r) (h' : (relRules env x)[j]? = some r') : r' = r := by
  obtain ⟨ps, t, rules, hrel, -, hj⟩ := h
  simp only [relRules, hrel] at h'
  rw [hj] at h'
  exact (Option.some.inj h').symm

/-- **`otherwise` by opcode**, for a relation one of whose rules is known. -/
theorem otherwise_of_ruleAt {env : Env} {x : IL.Id} {k : Nat} {r : Rule}
    (h : HasRuleAt env x "%~>%" k r) {n : Nat} {T : List (List MixopS)}
    (hT : ((relRules env x).map ruleTags).take n = T) {i : Nat} (hi : i ≤ T.length)
    {S : List MixopS} {exc : List Nat} {a b : Value} (ha : LhsIn S a)
    (hc : checkAvoid T i exc S = true)
    (hexc : ∀ j ∈ exc, j < i → ∀ r', (relRules env x)[j]? = some r' → ∀ w,
      SameLhs (.tuple [a, b]) w →
      ¬ RuleBody env (DDerives env noElse) (otherwiseAt env x [] j w) [] [] "%~>%" r' w) :
    otherwise env x [] i (.tuple [a, b]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := h
  have hrr : relRules env x = rules := by simp [relRules, hrel]
  rw [hrr] at hexc
  exact otherwiseAt_of_table hrel (tags_of_take hrel hT) hi ha hc hexc

/-- `SameLhs` keeps the left-hand side. -/
theorem sameLhs_inv {a b w : Value} (h : SameLhs (.tuple [a, b]) w) : ∃ c, w = .tuple [a, c] := by
  obtain ⟨a', b', c, h₁, rfl⟩ := h
  simp only [Value.tuple.injEq, List.cons.injEq] at h₁
  exact ⟨c, by rw [h₁.1]⟩

/-! ## Inverting a rule body -/

/-- The scope of a parameterless rule instance binds term variables only. -/
theorem valsOnly_scope {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
    (h : bindParams VarEnv.empty [] [] = some ρ₀) : ValsOnly (ρ₀.bindVals σ) := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- The left-hand side of a conclusion `lhs ~> rhs`. -/
theorem lhs_of_concl {env : Env} {ρ : VarEnv} {l rh : Exp} {a c : Value}
    (h : EvalExp env ρ (.tupE [l, rh]) (.tuple [a, c])) : EvalExp env ρ l a := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u, us, hu, -, rfl⟩ := evalExps_cons_iff.1 hvs
  simp only [Value.tuple.injEq, List.cons.injEq] at hv
  rw [hv.1]
  exact hu

/-- The right-hand side of a conclusion `lhs ~> rhs`. -/
theorem rhs_of_concl {env : Env} {ρ : VarEnv} {l rh : Exp} {a c : Value}
    (h : EvalExp env ρ (.tupE [l, rh]) (.tuple [a, c])) : EvalExp env ρ rh c := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u, us, -, hus, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨u', us', hu', -, rfl⟩ := evalExps_cons_iff.1 hus
  simp only [Value.tuple.injEq, List.cons.injEq] at hv
  rw [hv.2.1]
  exact hu'

/-- The components of a list. -/
theorem elems_of_list {env : Env} {ρ : VarEnv} {es : List Exp} {vs : List Value}
    (h : EvalExp env ρ (.listE es) (.list vs)) : EvalExps env ρ es vs := by
  obtain ⟨ws, hws, hv⟩ := evalExp_listE_iff.1 h
  cases hv
  exact hws

/-- The components of a tuple. -/
theorem elems_of_tup {env : Env} {ρ : VarEnv} {es : List Exp} {vs : List Value}
    (h : EvalExp env ρ (.tupE es) (.tuple vs)) : EvalExps env ρ es vs := by
  obtain ⟨ws, hws, hv⟩ := evalExp_tupE_iff.1 h
  cases hv
  exact hws

/-- Head and tail of a list of expressions. -/
theorem evalExps_cons_inv {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp} {v : Value}
    {vs : List Value} (h : EvalExps env ρ (e :: es) (v :: vs)) :
    EvalExp env ρ e v ∧ EvalExps env ρ es vs := by
  obtain ⟨w, ws, hw, hws, he⟩ := evalExps_cons_iff.1 h
  simp only [List.cons.injEq] at he
  rw [he.1, he.2]
  exact ⟨hw, hws⟩

/-- An `if` premise holds. -/
theorem premW_if {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {e : Exp}
    (h : PremW env D els ρ (.ifPr e)) : EvalExp env ρ e (.bool true) := by
  cases h
  assumption

/-- A true equation between the denotations `v₁`, `v₂` of its sides: `v₁ = v₂`. -/
theorem eq_of_evalExp_eq {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.cmpE .eqOp t e₁ e₂) (.bool true)) (h₁ : EvalExp env ρ e₁ v₁)
    (h₂ : EvalExp env ρ e₂ v₂) : v₁ = v₂ := by
  have hb := EvalExp.unique h (evalExp_eq h₁ h₂)
  simp only [Value.bool.injEq] at hb
  exact of_decide_eq_true hb.symm

/-- The payload of an injection. -/
theorem case_inv {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {w : Value}
    (h : EvalExp env ρ (.caseE op e) (.case op w)) : EvalExp env ρ e w := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  cases he
  exact hu

/-- The store, frame and code of a left-hand side `(s; f); instr*`. -/
theorem cfg_inv {env : Env} {ρ : VarEnv} {xs xf : IL.Id} {code : Exp} {a b : Value}
    {l : List Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE xs, .varE xf]), code]))
      (cfgV (stV a b) l)) :
    EvalExp env ρ (.varE xs) a ∧ EvalExp env ρ (.varE xf) b ∧ EvalExp env ρ code (.list l) := by
  have h₁ := evalExps_cons_inv (elems_of_tup (case_inv h))
  have h₂ := evalExps_cons_inv (elems_of_tup (case_inv h₁.1))
  exact ⟨h₂.1, (evalExps_cons_inv h₂.2).1, (evalExps_cons_inv h₁.2).1⟩

/-- A rule premise without arguments that holds. -/
theorem premW_rule {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {x : IL.Id} {op : MixopS}
    {e : Exp} (h : PremW env D els ρ (.rulePr x [] op e)) : ∃ w, EvalExp env ρ e w ∧ D x op [] w := by
  cases h with
  | rulePr ha he hd =>
      obtain rfl := evalArgs_nil_iff.1 ha
      exact ⟨_, he, hd⟩

/-- The `k`-th component of an evaluated list of expressions. -/
theorem evalExps_get {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs → ∀ (k : Nat) {e : Exp} {v : Value},
      es[k]? = some e → vs[k]? = some v → EvalExp env ρ e v
  | [], _, _, _, _, _, he, _ => by simp at he
  | e' :: es, vs, h, k, e, v, he, hv => by
      obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he hv
          subst he hv
          exact hw
      | succ k =>
          simp only [List.getElem?_cons_succ] at he hv
          exact evalExps_get hws k he hv

/-- The state and code of a left-hand side `z; instr*`. -/
theorem cfgz_inv {env : Env} {ρ : VarEnv} {code : Exp} {z : Value} {l : List Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", code])) (cfgV z l)) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ code (.list l) := by
  have h₁ := evalExps_cons_inv (elems_of_tup (case_inv h))
  exact ⟨h₁.1, (evalExps_cons_inv h₁.2).1⟩

/-- `CONST I32 x`, inverted. -/
theorem const_var {env : Env} {ρ : VarEnv} {x : IL.Id} {t v : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE x]))
      (.case "CONST" (.tuple [t, v]))) : EvalExp env ρ (.varE x) v :=
  (evalExps_cons_inv (evalExps_cons_inv (elems_of_tup (case_inv h))).2).1

/-- `CONST I32 (% x)`, inverted. -/
theorem const_pct_var {env : Env} {ρ : VarEnv} {x : IL.Id} {t v : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
      .caseE "%" (.tupE [.varE x])])) (.case "CONST" (.tuple [t, .case "%" (.tuple [v])]))) :
    EvalExp env ρ (.varE x) v :=
  have hp := (evalExps_cons_inv (evalExps_cons_inv (elems_of_tup (case_inv h))).2).1
  (evalExps_cons_inv (elems_of_tup (case_inv hp))).1

/-! ## From `Step_pure` and `Step_read` to a forward obligation -/

variable {H : Type}

/-- A forward obligation discharged by a `Step_pure` step of the images. -/
theorem fwd_of_spure {env : Env} {hn : H → String} (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule) {s : Store H} {f : Frame}
    {is is' : List Admin}
    (hp : TypedV env instrsT (.list (adminsToV is)) → SPure env (adminsToV is) (adminsToV is')) :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨-, hcode'⟩ := (T.config _).1 hc'
  exact sstep_pure hr hst hcode hcode' (hp hcode)

/-- A forward obligation discharged by a `Step_read` step of the images. -/
theorem fwd_of_sread {env : Env} {hn : H → String} (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 1 Equiv.ExecStepRules.readRule) {s : Store H} {f : Frame}
    {is is' : List Admin}
    (hp : TypedV env stateT (stateV hn s f) → TypedV env instrsT (.list (adminsToV is)) →
      SRead env (configV hn ⟨s, f, is⟩) (adminsToV is')) :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨-, hcode'⟩ := (T.config _).1 hc'
  exact sstep_read hr hst hcode hcode' (hp hst hcode)

/-- The first instruction of a typed sequence is typed. -/
theorem typed_head {env : Env} {hn : H → String} (T : TypingFacts env hn) {x : Value}
    {l : List Value} (h : TypedV env instrsT (.list (x :: l))) : TypedV env instrsT (.list [x]) :=
  ((T.append [x] l).1 h).1

/-- The rest of a typed sequence is typed. -/
theorem typed_tail {env : Env} {hn : H → String} (T : TypingFacts env hn) {x : Value}
    {l : List Value} (h : TypedV env instrsT (.list (x :: l))) : TypedV env instrsT (.list l) :=
  ((T.append [x] l).1 h).2

end Silmaril.Wasm.SpecTec.Sim.RefsGC
